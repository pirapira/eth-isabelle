open Yojson.Basic
open Stateparser
open Block
open Evm
open TestResult

let bighex x = Z.format "%x" (Z.of_string (Big_int.string_of_big_int x))

let construct_block_info (t : test_case) : block_info =
  let block_number = Conv.word256_of_big_int t.env.currentNumber in
  { block_blockhash = (fun num ->
      let num : Big_int.big_int = Conv.big_int_of_word256 num in
      if Big_int.lt_big_int num (Big_int.sub_big_int t.env.currentNumber (Big_int.big_int_of_int 256)) then
        Conv.word256_of_big_int Big_int.zero_big_int
      else if Big_int.gt_big_int num t.env.currentNumber then
        Conv.word256_of_big_int Big_int.zero_big_int
      else if Big_int.eq_big_int num t.env.currentNumber then
        Conv.word256_of_big_int Big_int.zero_big_int
      else
        let hashed_byte_list = (Conv.string_as_byte_list
                       (Big_int.string_of_big_int num)) in
        let ret = Keccak.keccak hashed_byte_list in
        ret
    )
  ; block_coinbase  = Conv.word160_of_big_int t.env.currentCoinbase
  ; block_timestamp = Conv.word256_of_big_int t.env.currentTimestamp
  ; block_number    = block_number
  ; block_difficulty = Conv.word256_of_big_int t.env.currentDifficulty
  ; block_gaslimit = Conv.word256_of_big_int t.env.currentGasLimit
  ; block_gasprice = Conv.word256_of_big_int t.tr.gasPrice
  }

let string_to_w256 str = Conv.word256_of_big_int (Big_int.big_int_of_string str)

let zero = string_to_w256 "0"

let convert_storage lst =
  let conv = List.map (fun (p,v) -> (Conv.word256_of_big_int p, string_to_w256 v)) lst in
  (fun x -> try List.assoc x conv with _ -> zero)

let convert_state addr st = {
  account_storage0 = convert_storage st.VmTestParser.storage;
  account_address0 = addr;
  account_exists = true;
  account_balance0 = Conv.word256_of_big_int st.VmTestParser.balance;
  account_nonce = Conv.word256_of_big_int st.VmTestParser.nonce;
  account_code0 = fst (Hexparser.parse_code st.VmTestParser.code);
  account_hascode = false;
}

let make_state_list lst =
  List.map (fun (a,st) ->
     let addr = Conv.word160_of_big_int (Big_int.big_int_of_string ("0x"^a)) in
     let stor_lst = List.map (fun (p,v) -> (Conv.word256_of_big_int p, string_to_w256 v)) st.VmTestParser.storage in
     (addr, convert_state addr st, stor_lst)) lst

let construct_tr a = {
  tr_from = Conv.word160_of_big_int a.address;
  tr_to = (match a.target with None -> None | Some x -> Some (Conv.word160_of_big_int x));
  tr_gas_limit = Conv.word256_of_big_int a.gasLimit;
  tr_gas_price = Conv.word256_of_big_int a.gasPrice;
  tr_value = Conv.word256_of_big_int a.value;
  tr_nonce = Conv.word256_of_big_int a.nonce;
  tr_data = Conv.byte_list_of_hex_string a.data;
}

let w256hex i = Z.format "%x" (Word256.word256ToNatural i)
let w256dec i = Z.format "%d" (Word256.word256ToNatural i)

let debug_vm c1 pr =
 match pr with
  | InstructionContinue v ->
     prerr_endline ("Gas " ^ Z.to_string v.vctx_gas);
     (match vctx_next_instruction v c1 with
      | None -> ()
      | Some i ->
        (* prerr_endline ("Watch " ^ w256hex (v.vctx_storage (Word256.word256FromNat 1))); *)
        (* prerr_endline ("Calldata " ^ String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) v.vctx_data_sent)); *)
        prerr_endline ("Inst " ^ String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) (inst_code i)));
        prerr_endline ("Stack " ^ String.concat "," (List.map (fun x -> Z.format "%d" (Word256.word256ToNatural x)) v.vctx_stack)) )
  | InstructionToEnvironment( _, v, _) -> prerr_endline ("Gas left " ^ Z.to_string v.vctx_gas)

let debug_state = function
 | Continue res -> debug_vm res.g_cctx res.g_vmstate
 | _ -> ()

let debug_mode = if Array.length Sys.argv > 2 then true else false

exception Skip

let run_tr tr state block net =
  let res = start_transaction tr state block in
  let rec do_run = function
   | Finished fi -> fi
   | Unimplemented -> raise Skip
   | a ->
     if debug_mode then debug_state a;
     do_run (next net a) in
  let fi = do_run res in
  if debug_mode then begin
    prerr_endline ("Bal " ^ w256dec (fi.f_state tr.tr_from).account_balance0);
    prerr_endline ("Killed " ^ string_of_int (List.length fi.f_killed));
  end;
  let final_state = end_transaction fi tr block in
  final_state

let compare_storage diff_found a stor (p,v) =
  if stor p <> v then begin
      Printf.printf "address %s has storage %s at %s, but it should be %s!\n" (Conv.string_of_address a)
       (Conv.decimal_of_word256 (stor p)) (Conv.decimal_of_word256 p) (Conv.decimal_of_word256 v);
      diff_found := true
  end

let run_test (label, elm) : testResult =
  let () = Printf.printf "%s\n%!" label in
  let tc = parse_test_case elm in
  let block_info = construct_block_info tc in
  let tr = construct_tr tc.tr in
  let pre_st = List.map (fun (a,b,_) -> (a,b)) (make_state_list tc.pre) in
  let post_st = make_state_list tc.post in
  let state x = try List.assoc x pre_st with _ -> empty_account0 x in
  let net = Evm.network_of_block_number (Word256.word256ToNatural (block_info.block_number)) in
  try
    let state = run_tr tr state block_info net in
    let diff_found = ref false in
    List.iter (fun (a,cmp, storage_list) ->
      let acc = state a in
      if acc.account_balance0 <> cmp.account_balance0 then begin
        Printf.printf "address %s has balance %s, but it should be %s!\n%!" (Conv.string_of_address a) (Conv.decimal_of_word256 acc.account_balance0)
         (Conv.decimal_of_word256 cmp.account_balance0);
        diff_found := true
      end;
      if acc.account_nonce <> cmp.account_nonce then begin
        Printf.printf "address %s has nonce %s, but it should be %s!\n%!" (Conv.string_of_address a) (Conv.decimal_of_word256 acc.account_nonce)
         (Conv.decimal_of_word256 cmp.account_nonce);
         diff_found := true
      end;
      List.iter (compare_storage diff_found a acc.account_storage0) storage_list) post_st;
    (if !diff_found then TestFailure else TestSuccess)
  with
    Skip -> TestSkipped
