
open Yojson.Basic
open Stateparser
open Block
open Evm
open Extlib.ExtList

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
  account_storage0 = convert_storage st.Jsonparser.storage;
  account_address0 = addr;
  account_exists = true;
  account_balance0 = Conv.word256_of_big_int st.Jsonparser.balance;
  account_nonce = Conv.word256_of_big_int st.Jsonparser.nonce;
  account_code0 = fst (Hexparser.parse_code st.Jsonparser.code);
  account_hascode = false;
}

let make_state_list lst =
  List.map (fun (a,st) ->
     let addr = Conv.word160_of_big_int (Big_int.big_int_of_string ("0x"^a)) in
     let stor_lst = List.map (fun (p,v) -> (Conv.word256_of_big_int p, string_to_w256 v)) st.Jsonparser.storage in
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
     Printf.printf "Gas %s\n"  (Z.to_string v.vctx_gas);
     (match vctx_next_instruction v c1 with
      | None -> ()
      | Some i ->
        (* prerr_endline ("Watch " ^ w256hex (v.vctx_storage (Word256.word256FromNat 1))); *)
        (* prerr_endline ("Calldata " ^ String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) v.vctx_data_sent)); *)
        Printf.printf "Inst %s Stack %s\n" (String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) (inst_code i)))
                                    (String.concat "," (List.map (fun x -> Z.format "%x" (Word256.word256ToNatural x)) v.vctx_stack)) )
  | InstructionToEnvironment( _, v, _) -> prerr_endline ("Gas left " ^ Z.to_string v.vctx_gas)
  | InstructionAnnotationFailure -> ()

let debug_state = function
 | Continue res -> debug_vm res.g_cctx res.g_vmstate
 | _ -> ()

let debug_mode = if Array.length Sys.argv > 2 then true else false

let run_tr tr state block =
  let res = start_transaction tr state block in
  let rec do_run = function
   | Finished fi -> fi
   | a ->
     if debug_mode then debug_state a;
     do_run (next a) in
  let fi = do_run res in
  if debug_mode then begin
    prerr_endline ("Bal " ^ w256dec (fi.f_state tr.tr_from).account_balance0);
    prerr_endline ("Killed " ^ string_of_int (List.length fi.f_killed));
  end;
  let final_state = end_transaction fi tr block in
  final_state, List.rev fi.f_logs

let compare_storage a stor (p,v) =
  if stor p <> v then begin
      Printf.printf "address %s has storage %s at %s, but it should be %s!\n" (Conv.string_of_address a) 
       (Conv.decimal_of_word256 (stor p)) (Conv.decimal_of_word256 p) (Conv.decimal_of_word256 v)
  end

let compare_topics (actual : Keccak.w256) (spec : Big_int.big_int) =
  if not (Big_int.eq_big_int spec (Conv.big_int_of_word256 actual)) then
    Printf.printf "Bad log topic %s, should have been %s!\n" (w256hex actual) (w256hex (Conv.word256_of_big_int spec))

let compare_log_entry (actual : Evm.log_entry) (spec : Jsonparser.log) =
  if not (Big_int.eq_big_int (Conv.big_int_of_word160 actual.Evm.log_addr) spec.logAddress) then Printf.printf "Wrong log address\n";
  if List.length actual.Evm.log_topics <> List.length spec.topics then Printf.printf "Log topic list length mismatch!\n";
  BatList.iter2 compare_topics actual.Evm.log_topics spec.topics;
  if spec.logData <> Conv.hex_string_of_byte_list "0x" actual.Evm.log_data then
    Printf.printf "Bad log data: was %s and should be %s!\n" (Conv.hex_string_of_byte_list "0x" actual.Evm.log_data) spec.logData

let run_test (label, elm) =
  let () = Printf.printf "%s\n%!" label in
  let tc = parse_test_case elm in
  let block_info = construct_block_info tc in
  let tr = construct_tr tc.tr in
  let pre_st = List.map (fun (a,b,_) -> (a,b)) (make_state_list tc.pre) in
  let post_st = make_state_list tc.post in
  let state x = try List.assoc x pre_st with _ -> empty_account0 x in
  let state, logs = run_tr tr state block_info in
  let _ = if List.length logs <> List.length tc.logs then Printf.printf "Log length bad" in
  List.iter2 compare_log_entry logs tc.logs;
  List.iter (fun (a,cmp, storage_list) ->
    let acc = state a in
    if acc.account_balance0 <> cmp.account_balance0 then begin
      Printf.printf "address %s has balance %s, but it should be %s!\n%!" (Conv.string_of_address a) (Conv.decimal_of_word256 acc.account_balance0)
       (Conv.decimal_of_word256 cmp.account_balance0)
    end;
    if acc.account_nonce <> cmp.account_nonce then begin
      Printf.printf "address %s has nonce %s, but it should be %s!\n%!" (Conv.string_of_address a) (Conv.decimal_of_word256 acc.account_nonce)
       (Conv.decimal_of_word256 cmp.account_nonce)
    end;
    List.iter (compare_storage a acc.account_storage0) storage_list) post_st;
  ()

let main fn filter =
  let test : json = Yojson.Basic.from_file fn in
  let test_assoc : (string * json) list = Util.to_assoc test in
  let check a = match filter with None -> true | Some b -> a = b in
  let () =
    List.iter (fun (a,b) -> if check a then run_test (a,b)) test_assoc
  in
  ()

let _ =
  if Array.length Sys.argv = 2 then main Sys.argv.(1) None else
  if Array.length Sys.argv > 2 then main Sys.argv.(1) (Some Sys.argv.(2))
  (*
  for i = 1 to Array.length Sys.argv - 1 do
    main Sys.argv.(i)
  done*)


