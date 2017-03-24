
open Yojson.Basic
open Stateparser
open Block
open Evm

let bighex x = Z.format "%x" (Z.of_string (Big_int.string_of_big_int x))

let construct_block_info (t : test_case) : block_info =
  let block_number = Conv.word256_of_big_int t.env.currentNumber in
  { block_blockhash = (fun num ->
      let num : Big_int.big_int = Conv.big_int_of_word256 num in
      if Big_int.eq_big_int Big_int.zero_big_int num then
        Conv.word256_of_big_int Big_int.zero_big_int
      else if Big_int.lt_big_int num (Big_int.sub_big_int t.env.currentNumber (Big_int.big_int_of_int 256)) then
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

(*
let debug_state = function
 | Continue res ->
   (match res.g_vmstate with
   | InstructionContinue v ->
   | _ -> () )
 | _ -> ()
*)

let run_tr tr state block =
  let res = start_transaction tr state block in
  let rec do_run = function
   | Finished fi -> fi
   | a ->
     do_run (next a) in
  let fi = do_run res in
  let final_state = end_transaction fi tr block in
  final_state

let compare_storage a stor (p,v) =
  if stor p <> v then begin
      Printf.printf "address %s has storage %s at %s, but it should be %s!\n" (Conv.string_of_address a) 
       (Conv.decimal_of_word256 (stor p)) (Conv.decimal_of_word256 p) (Conv.decimal_of_word256 v)
  end

let run_test (label, elm) =
  let () = Printf.printf "%s\n%!" label in
  let tc = parse_test_case elm in
  let block_info = construct_block_info tc in
  let tr = construct_tr tc.tr in
  let pre_st = List.map (fun (a,b,_) -> (a,b)) (make_state_list tc.pre) in
  let post_st = make_state_list tc.post in
  let state x = try List.assoc x pre_st with _ -> empty_account0 x in
  let state = run_tr tr state block_info in
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


