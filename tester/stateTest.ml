
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
  List.map (fun (a,st) -> let addr = Conv.word160_of_big_int (Big_int.big_int_of_string ("0x"^a)) in (addr, convert_state addr st)) lst

let construct_tr a = {
  tr_from = Conv.word160_of_big_int a.address;
  tr_to = (match a.target with None -> None | Some x -> Some (Conv.word160_of_big_int x));
  tr_gas_limit = Conv.word256_of_big_int a.gasLimit;
  tr_gas_price = Conv.word256_of_big_int a.gasPrice;
  tr_value = Conv.word256_of_big_int a.value;
  tr_nonce = Conv.word256_of_big_int a.nonce;
  tr_data = Conv.byte_list_of_hex_string a.data;
}

let () =
  let test : json = Yojson.Basic.from_file "../tests/StateTests/stExample.json" in
  let test_assoc : (string * json) list = Util.to_assoc test in
  let () =
    List.iter (fun (label, elm) ->
        let () = Printf.printf "%s\n%!" label in
        let tc = parse_test_case elm in
        Printf.printf "address: %s\n" (bighex tc.tr.address);
        let block_info = construct_block_info tc in
        let tr = construct_tr tc.tr in
        let pre_st = make_state_list tc.pre in
        let post_st = make_state_list tc.post in
        Printf.printf "state has %d accounts\n" (List.length pre_st);
        let state x = try List.assoc x pre_st with _ -> empty_account0 x in
        ()
      ) test_assoc
  in
  ()


