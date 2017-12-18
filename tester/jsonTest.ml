open Yojson.Basic
open BlockchainTestParser

let () =
(*  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let () =
    List.iter (fun (label, elm) ->
        let () = Printf.printf "%s\n" label in
        let case : test_case = parse_test_case elm in
        ()
      ) vm_arithmetic_test_assoc in *)
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmIOandFlowOperationsTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let () =
    List.iter (fun (label, elm) ->
        let () = Printf.printf "%s\n%!" label in
        let _ : VmTestParser.test_case = VmTestParser.parse_test_case elm in
        ()
      ) vm_arithmetic_test_assoc
  in
  let addr_big = Big_int.big_int_of_string "0x000000000000000000000000000000000000000f" in
  let addr_w = Conv.word160_of_big_int addr_big in
  let () = assert (addr_w = Word160.W160 (false, [true; true; true; true]) ) in (* passes *)
  let () = assert (Big_int.eq_big_int addr_big (Conv.big_int_of_word160 addr_w)) in
  let () = Printf.printf "address_printed %s\n" (BatBig_int.to_string_in_hexa (Conv.big_int_of_word160 addr_w)) in
  let addr_s = Conv.string_of_address addr_w in
  let () = assert (addr_s = "000000000000000000000000000000000000000f") in

  let blockHeaderSample : json = Yojson.Basic.from_file "./sample_json/block_header_sample.json" in
  let blockHeader = parse_block_header blockHeaderSample in
  let () = Printf.printf "something parsed from block_header_sample.json\n" in
  let () = Easy_format.Pretty.to_stdout (format_block_header blockHeader) in

  let transactionSample : json = Yojson.Basic.from_file "./sample_json/block_transaction_sample.json" in
  let tr = BlockchainTestParser.parse_transaction transactionSample in
  let () = Printf.printf "something parsed from block_transaction_sample.json\n" in
  let () = Easy_format.Pretty.to_stdout (format_transaction tr) in

  let blockSample : json = Yojson.Basic.from_file "./sample_json/block_sample.json" in
  let b = BlockchainTestParser.parse_block blockSample in
  let () = Printf.printf "something parsed from block_sample.json\n" in
  let () = Easy_format.Pretty.to_stdout (format_block b) in

  ()
