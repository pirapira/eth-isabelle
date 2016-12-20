open Yojson.Basic
open Jsonparser

let () =
(*  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let () =
    List.iter (fun (label, elm) ->
        let () = Printf.printf "%s\n" label in
        let case : test_case = parse_test_case elm in
        ()
      ) vm_arithmetic_test_assoc in
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmIOandFlowOperationsTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let () =
    List.iter (fun (label, elm) ->
        let () = Printf.printf "%s\n" label in
        let case : test_case = parse_test_case elm in
        ()
      ) vm_arithmetic_test_assoc
  in *)
  let addr_big = Big_int.big_int_of_string "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6" in
  let addr_w = Conv.word160_of_big_int addr_big in
  let addr_s = Conv.string_of_address addr_w in
  let () = assert (addr_s = "0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6") in

  ()
