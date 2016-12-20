open Yojson.Basic
open Jsonparser

(* for now executes the first vmTest found in a particular file *)

let () =
  let () = Printf.printf "hello\n" in
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let (label, j) = List.nth vm_arithmetic_test_assoc 0 in
  let () = Printf.printf "test case: %s\n" label in
  let case : test_case = parse_test_case j in
  ()
