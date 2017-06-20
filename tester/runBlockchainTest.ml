open Yojson.Basic

exception SkipTest

let test_one_case (path : string) (case_name, test) =
  let strip_singleton_list lst =
    if List.length lst <> 1 then raise SkipTest else List.nth lst 0 in
  try
    let block = strip_singleton_list test.BlockchainTestParser.bcCaseBlocks in
    let tr = strip_singleton_list block.BlockchainTestParser.blockTransactions in
  (* check if the transaction is one *)
  (* tr *)
  (* get pre state *)
  (* get post state *)
  (* create a dummy state *)
  (* decide net *)
    ()
  with SkipTest ->
    Printf.printf "...... skipping %s\n" case_name

let test_one_file path =
  let () = Printf.printf "file: %s\n" path in
  let j = Yojson.Basic.from_file path in
  let () = Printf.printf ".... JSON parsed!\n" in
  try
    let testCases = BlockchainTestParser.parse_test_file j in
    let () = Printf.printf ".... test parsed!\n" in
    let () = List.iter (test_one_case path) testCases in
    ()
  with BlockchainTestParser.UnsupportedEncoding ->
    let () = Printf.printf ".... has an unsupported encoding.\n" in
    ()

let _ =
  let () = Printf.printf "runBlockchainTest is not running any test yet. \n%!" in
  let () = TraverseJsons.traverse "../tests/BlockchainTests" test_one_file in
  ()
