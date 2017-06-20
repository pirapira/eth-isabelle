open Yojson.Basic

let test_one_case (path : string) (case_name, test) =
  let skip () =
    Printf.printf "...... skipping %s\n" case_name in
  let () =
    (if List.length test.BlockchainTestParser.bcCaseBlocks <> 1 then skip ()) in
  let block = List.nth test.BlockchainTestParser.bcCaseBlocks 0 in
  let () =
    (if List.length block.BlockchainTestParser.blockTransactions <> 1 then skip ()) in
  let tr = List.nth block.BlockchainTestParser.blockTransactions 0 in
  (* check if the transaction is one *)
  (* tr *)
  (* get pre state *)
  (* get post state *)
  (* create a dummy state *)
  (* decide net *)
  ()

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
