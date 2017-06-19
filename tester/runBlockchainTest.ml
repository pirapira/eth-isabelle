open Yojson.Basic

let test_one_file path =
  let () = Printf.printf "file: %s\n" path in
  let j = Yojson.Basic.from_file path in
  let () = Printf.printf ".... JSON parsed!\n" in
  try
    let () = ignore (BlockchainTestParser.parse_test_file j) in
    let () = Printf.printf ".... test parsed!\n" in
    ()
  with BlockchainTestParser.UnsupportedEncoding ->
    let () = Printf.printf ".... has an unsupported encoding.\n" in
    ()

let _ =
  let () = Printf.printf "runBlockchainTest is not running any test yet. \n%!" in
  let () = TraverseJsons.traverse "../tests/BlockchainTests" test_one_file in
  ()
