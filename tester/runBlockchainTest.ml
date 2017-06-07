open Yojson.Basic

let test_one_file path =
  let () = Printf.printf "file: %s\n" path in
  let () = ignore (Yojson.Basic.from_file path) in
  let () = Printf.printf ".... JSON parsed!\n" in
  ()

let _ =
  let () = Printf.printf "runBlockchainTest is not running any test yet. \n%!" in
  let () = TraverseJsons.traverse "../tests/BlockchainTests" test_one_file in
  ()
