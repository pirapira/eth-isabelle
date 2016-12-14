let () =
  let open Yojson.Basic in
  let vmArithmeticTest : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vmArithmeticTestAssoc : (string * json) list = Util.to_assoc vmArithmeticTest in
  let () =
    List.iter (fun (label, elm) -> Printf.printf "%s\n" label) vmArithmeticTestAssoc
  in
  ()
