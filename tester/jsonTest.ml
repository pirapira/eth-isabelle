open Yojson.Basic

type test_case =
  { callcreates : json
  ; env : json
  ; exec : json
  ; gas : json
  ; logs : json
  ; out : json
  ; post : json
  ; pre : json
  }

let parse_test_case (j : json) : test_case =
  Util.(
  { callcreates = member "callcreates" j
  ; env = member "env" j
  ; exec = member "exec" j
  ; gas = member "gas" j
  ; logs = member "logs" j
  ; out = member "out" j
  ; post = member "post" j
  ; pre = member "pre" j
  })

let () =
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let () =
    List.iter (fun (label, elm) ->
        let () = Printf.printf "%s\n" label in
        let case : test_case = parse_test_case elm in
        ()
      ) vm_arithmetic_test_assoc
  in
  ()
