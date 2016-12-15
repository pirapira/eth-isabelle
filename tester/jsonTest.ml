open Yojson.Basic

type env =
  { currentCoinbase : string
  ; currentDifficulty : string
  ; currentGasLimit : string
  ; currentNumber : string
  ; currentTimestamp : string
  }

let parse_env (j : json) : env =
  Util.(
    { currentCoinbase = to_string (member "currentCoinbase" j)
    ; currentDifficulty = to_string (member "currentDifficulty" j)
    ; currentGasLimit = to_string (member "currentGasLimit" j)
    ; currentNumber = to_string (member "currentNumber" j)
    ; currentTimestamp = to_string (member "currentTimestamp" j)
    })

type test_case =
  { callcreates : json list
  ; env : env
  ; exec : json
  ; gas : json
  ; logs : json
  ; out : json
  ; post : json
  ; pre : json
  }

let parse_test_case (j : json) : test_case =
  Util.(
  { callcreates = to_list (member "callcreates" j)
  ; env = parse_env (member "env" j)
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
