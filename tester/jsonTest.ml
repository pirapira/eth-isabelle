open Yojson.Basic

type env =
  { currentCoinbase : string
  ; currentDifficulty : Big_int.big_int
  ; currentGasLimit : Big_int.big_int
  ; currentNumber : Big_int.big_int
  ; currentTimestamp : Big_int.big_int
  }

let to_big_int j = Big_int.big_int_of_string (to_string j)


let parse_big_int_from_field field j =
  let str = (to_string (Util.member field j)) in
    try
      Big_int.big_int_of_string str
    with e ->
      begin
        let () = Printf.eprintf "parse error %s: %s %d%!\n" field str (String.length str) in
        raise e
      end

let parse_env (j : json) : env =
  let () = Printf.eprintf "parse_env\n%!" in
  Util.(
    { currentCoinbase =
        to_string (member "currentCoinbase" j)
    ; currentDifficulty =
        parse_big_int_from_field "currentDifficulty" j
    ; currentGasLimit =
        parse_big_int_from_field "currentGasLimit" j
    ; currentNumber =
        parse_big_int_from_field "currentNumber" j
    ; currentTimestamp =
        parse_big_int_from_field "currentTimestamp" j
    })


let format_env (e : env) : Easy_format.t =
  let open Easy_format in
  let lst : Easy_format.t list =
    [ Label ((Atom ("currentCoinbase", atom), label), Atom (e.currentCoinbase, atom))
    ; Label ((Atom ("currentDifficulty", atom), label), Atom (Big_int.string_of_big_int e.currentDifficulty, atom))
    ] in
  List (("{", ",", "}", list), lst)

type exec =
  { address : string
  ; caller : string
  ; code : string
  ; data : string
  ; gas : string
  ; gasPrice : string
  ; origin : string
  ; value : string
  }

let parse_exec (j : json) : exec =
  Util.(
    { address = to_string (member "address" j)
    ; caller = to_string (member "caller" j)
    ; code = to_string (member "code" j)
    ; data = to_string (member "data" j)
    ; gas = to_string (member "gas" j)
    ; gasPrice = to_string (member "gasPrice" j)
    ; origin = to_string (member "origin" j)
    ; value = to_string (member "value" j)
    })

type storage = (string * string) list

let parse_storage (j : json) : storage =
  Util.(
    List.map (fun (label, content) -> (label, to_string content)) (to_assoc j)
  )

type account_state =
  { balance : string
  ; code : string
  ; nonce : string
  ; storage : storage
  }

let parse_account_state (j : json) : account_state =
  Util.(
  { balance = to_string (member "balance" j)
  ; code = to_string (member "code" j)
  ; nonce = to_string (member "nonce" j)
  ; storage = parse_storage (member "storage" j)
  })

let parse_states (asc : (string * json) list) : (string * account_state) list =
  List.map (fun (label, j) -> (label, parse_account_state j)) asc

type test_case =
  { callcreates : json list
  ; env : env
  ; exec : exec
  ; gas : string option
  ; logs : json list option
  ; out : string option
  ; post : (string * account_state) list option
  ; pre : (string * account_state) list
  }

let parse_test_case (j : json) : test_case =
  let () = Easy_format.Pretty.to_stdout (format_env (parse_env (Util.member "env" j))) in
  Util.(
  { callcreates =
      (try
        to_list (member "callcreates" j)
       with Yojson.Basic.Util.Type_error _ ->
        []
      )
  ; env = parse_env (member "env" j)
  ; exec = parse_exec (member "exec" j)
  ; gas =
      (try Some (to_string (member "gas" j))
       with Yojson.Basic.Util.Type_error _ -> None)
  ; logs =
      (try Some (to_list (member "logs" j))
       with Yojson.Basic.Util.Type_error _ -> None)
  ; out =
      (try Some (to_string (member "out" j))
       with Yojson.Basic.Util.Type_error _ -> None)
  ; post =
      (try
         Some (parse_states (to_assoc (member "post" j)))
       with Yojson.Basic.Util.Type_error _ ->
         None
      )
  ; pre = parse_states (to_assoc (member "pre" j))
  })

let () =
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
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
  in
  ()
