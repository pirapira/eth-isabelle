open Yojson.Basic
open Hexparser
open Evm

type env =
  { currentCoinbase : Big_int.big_int
  ; currentDifficulty : Big_int.big_int
  ; currentGasLimit : Big_int.big_int
  ; currentNumber : Big_int.big_int
  ; currentTimestamp : Big_int.big_int
  }

let to_big_int j = Big_int.big_int_of_string (to_string j)


let parse_big_int_from_field field j =
  let str = to_string (Util.member field j) in
  let str = BatString.(of_list
                         (List.filter
                            (fun c -> c <> '"')
                         (to_list str))) in
    try
      Big_int.big_int_of_string str
    with e ->
      begin
        let () = Printf.eprintf "parse error %s: %s %d%!\n" field str (String.length str) in
        raise e
      end

let parse_address_from_field field j =
  let str = to_string (Util.member field j) in
  let str = BatString.(of_list
                         (List.filter
                            (fun c -> c <> '"')
                         (to_list str))) in
  let str = "0x" ^ str in
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
        parse_address_from_field "currentCoinbase" j
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
    [ Label ((Atom ("currentCoinbase", atom), label), Atom (Big_int.string_of_big_int e.currentCoinbase, atom))
    ; Label ((Atom ("currentDifficulty", atom), label), Atom (Big_int.string_of_big_int e.currentDifficulty, atom))
    ] in
  List (("{", ",", "}", list), lst)

type exec =
  { address : Big_int.big_int
  ; caller : Big_int.big_int
  ; code : Evm.program
  ; data : string
  ; gas : Big_int.big_int
  ; gasPrice : Big_int.big_int
  ; origin : Big_int.big_int
  ; value : Big_int.big_int
  }

let parse_exec (j : json) : exec =
  Util.(
    { address = parse_address_from_field "address" j
    ; caller = parse_address_from_field "caller" j
    ; code =
        begin
          let (parsed, rest) = parse_code(to_string (member "code" j)) in
          if rest = "" then parsed else failwith "code parsing left some garbage data"
        end
    ; data = to_string (member "data" j)
    ; gas = parse_big_int_from_field "gas" j
    ; gasPrice = parse_big_int_from_field "gasPrice" j
    ; origin = parse_address_from_field  "origin" j
    ; value = parse_big_int_from_field "value" j
    })

type list_storage = (string * string) list

let parse_storage (j : json) : list_storage =
  Util.(
    List.map (fun (label, content) -> (label, to_string content)) (to_assoc j)
  )

type account_state =
  { balance : Big_int.big_int
  ; code : string
  ; nonce : Big_int.big_int
  ; storage : list_storage
  }

let parse_account_state (j : json) : account_state =
  Util.(
  { balance = parse_big_int_from_field "balance" j
  ; code = to_string (member "code" j)
  ; nonce = parse_big_int_from_field "nonce" j
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

let lookup_storage (addr : address) (pre_state : (string * account_state) list) : storage =
  failwith "lookup_storage"

let construct_global_balance (pre_state : (string * account_state) list) : address -> w256 =
  failwith "construct_global_balance"

let construct_ext_program (pre_state : (string * account_state) list) : address -> program =
  failwith "construct_ext_program"

let construct_block_info (t : test_case) : block_info =
  failwith "construct_block_info"

let construct_account_existence (pre_state : (string * account_state) list) : address -> bool =
  failwith "construct_account_existence"

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
