open Yojson.Basic
open Hexparser
open Keccak
open Evm

type env =
  { currentCoinbase : Big_int.big_int
  ; currentDifficulty : Big_int.big_int
  ; currentGasLimit : Big_int.big_int
  ; currentNumber : Big_int.big_int
  ; currentTimestamp : Big_int.big_int
  ; previousHash : Big_int.big_int option
  }

let to_big_int j = Big_int.big_int_of_string (to_string j)


let parse_big_int_from_string str =
  let str = BatString.(of_list
                         (List.filter
                            (fun c -> c <> '"')
                         (to_list str))) in
    try
      Big_int.big_int_of_string str
    with e ->
      begin
        raise e
      end

let parse_big_int_from_field field j =
  let str = to_string (Util.member field j) in
  parse_big_int_from_string str

let parse_address_from_field field j =
  let str = to_string (Util.member field j) in
  let str = BatString.(of_list
                         (List.filter
                            (fun c -> c <> '"')
                         (to_list str))) in
  let str = if String.length str > 1 && str.[0] = '0' && str.[1] = 'x' then str else "0x" ^ str in
    try
      Big_int.big_int_of_string str
    with e ->
      begin
        raise e
      end

let parse_env (j : json) : env =
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
    ; previousHash =
        try
          Some (parse_address_from_field "previousHash" j)
        with Failure _ -> None
    })


let format_env (e : env) : Easy_format.t =
  let open Easy_format in
  let lst : t list =
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
          let code = to_string (member "code" j) in
          let () = Printf.printf "code: %s\n%!" code in
          let (parsed, rest) = parse_code code in
          if rest = "" then parsed else failwith ("code parsing left some garbage data: "^rest)
        end
    ; data = to_string (member "data" j)
    ; gas = parse_big_int_from_field "gas" j
    ; gasPrice = parse_big_int_from_field "gasPrice" j
    ; origin = parse_address_from_field  "origin" j
    ; value = parse_big_int_from_field "value" j
    })

type list_storage = (Big_int.big_int * string) list

let parse_storage (j : json) : list_storage =
  Util.(
    List.map (fun ((label : string), content) ->
        ((if label = "0x" then Big_int.zero_big_int else Big_int.big_int_of_string label),
         to_string content)) (to_assoc j))

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

type log =
  { logAddress : Big_int.big_int
  ; logData : string
  ; topics : Big_int.big_int list
  }

let parse_log (j : json) : log =
  Util.(
  { logAddress = parse_address_from_field "address" j
  ; logData = to_string (member "data" j)
  ; topics = List.map (fun j -> parse_big_int_from_string ("0x" ^ to_string j)) (to_list (member "topics" j))
  }
  )

type test_case =
  { callcreates : json list
  ; env : env
  ; exec : exec
  ; gas : string option
  ; logs : log list option
  ; out : string option
  ; post : (string * account_state) list option
  ; pre : (string * account_state) list
  }

let lookup_storage (addr : address) (pre_state : (string * account_state) list) (index : w256) : w256 =
  let addr_string = Conv.string_of_address addr in
  try
    let a : account_state = List.assoc addr_string pre_state in
    let v : string = Conv.bigint_assoc (Conv.big_int_of_word256 index) a.storage in
    let b : Big_int.big_int = Big_int.big_int_of_string v in
    Conv.word256_of_big_int b
  with Not_found ->
       Conv.word256_of_big_int Big_int.zero_big_int

let construct_global_balance (pre_state : (string * account_state) list) (addr : address) : w256 =
  try
    let lookup_addr = Conv.string_of_address addr in
    let a : account_state = List.assoc lookup_addr pre_state in
    Conv.word256_of_big_int a.balance
  with
    Not_found -> Conv.word256_of_big_int Big_int.zero_big_int

let construct_ext_program (pre_state : (string * account_state) list) (addr : address) : program =
  try
    let lookup_addr = Conv.string_of_address addr in
    let a : account_state = List.assoc lookup_addr pre_state in
    let (p, rest) = parse_code a.code in
    let () = assert (rest = "") in
    p
  with
    Not_found -> empty_program

let construct_block_info (t : test_case) : block_info =
  let block_number = Conv.word256_of_big_int t.env.currentNumber in
  { block_blockhash = (fun num ->
      let num : Big_int.big_int = Conv.big_int_of_word256 num in
      if Big_int.eq_big_int Big_int.zero_big_int num then
        Conv.word256_of_big_int Big_int.zero_big_int
      else if Big_int.lt_big_int num (Big_int.sub_big_int t.env.currentNumber (Big_int.big_int_of_int 256)) then
        Conv.word256_of_big_int Big_int.zero_big_int
      else if Big_int.gt_big_int num t.env.currentNumber then
        Conv.word256_of_big_int Big_int.zero_big_int
      else if Big_int.eq_big_int num t.env.currentNumber then
        Conv.word256_of_big_int Big_int.zero_big_int
      else
        let hashed_byte_list = (Conv.string_as_byte_list
                       (Big_int.string_of_big_int num)) in
        let ret = keccak hashed_byte_list in
        ret
    )
  ; block_coinbase  = Conv.word160_of_big_int t.env.currentCoinbase
  ; block_timestamp = Conv.word256_of_big_int t.env.currentTimestamp
  ; block_number    = block_number
  ; block_difficulty = Conv.word256_of_big_int t.env.currentDifficulty
  ; block_gaslimit = Conv.word256_of_big_int t.env.currentGasLimit
  }

let construct_account_existence (pre_state : (string * account_state) list) (addr : address) : bool =
  let str = Conv.string_of_address addr in
  try
    let _ = List.assoc str pre_state in
    true
  with Not_found -> false

let parse_test_case (j : json) : test_case =
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
      (try Some (List.map parse_log (to_list (member "logs" j)))
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
