open Evm

let pad_left (elm : 'a) (len : int) (orig : 'a list) =
  let remaining = len - List.length orig in
  let () = Printf.printf "padding: remaining: %d\n%!" remaining in
  let padding = BatList.make remaining elm in
  padding @ orig

let word_of_big_int (target_len : int) (b : Big_int.big_int) =
  let () = if BatBig_int.(lt_big_int b zero_big_int) then failwith "negative number cannot be turned into word256" else () in
  let binary : string = BatBig_int.to_string_in_binary b in
  (* should be a sequence of 0s and 1s *)
  let bl : bool list =
    List.map (fun (digit : char) ->
        match digit with
        | '0' -> false
        | '1' -> true
        | _ -> failwith "neither 0 or 1"
      ) (BatString.to_list binary)
    in
  let (h :: tl) = pad_left false target_len bl in
  (h, tl)

let word256_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 256 b in
  Word256.W256 (h, tl)

let word160_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 160 b in
  Word160.W160 (h, tl)

let byte_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 8 b in
  Word8.W8 (h, tl)

let big_int_of_bit_list bl =
  let nums : Big_int.big_int list = List.map (fun x -> if x then Big_int.unit_big_int else Big_int.zero_big_int) bl in
  List.fold_left (fun x y -> Big_int.(add_big_int y (mult_int_big_int 2 x))) Big_int.zero_big_int nums

let big_int_of_word256 (Word256.W256 (h, tl)) : Big_int.big_int =
  big_int_of_bit_list (h :: tl)

let big_int_of_word160 (Word160.W160 (h, tl)) : Big_int.big_int =
  big_int_of_bit_list (h :: tl)




(*val program_sem : variable_env -> constant_env -> int -> nat -> program_result*)

let empty_program : program =
  { program_content = (fun _ -> None)
  ; program_length = 0
  ; program_annotation = (fun _ -> [])
  }

let dummy_constant_env : constant_env =
  { cenv_program = empty_program
  ; cenv_this = word160_of_big_int (Big_int.big_int_of_int 100)
  }

let empty_memory : memory = (fun _ -> byte_of_big_int Big_int.zero_big_int)

let zero_word = word256_of_big_int Big_int.zero_big_int

let empty_balance _ = zero_word

let dummy_address = word160_of_big_int (Big_int.big_int_of_int 144545)

let empty_ext_program (_ : Word160.word160) = empty_program

let dummy_block_info : block_info =
  { block_blockhash = (fun _ -> zero_word)
  ; block_coinbase = dummy_address
  ; block_timestamp = zero_word
  ; block_number = zero_word
  ; block_difficulty = zero_word
  ; block_gaslimit = zero_word
  ; block_gasprice = zero_word
  }

let dummy_variable_env : variable_env =
  { venv_stack = []
  ; venv_memory = empty_memory
  ; venv_memory_usage = 0
  ; venv_storage = empty_storage
  ; venv_pc = 0
  ; venv_balance = empty_balance
  ; venv_caller = dummy_address
  ; venv_value_sent = zero_word
  ; venv_data_sent = []
  ; venv_storage_at_call = empty_storage
  ; venv_balance_at_call = empty_balance
  ; venv_origin = dummy_address
  ; venv_ext_program = empty_ext_program
  ; venv_block = dummy_block_info
  ; venv_gas = 50000
  ; venv_account_existence = fun _ -> false
  }



let () =
  let x : Word256.word256 = Word256.W256 (true, []) in
  let open Big_int in
  Printf.printf "hello %s\n" (string_of_big_int (big_int_of_word256 (word256_of_big_int (BatBig_int.big_int_of_int (333)))))
