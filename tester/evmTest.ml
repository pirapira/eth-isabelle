open Evm
open Conv

(*val program_sem : variable_env -> constant_env -> int -> nat -> program_result*)

let empty_program : program =
  { program_content = (fun _ -> None)
  ; program_length = 0
  ; program_annotation = (fun _ -> [])
  }

let dummy_constant_con : constant_con =
  { ccon_program = empty_program
  ; ccon_this = word160_of_big_int (Big_int.big_int_of_int 100)
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

let dummy_variable_con : variable_con =
  { vcon_stack = []
  ; vcon_memory = empty_memory
  ; vcon_memory_usage = 0
  ; vcon_storage = empty_storage
  ; vcon_pc = 0
  ; vcon_balance = empty_balance
  ; vcon_caller = dummy_address
  ; vcon_value_sent = zero_word
  ; vcon_data_sent = []
  ; vcon_storage_at_call = empty_storage
  ; vcon_balance_at_call = empty_balance
  ; vcon_origin = dummy_address
  ; vcon_ext_program = empty_ext_program
  ; vcon_block = dummy_block_info
  ; vcon_gas = 50000
  ; vcon_account_existence = fun _ -> false
  }


let () =
  let x : Word256.word256 = Word256.W256 (true, []) in
  let open Big_int in
  let () = Printf.printf "hello %s\n" (string_of_big_int (big_int_of_word256 (word256_of_big_int (BatBig_int.big_int_of_int (333))))) in
  let (_ : program_result) = program_sem dummy_variable_con dummy_constant_con 200 300 in
  let () = Printf.printf "called EVM.\n" in
  ()
