open Evm
open Conv

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
