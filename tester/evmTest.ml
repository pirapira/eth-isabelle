open Evm
open Conv

(*val program_sem : variable_env -> constant_env -> int -> nat -> program_result*)

let empty_program : program =
  { program_content = (fun _ -> None)
  ; program_length = 0
  ; program_annotation = (fun _ -> [])
  }

let dummy_constant_ctx : constant_ctx =
  { cctx_program = empty_program
  ; cctx_this = word160_of_big_int (Big_int.big_int_of_int 100)
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

let dummy_variable_con : variable_ctx =
  { vctx_stack = []
  ; vctx_memory = empty_memory
  ; vctx_memory_usage = 0
  ; vctx_storage = empty_storage
  ; vctx_pc = 0
  ; vctx_balance = empty_balance
  ; vctx_caller = dummy_address
  ; vctx_value_sent = zero_word
  ; vctx_data_sent = []
  ; vctx_storage_at_call = empty_storage
  ; vctx_balance_at_call = empty_balance
  ; vctx_origin = dummy_address
  ; vctx_ext_program = empty_ext_program
  ; vctx_block = dummy_block_info
  ; vctx_gas = 50000
  ; vctx_account_existence = (fun _ -> false)
  ; vctx_touched_storage_index = []
  }


let () =
  let x : Word256.word256 = Word256.W256 (true, []) in
  let open Big_int in
  let () = Printf.printf "hello %s\n" (string_of_big_int (big_int_of_word256 (word256_of_big_int (BatBig_int.big_int_of_int (333))))) in
  let (r : program_result) = program_sem dummy_variable_con dummy_constant_ctx 200 300 in
  let f = format_program_result r in
  let () = Easy_format.Pretty.to_stdout f in
  let () = Printf.printf "\ncalled EVM.\n" in
  ()
