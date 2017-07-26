open Evm
open Conv

let empty_program : program =
  { program_content = (fun _ -> None)
  ; program_length = Nat_big_num.of_int 0
  }

let dummy_constant_ctx : constant_ctx =
  { cctx_program = empty_program
  ; cctx_this = word160_of_big_int (Big_int.big_int_of_int 100)
  ; cctx_hash_filter = (fun _ -> true)
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
  ; vctx_memory_usage = Nat_big_num.of_int 0
  ; vctx_storage = empty_storage
  ; vctx_pc = Nat_big_num.of_int 0
  ; vctx_balance = empty_balance
  ; vctx_caller = dummy_address
  ; vctx_value_sent = zero_word
  ; vctx_data_sent = []
  ; vctx_storage_at_call = empty_storage
  ; vctx_balance_at_call = empty_balance
  ; vctx_origin = dummy_address
  ; vctx_ext_program = empty_ext_program
  ; vctx_block = dummy_block_info
  ; vctx_gas = Nat_big_num.of_int 50000
  ; vctx_account_existence = (fun _ -> false)
  ; vctx_touched_storage_index = []
  ; vctx_logs = []
  ; vctx_refund = Nat_big_num.of_int 0
  }
