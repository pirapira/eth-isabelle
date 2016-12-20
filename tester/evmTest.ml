open Evm
open Conv

(*val program_sem : variable_env -> constant_env -> int -> nat -> program_result*)

open Constant

let () =
  let x : Word256.word256 = Word256.W256 (true, []) in
  let open Big_int in
  let () = Printf.printf "hello %s\n" (string_of_big_int (big_int_of_word256 (word256_of_big_int (BatBig_int.big_int_of_int (333))))) in
  let (r : program_result) = program_sem dummy_variable_con dummy_constant_ctx 200 300 in
  let f = format_program_result r in
  let () = Easy_format.Pretty.to_stdout f in
  let () = Printf.printf "\ncalled EVM.\n" in
  ()
