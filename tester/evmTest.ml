open Evm
open Conv

(*val program_sem : variable_env -> constant_env -> int -> nat -> program_result*)

open Constant

let () =
  let _ : Word256.word256 = Word256.W256 (true, []) in
  let open Big_int in
  let () = Printf.printf "hello %s\n" (string_of_big_int (big_int_of_word256 (word256_of_big_int (BatBig_int.big_int_of_int (333))))) in
  let (r : program_result) = program_sem_wrapper dummy_constant_ctx 300 (ProgramStepRunOut dummy_variable_con) in
  let f = format_program_result r in
  let () = Easy_format.Pretty.to_stdout f in
  let () = Printf.printf "\ncalled EVM.\n" in
  let () = Printf.printf "0is %s\n" (string_of_big_int (Conv.big_int_of_word256 (Conv.word256_of_big_int (Big_int.zero_big_int)))) in
  let () = Printf.printf "0x00 is converted into %s\n" (string_of_big_int (Conv.big_int_of_word256 (Keccak.word_of_bytes [byte_of_int 0]))) in
  let () = Printf.printf "false 256 times is converted into %s\n" (string_of_big_int (Conv.big_int_of_word256 (Word256.word256FromBoollist (Lem_pervasives.replicate 256 false)))) in
  let () =
    List.iter
      (Printf. printf "%b ")
      (Keccak.list_fill_right false( 256) (List.concat (Lem_pervasives.map Word8.boolListFromWord8 (List.rev [byte_of_int 0])))) in
  let () = Printf.printf "....\n" in
  let () =
    List.iter
      (Printf. printf "%b ")
      (Word8.boolListFromWord8 (byte_of_int 0)) in
  ()
