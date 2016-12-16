open Evm

let word256_of_big_int (b : Big_int.big_int) =
  let binary = BatBig_int.to_string_in_binary b in
  (** now here, the first char might be - or +, you can say, not supporting negative *)
  binary


let () =
  let x : Word256.word256 = Word256.W256 (true, []) in
  Printf.printf "hello %s\n" (word256_of_big_int (BatBig_int.big_int_of_int (-333)))
