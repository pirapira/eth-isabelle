let () =
  let () = Printf.printf "49 is as bool list %s\n"
                         (Conv.string_of_bool_list (Word64.boolListFromWord64 (Int64.of_int 49))) in
  let () = Printf.printf "'256' is hashed into %s\n"
                (Conv.string_of_byte_list
                   (Keccak.keccak' (List.map Conv.byte_of_int [50;53;54]))) in
  let () = Printf.printf
             "the last 64 word is split into %s\n"
             (Conv.string_of_byte_list
                (List.rev (Keccak.word_rsplit
                             (Big_int.int64_of_big_int
                             (Big_int.big_int_of_string
"9223372036854775807"))))) in
  let () = Printf.printf
             "the last 64 word is split into a boollist %s\n"
             (Conv.string_of_bool_list
                (Word64.boolListFromWord64
                             (Big_int.int64_of_big_int
                             (Big_int.big_int_of_string "-5899601735930514117")))) in
  ()
