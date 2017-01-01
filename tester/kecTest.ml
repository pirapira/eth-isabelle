let () =
  let () = Printf.printf "49 is as bool list %s\n"
                         (Conv.string_of_bool_list (Keccak.boolListFromWord64 (Int64.of_int 49))) in
  let () = Printf.printf "[49] is hashed into %s\n"
                (Conv.string_of_byte_list
                   (Keccak.keccak' [Conv.byte_of_int 49])) in
  let () = Printf.printf "sha3_update [49] initial_pos initial_st is hashed into %s\n"
                (Conv.string_of_int_64list
                   (Keccak.(sha3_update [Conv.byte_of_int 49] initial_pos initial_st))) in
  let () = Printf.printf "iota 1 [49,,,] is %s\n"
                (Conv.string_of_64list
                   (Keccak.(iota 1 (List.map Int64.of_int [49; 0;0;0;0;0;0])))) in
  let () = Printf.printf "keccakf [49,,,,] is %s\n"
                         (Conv.string_of_64list
                            (Keccak.keccakf
                                ( List.map Int64.of_int [49;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]))) in
  let () = Printf.printf "word_rsplit 49 is %s\n"
                         (Conv.string_of_byte_list Keccak.(word_rsplit (Int64.of_int 49))) in
  let () = Printf.printf "boolList from word64 49 is %s\n"
                         (Conv.string_of_bool_list Keccak.(boolListFromWord64 (Int64.of_int 49))) in
  ()
