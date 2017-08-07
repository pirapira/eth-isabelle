
let string_to_Z str =
  let acc = ref (Z.of_int 0) in
  for i = 0 to String.length str - 1 do
     acc := Z.mul (Z.of_int 256) !acc;
     acc := Z.add !acc (Z.of_int (Char.code str.[i]))
  done;
  !acc

let decimal_of_string str =
  let num = Z.of_string str in
(*  prerr_endline ("decimal " ^ str); *)
  num

let hex_of_string str = Z.of_string str

let hexliteral_of_string str = Z.of_string_base 16 (String.sub str 4 (String.length str - 5))

let literal_of_string str = string_to_Z (String.sub str 1 (String.length str - 2))


