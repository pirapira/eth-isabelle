let pad_left (elm : 'a) (len : int) (orig : 'a list) =
  let remaining = len - List.length orig in
  let () = Printf.printf "padding: remaining: %d\n%!" remaining in
  let padding = BatList.make remaining elm in
  padding @ orig

let pad_left_string (padding : char) (len : int) (orig : string) =
  let lst = BatString.to_list orig in
  let lst = pad_left '0' len lst in
  BatString.of_list lst

let word_of_big_int (target_len : int) (b : Big_int.big_int) =
  let () = if BatBig_int.(lt_big_int b zero_big_int) then failwith "negative number cannot be turned into word256" else () in
  let binary : string = BatBig_int.to_string_in_binary b in
  (* should be a sequence of 0s and 1s *)
  let bl : bool list =
    List.map (fun (digit : char) ->
        match digit with
        | '0' -> false
        | '1' -> true
        | _ -> failwith "neither 0 or 1"
      ) (BatString.to_list binary)
    in
  let (h :: tl) = pad_left false target_len bl in
  (h, tl)

let word256_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 256 b in
  Word256.W256 (h, tl)

let word160_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 160 b in
  Word160.W160 (h, tl)

let byte_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 8 b in
  Word8.W8 (h, tl)

let byte_of_int (i : int) =
  byte_of_big_int (Big_int.big_int_of_int i)

let big_int_of_bit_list bl =
  let nums : Big_int.big_int list = List.map (fun x -> if x then Big_int.unit_big_int else Big_int.zero_big_int) bl in
  List.fold_left (fun x y -> Big_int.(add_big_int y (mult_int_big_int 2 x))) Big_int.zero_big_int nums

let big_int_of_word256 (Word256.W256 (h, tl)) : Big_int.big_int =
  big_int_of_bit_list (h :: tl)

let big_int_of_word160 (Word160.W160 (h, tl)) : Big_int.big_int =
  big_int_of_bit_list (h :: tl)


(** [string_of_address a] returns a string of 40 characters containing [0-9] and [a-f] *)
let string_of_address (addr : Word160.word160) : string =
  let b = big_int_of_word160 addr in
  let str = BatBig_int.to_string_in_hexa b in
  pad_left_string '0' 40 str

let rec byte_list_of_hex_string (s : string) =
  if String.length s < 2 then []
  else
    let first_byte = int_of_string ("0x"^(BatString.left s 2)) in
    let rest = BatString.tail s 2 in
    byte_of_int first_byte :: byte_list_of_hex_string rest

let format_quad_as_list
      (act : Evm.contract_action) (storage : Evm.storage)
      (bal : Evm.address -> Evm.w256) (stashed_opt : (Evm.variable_ctx * int * int) option) : Easy_format.t list =
  let open Easy_format in
  [ Label ((Atom ("Action", atom), label), Atom ("to be printed", atom))
  ; Atom ("storage to be printed", atom)
  ; Atom ("balance to be printed", atom)
  ; Atom ("stashed_opt to be printed", atom)
  ]

let format_program_result (r : Evm.program_result) : Easy_format.t =
  let open Evm in
  let open Easy_format in
  let list_usual = ("{", ",", "}", list) in
  match r with
  | ProgramStepRunOut -> Atom ("ProgramStepRunOut", atom)
  | ProgramToEnvironment (act, storage, bal, touched, stashed_opt) ->
     Label ((Atom ("ProgramToEnvironment", atom), label),
            List (list_usual, format_quad_as_list act storage bal stashed_opt))
  | ProgramInvalid -> Atom ("ProgramInvalid", atom)
  | ProgramAnnotationFailure -> Atom ("ProgramAnnotationFailure", atom)
  | ProgramInit cenv ->
     Label ((Atom ("ProgramInit", atom), label),
            List (list_usual, [(* to be filled *)]))
