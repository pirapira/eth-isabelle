open Evm

let pad_left (elm : 'a) (len : int) (orig : 'a list) =
  let remaining = len - List.length orig in
  let padding = BatList.make remaining elm in
  let ret = padding @ orig in
  let () = assert (List.length ret = len) in
  ret

let pad_right (elm : 'a) (len : int) (orig : 'a list) =
  let remaining = len - List.length orig in
  let padding = BatList.make remaining elm in
  let ret = orig @ padding in
  let () = assert (List.length ret = len) in
  ret

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
      ) (List.rev (BatString.to_list binary))
    in
  let bl = pad_right false target_len bl in
  let Lem_word.BitSeq(_, h, tl) = Lem_word.(resizeBitSeq (Some target_len) (BitSeq (Some target_len, List.nth bl (target_len - 1), BatList.take (target_len - 1) bl))) in
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

let nibble_of_big_int (b : Big_int.big_int) =
  let (h, tl) = word_of_big_int 4 b in
  Word4.W4 (h, tl)

let byte_of_int (i : int) =
  byte_of_big_int (Big_int.big_int_of_int i)

let nibble_of_int (i : int) =
  nibble_of_big_int (Big_int.big_int_of_int i)

let big_int_of_bit_list bl =
  let nums : Big_int.big_int list = List.map (fun x -> if x then Big_int.unit_big_int else Big_int.zero_big_int) bl in
  let nums = List.rev nums in
  List.fold_left (fun x y -> Big_int.(add_big_int y (mult_int_big_int 2 x))) Big_int.zero_big_int nums

let big_int_of_word256 (Word256.W256 (h, tl)) : Big_int.big_int =
  big_int_of_bit_list (pad_right h 256 tl)

let big_int_of_word160 (Word160.W160 (h, tl)) : Big_int.big_int =
  big_int_of_bit_list (pad_right h 160 tl)

let int_of_byte (Word8.W8 (h, tl) : Word8.word8) : int =
  Big_int.int_of_big_int (big_int_of_bit_list (pad_right h 8 tl))

(** [string_of_address a] returns a string of 40 characters containing [0-9] and [a-f] *)
let string_of_address (addr : Word160.word160) : string =
  let b = big_int_of_word160 addr in
  let str = BatBig_int.to_string_in_hexa b in
  pad_left_string '0' 40 str

let rec byte_list_of_hex_string (s : string) =
  if BatString.left s 2 = "0x" then byte_list_of_hex_string (BatString.tail s 2)
  else if String.length s < 2 then []
  else
    let first_string = "0x"^(BatString.left s 2) in
    let first_byte = int_of_string first_string in
    let rest = BatString.tail s 2 in
    byte_of_int first_byte :: byte_list_of_hex_string rest

let rec hex_str_of_bl_inner (acc : string) (bs : Word8.word8 list) : string =
  match bs with
  | [] -> acc
  | h :: t ->
     hex_str_of_bl_inner (acc ^ BatPrintf.sprintf "%02x" (int_of_byte h)) t

let hex_string_of_byte_list (prefix : string) (bs : Word8.word8 list) : string =
  prefix^(hex_str_of_bl_inner "" bs)

let format_quad_as_list
      (act : Evm.contract_action)
      (stashed_opt : (Nat_big_num.num * Nat_big_num.num) option) : Easy_format.t list =
  let open Easy_format in
  [ Label ((Atom ("Action", atom), label), Atom ("to be printed", atom))
  ; Atom ("storage to be printed", atom)
  ; Atom ("balance to be printed", atom)
  ; Atom ("stashed_opt to be printed", atom)
  ]

let list_usual = ("{", ",", "}", Easy_format.list)

let format_program_result (r : Evm.instruction_result) : Easy_format.t =
  let open Evm in
  let open Easy_format in
  match r with
  | InstructionContinue _ -> Atom ("ProgramStepRunOut", atom)
  | InstructionToEnvironment (act, touched, stashed_opt) ->
     Label ((Atom ("ProgramToEnvironment", atom), label),
            List (list_usual, format_quad_as_list act stashed_opt))

let format_stack (stack : Word256.word256 list) =
  Easy_format.(Atom ("format_stack", atom))

let format_integer (i : Nat_big_num.num) : Easy_format.t =
  Easy_format.(Atom (Nat_big_num.to_string i, atom))

let format_variable_ctx (v : Evm.variable_ctx) : Easy_format.t =
  let open Easy_format in
  let open Evm in
  List (list_usual,
        [ Label ((Atom ("stack", atom), label),
                 format_stack v.vctx_stack)
        ; Label ((Atom ("gas", atom), label),
                 format_integer v.vctx_gas)
        ])

let print_variable_ctx (v : Evm.variable_ctx) : unit =
  Easy_format.Pretty.to_stdout (format_variable_ctx v)

let format_constant_ctx (c : Evm.constant_ctx) : Easy_format.t =
  Easy_format.(Atom ("cctx", atom))

let print_constant_ctx (c : Evm.constant_ctx) : unit =
  Easy_format.Pretty.to_stdout (format_constant_ctx c)


let rec bigint_assoc (key : Big_int.big_int) (lst : (Big_int.big_int * 'a) list) : 'a =
  match lst with
  | [] -> raise Not_found
  | (hk, hv) :: t ->
     if Big_int.eq_big_int key hk then hv
     else bigint_assoc key t

let string_of_word256 (Word256.W256 (h, lst)) =
  String.concat "," (List.map string_of_bool (h :: lst))

let string_of_word160 (Word160.W160 (h, lst)) =
  String.concat "," (List.map string_of_bool (h :: lst))

let string_of_bitseq (Lem_word.BitSeq (_, h, lst)) =
  String.concat "," (List.map string_of_bool (h :: lst))

let string_of_byte (b : Word8.word8) =
  string_of_int (int_of_byte b)

let string_of_byte_list (lst : Word8.word8 list) =
  String.concat "," (List.map string_of_byte lst)

let string_of_bool_list (lst : bool list) =
  String.concat "," (List.map string_of_bool lst)

let decimal_of_word256 (w : Word256.word256) =
  Big_int.string_of_big_int (big_int_of_word256 w)

let char_as_byte (c : char) : Word8.word8 =
  byte_of_int (BatChar.code c)

let string_as_byte_list (str : string) =
  (List.map char_as_byte (BatString.to_list str))

let string_of_64list (lst : Int64.t list) =
  String.concat "," (List.map Int64.to_string lst)

let string_of_int_64list ((n, lst) : (int * Int64.t list)) =
  (string_of_int n)^", "^
  string_of_64list lst

exception ToEnvironment of instruction_result

let the_stopper r = raise (ToEnvironment r)

let program_sem_wrapper c n net r =
  try
    program_sem the_stopper c n net r
  with ToEnvironment a -> a
