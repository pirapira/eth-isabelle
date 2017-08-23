open Keccak
open Evm

module IntMap = BatMap.Make(BatInt)

(** [program_impl] implements the partial map in [program] using
 [Map] library of OCaml *)
type program_impl =
  { p_impl_content : inst IntMap.t
  ; p_impl_length : int
 (* annotations do not exist yet. *)
  }

let empty_program_impl : program_impl =
  { p_impl_content = IntMap.empty
  ; p_impl_length = 0
  }

let program_from_impl (imp : program_impl) : program =
  { program_content =
      (fun (pos : Nat_big_num.num) ->
        try Some (IntMap.find (Nat_big_num.to_int pos) imp.p_impl_content)
        with
        | Not_found -> None
        | Failure _ -> None
      )
  ; program_length = Nat_big_num.of_int imp.p_impl_length
  }

let rec add_unknown_bytes_from (pos : int) (lst : byte list) (orig : inst IntMap.t) : inst IntMap.t =
  match lst with
  | [] -> orig
  | h :: t ->
     add_unknown_bytes_from (pos + 1) t (IntMap.add pos (Unknown h) orig)

(** The payload of PUSH instructions are stored as Unknown *)
let store_instruction (inst : inst) (orig : program_impl) : program_impl =
  let orig_map = orig.p_impl_content in
  let added_map = IntMap.add orig.p_impl_length inst orig_map in
  let (new_map, new_length) =
    match inst with
    | Stack (PUSH_N lst) ->
       let new_map = add_unknown_bytes_from (orig.p_impl_length + 1) lst added_map in
       (new_map, orig.p_impl_length + 1 + List.length lst)
    | _ ->
       (added_map, orig.p_impl_length + 1)
  in
  { p_impl_content = new_map
  ; p_impl_length = new_length
  }

let string_right_fill (pad : char) (target : int) (orig : string) : string =
  let () = assert (target >= String.length orig) in
  let pad_len = target - String.length orig in
  let padding = String.make pad_len pad in
  orig ^ padding

let parse_instruction (str : string) : (inst * string) option =
  let opcode = BatString.left str 2 in
  let rest = BatString.tail str 2 in
  match opcode with
  | "" -> None
  | "00" -> Some (Misc STOP, rest)
  | "01" -> Some (Arith ADD, rest)
  | "02" -> Some (Arith MUL, rest)
  | "03" -> Some (Arith SUB, rest)
  | "04" -> Some (Arith DIV, rest)
  | "05" -> Some (Sarith SDIV, rest)
  | "06" -> Some (Arith MOD, rest)
  | "07" -> Some (Sarith SMOD, rest)
  | "08" -> Some (Arith ADDMOD, rest)
  | "09" -> Some (Arith MULMOD, rest)
  | "0a" -> Some (Arith EXP, rest)
  | "0b" -> Some (Sarith SIGNEXTEND, rest)
  | "10" -> Some (Arith Inst_LT, rest)
  | "11" -> Some (Arith Inst_GT, rest)
  | "12" -> Some (Sarith SLT, rest)
  | "13" -> Some (Sarith SGT, rest)
  | "14" -> Some (Arith Inst_EQ, rest)
  | "15" -> Some (Arith ISZERO, rest)
  | "16" -> Some (Bits Inst_AND, rest)
  | "17" -> Some (Bits Inst_OR, rest)
  | "18" -> Some (Bits Inst_XOR, rest)
  | "19" -> Some (Bits Inst_NOT, rest)
  | "1a" -> Some (Bits BYTE, rest)
  | "20" -> Some (Arith SHA3, rest)
  | "30" -> Some (Info ADDRESS, rest)
  | "31" -> Some (Info BALANCE, rest)
  | "32" -> Some (Info ORIGIN, rest)
  | "33" -> Some (Info CALLER, rest)
  | "34" -> Some (Info CALLVALUE, rest)
  | "35" -> Some (Stack CALLDATALOAD, rest)
  | "36" -> Some (Info CALLDATASIZE, rest)
  | "37" -> Some (Memory CALLDATACOPY, rest)
  | "38" -> Some (Info CODESIZE, rest)
  | "39" -> Some (Memory CODECOPY, rest)
  | "3a" -> Some (Info GASPRICE, rest)
  | "3b" -> Some (Info EXTCODESIZE, rest)
  | "3c" -> Some (Memory EXTCODECOPY, rest)
  | "40" -> Some (Info BLOCKHASH, rest)
  | "41" -> Some (Info COINBASE, rest)
  | "42" -> Some (Info TIMESTAMP, rest)
  | "43" -> Some (Info NUMBER, rest)
  | "44" -> Some (Info DIFFICULTY, rest)
  | "45" -> Some (Info GASLIMIT, rest)
  | "50" -> Some (Stack POP, rest)
  | "51" -> Some (Memory MLOAD, rest)
  | "52" -> Some (Memory MSTORE, rest)
  | "53" -> Some (Memory MSTORE8, rest)
  | "54" -> Some (Storage SLOAD, rest)
  | "55" -> Some (Storage SSTORE, rest)
  | "56" -> Some (Pc JUMP, rest)
  | "57" -> Some (Pc JUMPI, rest)
  | "58" -> Some (Pc PC, rest)
  | "59" -> Some (Memory MSIZE, rest)
  | "5a" -> Some (Info GAS, rest)
  | "5b" -> Some (Pc JUMPDEST, rest)
  | "a0" -> Some (Log LOG0, rest)
  | "a1" -> Some (Log LOG1, rest)
  | "a2" -> Some (Log LOG2, rest)
  | "a3" -> Some (Log LOG3, rest)
  | "a4" -> Some (Log LOG4, rest)
  | "f0" -> Some (Misc CREATE, rest)
  | "f1" -> Some (Misc CALL, rest)
  | "f2" -> Some (Misc CALLCODE, rest)
  | "f3" -> Some (Misc RETURN, rest)
  | "f4" -> Some (Misc DELEGATECALL, rest)
  | "ff" -> Some (Misc SUICIDE, rest)
  | _ ->
     let opcode_num = int_of_string ("0x"^opcode) in
     if 0x60 <= opcode_num && opcode_num <= 0x7f then
       let l = opcode_num - 0x60 + 1 in
       let (payload, rest) = BatString.(left rest (2 * l), tail rest (2 * l)) in
       let payload =
         if String.length payload < 2 * l then
           string_right_fill '0' (2*l) payload
         else
           payload in
       Some (Stack (PUSH_N (Conv.byte_list_of_hex_string payload)), rest)
     else if 0x80 <= opcode_num && opcode_num <= 0x8f then
       Some (Dup (Conv.nibble_of_int (opcode_num - 0x80)), rest)
     else if 0x90 <= opcode_num && opcode_num <= 0x9f then
       Some (Swap (Conv.nibble_of_int (opcode_num - 0x90)), rest)
     else if String.length opcode = 2 then
       Some (Unknown (Conv.byte_of_int opcode_num), rest)
     else
       None

let rec parse_code_inner (acc : program_impl) (hex_inner : string) : program * string =
  match parse_instruction hex_inner with
  | None -> (program_from_impl acc, hex_inner)
  | Some (instr, rest) ->
     parse_code_inner (store_instruction instr acc) rest

(** [parse_code "0x...." returns a program and the
 * remaining string
 *)
let parse_code (hex : string) : program * string =
  if BatString.left hex 2 <> "0x"
  then
    failwith "parse_code: prefix is not 0x"
  else
    parse_code_inner empty_program_impl (BatString.tail hex 2)
