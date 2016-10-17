theory Parse

imports Main "./Instructions" 

begin

type_synonym "nibble" = "4 word"
type_synonym "byte" = "8 word"

datatype parse_single_result =
  Complete inst
| Incomplete "(byte list \<Rightarrow> (inst * byte list) option)"

definition parse_single :: "nibble \<Rightarrow> nibble \<Rightarrow> parse_single_result"
where
  "parse_single m n = 
    (let unknown = Unknown (word_rcat [m,n]) in
    (if m = 0x0 then
       Complete (if n = 0x0 then Misc STOP
        else if n = 0x1 then Arith ADD
        else if n = 0x2 then Arith MUL
        else if n = 0x3 then Arith SUB
        else if n = 0x4 then Arith DIV
        else if n = 0x5 then Sarith SDIV
        else if n = 0x6 then Arith MOD
        else if n = 0x7 then Sarith SMOD
        else if n = 0x8 then Arith ADDMOD
        else if n = 0x9 then Arith MULMOD
        else if n = 0xa then Arith EXP
        else if n = 0xb then Sarith SIGNEXTEND
        else unknown)
      else if m = 0x1 then
       Complete (if n = 0x0 then Arith LT
        else if n = 0x1 then Arith GT
        else if n = 0x2 then Sarith SLT
        else if n = 0x3 then Sarith SGT
        else if n = 0x4 then Arith EQ
        else if n = 0x5 then Arith ISZERO
        else if n = 0x6 then Bits inst_AND
        else if n = 0x7 then Bits inst_OR
        else if n = 0x8 then Bits inst_XOR
        else if n = 0x9 then Bits inst_NOT
        else if n = 0xa then Bits BYTE
        else Unknown (word_rcat [m,n])
        )
      else if m = 0x2 then
       Complete (if n = 0x0 then Arith SHA3
        else unknown)
      else if m = 0x3 then
       Complete (if n = 0x0 then Info ADDRESS
        else if n = 0x1 then Info BALANCE
        else if n = 0x2 then Info ORIGIN
        else if n = 0x3 then Info CALLER
        else if n = 0x4 then Info CALLVALUE
        else if n = 0x5 then Stack CALLDATALOAD
        else if n = 0x6 then Info CALLDATASIZE
        else if n = 0x7 then Memory CALLDATACOPY
        else if n = 0x8 then Info CODESIZE
        else if n = 0x9 then Memory CODECOPY
        else if n = 0xa then Info GASPRICE
        else if n = 0xb then Info EXTCODESIZE
        else if n = 0xc then Memory EXTCODECOPY
        else unknown)
      else if m = 0x4 then
       Complete (if n = 0x0 then Info BLOCKHASH
        else if n = 0x1 then Info COINBASE
        else if n = 0x2 then Info TIMESTAMP
        else if n = 0x3 then Info NUMBER
        else if n = 0x4 then Info DIFFICULTY
        else if n = 0x5 then Info GASLIMIT
        else unknown
       )
      else if m = 0x5 then
       Complete (if n = 0x0 then Stack POP
        else if n = 0x1 then Memory MLOAD
        else if n = 0x2 then Memory MSTORE
        else if n = 0x3 then Memory MSTORE8
        else if n = 0x4 then Storage SLOAD
        else if n = 0x5 then Storage SSTORE
        else if n = 0x6 then Pc JUMP
        else if n = 0x7 then Pc JUMPI
        else if n = 0x8 then Pc PC
        else if n = 0x9 then Memory MSIZE
        else if n = 0xa then Info GAS
        else if n = 0xb then Pc JUMPDEST
        else unknown)
      else if (m = 0x6) \<or> (m = 0x7) then
        (let bytes = (unat m - 6) * 16 + unat n + 1 in
        (Incomplete (\<lambda> (rest :: 8 word list).
          if length rest < bytes then None
          else Some (Stack (PUSH_N (take bytes rest)), (drop bytes rest))
          ) ))
      else if m = 0x8 then
        Complete (Dup (unat n + 1))
      else if m = 0x9 then
        Complete (Swap (unat n + 1))
      else if m = 0xa then
        Complete (if n = 0x0 then Log LOG0
        else if n = 0x1 then Log LOG1
        else if n = 0x2 then Log LOG2
        else if n = 0x3 then Log LOG3
        else if n = 0x4 then Log LOG4
        else unknown)
      else if m = 0xb \<or> m = 0xc \<or> m = 0xd \<or> m = 0xe then
        Complete unknown
      else Complete
      (if n = 0x0 then Misc CREATE
       else if n = 0x1 then Misc CALL
       else if n = 0x2 then Misc CALLCODE
       else if n = 0x3 then Misc RETURN
       else if n = 0xf then Misc SUICIDE
       else unknown)))"

definition parse_byte :: "byte \<Rightarrow> parse_single_result"
where
"parse_byte b =
   (let lst = word_rsplit b in
    parse_single (lst ! 0) (lst ! 1)
   )"

(* Now, need to parse a sequence of bytes.
   When you meet Incomplete, you have to make sure that the 
   result is shorter.
*)

fun parse_bytes :: "byte list \<Rightarrow> (inst list \<times> byte list) option"
where
"parse_bytes [] = Some ([], [])" |
"parse_bytes (b # rest) =
   (case parse_byte b of
     Complete i \<Rightarrow>
     (case parse_bytes rest of
       None \<Rightarrow> Some ([i], rest)
     | Some (tail, rest) \<Rightarrow> Some (i # tail, rest))
   | Incomplete f \<Rightarrow>
     (case f rest of
       None \<Rightarrow> None
     | Some (i, rrest) \<Rightarrow>
       if length rrest \<le> length rest then
       (case parse_bytes rrest of
         None \<Rightarrow> Some ([i], rrest)
       | Some (tail, rest) \<Rightarrow> Some (i # tail, rest))
       else None)
   )
   "
   
declare parse_bytes.simps [simp]

value "parse_bytes [0x60, 0x60, 0x60, 0x40]"

text "I still want to parse something like 0x6060604052604051"
text "How do I do that?"

text "Maybe Isabelle/HOL has some string literals."

value "''foobar'' :: char list"

definition byte_of_char :: "char \<Rightarrow> byte"
where
"byte_of_char c = of_nat (String.nat_of_char c)"

declare byte_of_char_def [simp]

definition int_of_hex_char :: "char \<Rightarrow> int"
where
"int_of_hex_char c =
   (case c of
      CHR ''0'' \<Rightarrow> 0
    | CHR ''1'' \<Rightarrow> 1
    | CHR ''2'' \<Rightarrow> 2
    | CHR ''3'' \<Rightarrow> 3
    | CHR ''4'' \<Rightarrow> 4
    | CHR ''5'' \<Rightarrow> 5
    | CHR ''6'' \<Rightarrow> 6
    | CHR ''7'' \<Rightarrow> 7
    | CHR ''8'' \<Rightarrow> 8
    | CHR ''9'' \<Rightarrow> 9
    | CHR ''a'' \<Rightarrow> 10
    | CHR ''b'' \<Rightarrow> 11
    | CHR ''c'' \<Rightarrow> 12
    | CHR ''d'' \<Rightarrow> 13
    | CHR ''e'' \<Rightarrow> 14
    | CHR ''f'' \<Rightarrow> 15
   )"
   
declare int_of_hex_char_def [simp]
    
value "int_of_hex_char (CHR ''0'')"

fun bytes_of_hex_content :: "char list \<Rightarrow> byte list"
where
"bytes_of_hex_content [] = []" |
"bytes_of_hex_content (m # n # rest) = (word_of_int ((int_of_hex_char m) * 16 + int_of_hex_char n) # bytes_of_hex_content rest)"

definition dao :: "byte list"
where
"dao = concat (map bytes_of_hex_content [dao00, dao01, dao02, dao03, dao04, dao05, dao06, dao07, dao08, dao09, dao0a, dao0b,
dao0c, dao0d, dao0e, dao0f, dao10, dao11, dao12, dao13, dao14, dao15, dao16, dao17, dao18, dao19,
dao1a])"

value "dao"


definition dao_insts :: "(inst list \<times> byte list) option"
where "dao_insts = parse_bytes dao"

value "take 33 dao"

value "parse_bytes dao"

declare parse_byte_def [simp]
declare parse_single_def [simp]

value "parse_byte 111"

value "parse_bytes [111, 200, 75, 166, 188, 149, 72, 64, 8, 246, 54, 47, 147, 22, 14, 243, 229, 99]"

end
