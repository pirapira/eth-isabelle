theory Parse

imports Main "./Instructions" 

begin

type_synonym "nibble" = "4 word"
type_synonym "byte" = "8 word"

datatype parse_byte_result =
  Complete inst
| Incomplete "(byte list \<Rightarrow> (inst * byte list) option)"

abbreviation "push n ==
      Incomplete (\<lambda> (rest :: byte list).
      (if length rest < n then None
       else Some (Stack (PUSH_N (take n rest)), drop n rest)))"


definition parse_byte :: "byte \<Rightarrow> parse_byte_result"
where
"parse_byte =
  (\<lambda> b. Complete (Unknown b))
  ( 0x00 := Complete (Misc STOP)
  , 0x01 := Complete (Arith ADD)
  , 0x02 := Complete (Arith MUL)
  , 0x03 := Complete (Arith SUB)
  , 0x04 := Complete (Arith DIV)
  , 0x05 := Complete (Sarith SDIV)
  , 0x06 := Complete (Arith MOD)
  , 0x07 := Complete (Sarith SMOD)
  , 0x08 := Complete (Arith ADDMOD)
  , 0x09 := Complete (Arith MULMOD)
  , 0x0a := Complete (Arith EXP)
  , 0x0b := Complete (Sarith SIGNEXTEND)
  , 0x10 := Complete (Arith LT)
  , 0x11 := Complete (Arith GT)
  , 0x12 := Complete (Sarith SLT)
  , 0x13 := Complete (Sarith SGT)
  , 0x14 := Complete (Arith EQ)
  , 0x15 := Complete (Arith ISZERO)
  , 0x16 := Complete (Bits inst_AND)
  , 0x17 := Complete (Bits inst_OR)
  , 0x18 := Complete (Bits inst_XOR)
  , 0x19 := Complete (Bits inst_NOT)
  , 0x1a := Complete (Bits BYTE)
  , 0x20 := Complete (Arith SHA3)
  , 0x30 := Complete (Info ADDRESS)
  , 0x31 := Complete (Info BALANCE)
  , 0x32 := Complete (Info ORIGIN)
  , 0x33 := Complete (Info CALLER)
  , 0x34 := Complete (Info CALLVALUE)
  , 0x35 := Complete (Stack CALLDATALOAD)
  , 0x36 := Complete (Info CALLDATASIZE)
  , 0x37 := Complete (Memory CALLDATACOPY)
  , 0x38 := Complete (Info CODESIZE)
  , 0x39 := Complete (Memory CODECOPY)
  , 0x3a := Complete (Info GASPRICE)
  , 0x3b := Complete (Info EXTCODESIZE)
  , 0x3c := Complete (Memory EXTCODECOPY)
  , 0x40 := Complete (Info BLOCKHASH)
  , 0x41 := Complete (Info COINBASE)
  , 0x42 := Complete (Info TIMESTAMP)
  , 0x43 := Complete (Info NUMBER)
  , 0x44 := Complete (Info DIFFICULTY)
  , 0x45 := Complete (Info GASLIMIT)
  , 0x50 := Complete (Stack POP)
  , 0x51 := Complete (Memory MLOAD)
  , 0x52 := Complete (Memory MSTORE)
  , 0x53 := Complete (Memory MSTORE8)
  , 0x54 := Complete (Storage SLOAD)
  , 0x55 := Complete (Storage SSTORE)
  , 0x56 := Complete (Pc JUMP)
  , 0x57 := Complete (Pc JUMPI)
  , 0x58 := Complete (Pc PC)
  , 0x59 := Complete (Memory MSIZE)
  , 0x5a := Complete (Info GAS)
  , 0x5b := Complete (Pc JUMPDEST)
  , 0x60 := push 1
  , 0x61 := push 2
  , 0x62 := push 3
  , 0x63 := push 4
  , 0x64 := push 5
  , 0x65 := push 6
  , 0x66 := push 7
  , 0x67 := push 8
  , 0x68 := push 9
  , 0x69 := push 10
  , 0x6a := push 11
  , 0x6b := push 12
  , 0x6c := push 13
  , 0x6d := push 14
  , 0x6e := push 15
  , 0x6f := push 16
  , 0x70 := push 17
  , 0x71 := push 18
  , 0x72 := push 19
  , 0x73 := push 20
  , 0x74 := push 21
  , 0x75 := push 22
  , 0x76 := push 23
  , 0x77 := push 24
  , 0x78 := push 25
  , 0x79 := push 26
  , 0x7a := push 27
  , 0x7b := push 28
  , 0x7c := push 29
  , 0x7d := push 30
  , 0x7e := push 31
  , 0x7f := push 32
  , 0x80 := Complete (Dup 1)
  , 0x81 := Complete (Dup 2)
  , 0x82 := Complete (Dup 3)
  , 0x83 := Complete (Dup 4)
  , 0x84 := Complete (Dup 5)
  , 0x85 := Complete (Dup 6)
  , 0x86 := Complete (Dup 7)
  , 0x87 := Complete (Dup 8)
  , 0x88 := Complete (Dup 9)
  , 0x89 := Complete (Dup 10)
  , 0x8a := Complete (Dup 11)
  , 0x8b := Complete (Dup 12)
  , 0x8c := Complete (Dup 13)
  , 0x8d := Complete (Dup 14)
  , 0x8e := Complete (Dup 15)
  , 0x8f := Complete (Dup 16)
  , 0x90 := Complete (Swap 1)
  , 0x91 := Complete (Swap 2)
  , 0x92 := Complete (Swap 3)
  , 0x93 := Complete (Swap 4)
  , 0x94 := Complete (Swap 5)
  , 0x95 := Complete (Swap 6)
  , 0x96 := Complete (Swap 7)
  , 0x97 := Complete (Swap 8)
  , 0x98 := Complete (Swap 9)
  , 0x99 := Complete (Swap 10)
  , 0x9a := Complete (Swap 11)
  , 0x9b := Complete (Swap 12)
  , 0x9c := Complete (Swap 13)
  , 0x9d := Complete (Swap 14)
  , 0x9e := Complete (Swap 15)
  , 0x9f := Complete (Swap 16)
  , 0xa0 := Complete (Log LOG0)
  , 0xa1 := Complete (Log LOG1)
  , 0xa2 := Complete (Log LOG2)
  , 0xa3 := Complete (Log LOG3)
  , 0xa4 := Complete (Log LOG4)
  , 0xf0 := Complete (Misc CREATE)
  , 0xf1 := Complete (Misc CALL)
  , 0xf2 := Complete (Misc CALLCODE)
  , 0xf3 := Complete (Misc RETURN)
  , 0xf4 := Complete (Misc DELEGATECALL)
  , 0xff := Complete (Misc SUICIDE)
       )"

value "parse_byte 0xa8"

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
declare parse_byte_def [simp]
       

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

value "parse_byte 111"

value "parse_bytes [111, 200, 75, 166, 188, 149, 72, 64, 8, 246, 54, 47, 147, 22, 14, 243, 229, 99]"

end
