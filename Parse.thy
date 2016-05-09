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
      else Complete unknown))"

definition parse_byte :: "byte \<Rightarrow> parse_single_result"
where
"parse_byte b =
   (let lst = word_rsplit b in
    parse_single (lst ! 0) (lst ! 1)
   )"

end
