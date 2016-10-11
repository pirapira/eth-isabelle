theory Instructions

imports Main "~~/src/HOL/Word/Word" "./ContractEnv"

begin

value "3 :: nat"

text "The set of instructions can be defined inductively, or"
text "just as a nibble.  I choose the inductive definition."

type_synonym byte = "8 word"

datatype bits_inst
= inst_AND
| inst_OR
| inst_XOR
| inst_NOT
| BYTE

datatype sarith_inst
= SDIV
| SMOD
| SGT
| SLT
| SIGNEXTEND

datatype arith_inst
= ADD
| MUL
| SUB
| DIV
| MOD
| ADDMOD
| MULMOD
| EXP
| GT
| EQ
| LT
| ISZERO
| SHA3

datatype info_inst =
    ADDRESS
  | BALANCE
  | ORIGIN
  | CALLER
  | CALLVALUE
  | CALLDATASIZE
  | CODESIZE
  | GASPRICE
  | EXTCODESIZE
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | DIFFICULTY
  | GASLIMIT
  | GAS

  type_synonym dup_inst = nat

datatype memory_inst =
    MLOAD
  | MSTORE
  | MSTORE8
  | CALLDATACOPY
  | CODECOPY
  | EXTCODECOPY
  | MSIZE

datatype storage_inst =
    SLOAD
  | SSTORE

datatype pc_inst =
    JUMP
  | JUMPI
  | PC
  | JUMPDEST
  
datatype stack_inst =
  POP
  | PUSH_N "8 word list"
  | CALLDATALOAD


type_synonym swap_inst = nat

datatype log_inst
  = LOG0
  | LOG1
  | LOG2
  | LOG3
  | LOG4

datatype misc_inst
  = STOP
  | CREATE
  | CALL
  | CALLCODE
  | RETURN
  | SUICIDE

type_synonym annotation = "aenv \<Rightarrow> bool"

datatype inst =
    Unknown byte
  | Bits bits_inst
  | Sarith sarith_inst
  | Arith arith_inst
  | Info info_inst
  | Dup dup_inst
  | Memory memory_inst
  | Storage storage_inst
  | Pc pc_inst
  | Stack stack_inst
  | Swap swap_inst
  | Log log_inst
  | Misc misc_inst
  | Annotation annotation

value "Misc STOP"

end
