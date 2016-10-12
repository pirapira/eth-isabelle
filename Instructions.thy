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

fun bits_inst_code :: "bits_inst \<Rightarrow> byte"
where
  "bits_inst_code inst_AND = 0x16"
| "bits_inst_code inst_OR = 0x17"
| "bits_inst_code inst_XOR = 0x18"
| "bits_inst_code inst_NOT = 0x18"
| "bits_inst_code BYTE = 0x1a"

declare bits_inst_code.simps [simp]

datatype sarith_inst
= SDIV
| SMOD
| SGT
| SLT
| SIGNEXTEND

fun sarith_inst_code :: "sarith_inst => byte"
where
  "sarith_inst_code SDIV = 0x05"
| "sarith_inst_code SMOD = 0x07"
| "sarith_inst_code SGT = 0x13"
| "sarith_inst_code SLT = 0x12"
| "sarith_inst_code SIGNEXTEND = 0x0b"

declare sarith_inst_code.simps [simp]

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

fun arith_inst_code :: "arith_inst \<Rightarrow> byte"
where
  "arith_inst_code ADD = 0x01"
| "arith_inst_code MUL = 0x02"
| "arith_inst_code SUB = 0x03"
| "arith_inst_code DIV = 0x04"
| "arith_inst_code MOD = 0x06"
| "arith_inst_code ADDMOD = 0x08"
| "arith_inst_code MULMOD = 0x09"
| "arith_inst_code EXP = 0x0a"
| "arith_inst_code GT = 0x11"
| "arith_inst_code LT = 0x10"
| "arith_inst_code EQ = 0x14"
| "arith_inst_code ISZERO = 0x15"
| "arith_inst_code SHA3 = 0x20"

declare arith_inst_code.simps [simp]

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
  
fun info_inst_code :: "info_inst \<Rightarrow> byte"
where
  "info_inst_code ADDRESS = 0x30"
| "info_inst_code BALANCE = 0x31"
| "info_inst_code ORIGIN = 0x32"
| "info_inst_code CALLVALUE = 0x34"
| "info_inst_code CALLDATASIZE = 0x36"
| "info_inst_code CALLER = 0x33"
| "info_inst_code CODESIZE = 0x38"
| "info_inst_code GASPRICE = 0x3a"
| "info_inst_code EXTCODESIZE = 0x3b"
| "info_inst_code BLOCKHASH = 0x40"
| "info_inst_code COINBASE = 0x41"
| "info_inst_code TIMESTAMP = 0x42"
| "info_inst_code NUMBER = 0x43"
| "info_inst_code DIFFICULTY = 0x44"
| "info_inst_code GASLIMIT = 0x45"
| "info_inst_code GAS = 0x5a"

declare info_inst_code.simps [simp]

type_synonym dup_inst = nat

abbreviation dup_inst_code :: "dup_inst \<Rightarrow> byte"
where
"dup_inst_code n ==
   (if n < 1 then undefined
    else (if n > 16 then undefined
    else (word_of_int (int n)) + 0x79))"

datatype memory_inst =
    MLOAD
  | MSTORE
  | MSTORE8
  | CALLDATACOPY
  | CODECOPY
  | EXTCODECOPY
  | MSIZE

fun memory_inst_code :: "memory_inst \<Rightarrow> byte"
where
  "memory_inst_code MLOAD = 0x51"
| "memory_inst_code MSTORE = 0x52"
| "memory_inst_code MSTORE8 = 0x53"
| "memory_inst_code CALLDATACOPY = 0x37"
| "memory_inst_code CODECOPY = 0x39"
| "memory_inst_code EXTCODECOPY = 0x3c"
| "memory_inst_code MSIZE = 0x59"

declare memory_inst_code.simps [simp]

datatype storage_inst =
    SLOAD
  | SSTORE

fun storage_inst_code :: "storage_inst \<Rightarrow> byte"
where
  "storage_inst_code SLOAD = 0x54"
| "storage_inst_code SSTORE = 0x55"

declare storage_inst_code.simps [simp]

datatype pc_inst =
    JUMP
  | JUMPI
  | PC
  | JUMPDEST

fun pc_inst_code :: "pc_inst \<Rightarrow> byte"
where
  "pc_inst_code JUMP = 0x56"
| "pc_inst_code JUMPI = 0x57"
| "pc_inst_code PC = 0x58"
| "pc_inst_code JUMPDEST = 0x5b"

declare pc_inst_code.simps [simp]
  
datatype stack_inst =
    POP
  | PUSH_N "8 word list"
  | CALLDATALOAD

fun stack_inst_code :: "stack_inst \<Rightarrow> byte list"
where
  "stack_inst_code POP = [0x50]"
| "stack_inst_code (PUSH_N lst) =
     (if (size lst) < 1 then undefined
      else (if (size lst) > 32 then undefined
      else word_of_int (int (size lst)) + 0x59)) # lst"
| "stack_inst_code CALLDATALOAD = [0x35]"

declare stack_inst_code.simps [simp]

type_synonym swap_inst = nat

abbreviation swap_inst_code :: "swap_inst \<Rightarrow> byte"
where
"swap_inst_code n ==
  (if n < 1 then undefined else
  (if n > 16 then undefined else
   word_of_int (int n) + 0x89))"

datatype log_inst
  = LOG0
  | LOG1
  | LOG2
  | LOG3
  | LOG4

fun log_inst_code :: "log_inst \<Rightarrow> byte"
where
  "log_inst_code LOG0 = 0xa0"
| "log_inst_code LOG1 = 0xa1"
| "log_inst_code LOG2 = 0xa2"
| "log_inst_code LOG3 = 0xa3"
| "log_inst_code LOG4 = 0xa4"

declare log_inst_code.simps [simp]

datatype misc_inst
  = STOP
  | CREATE
  | CALL
  | CALLCODE
  | DELEGATECALL
  | RETURN
  | SUICIDE

fun misc_inst_code :: "misc_inst \<Rightarrow> byte"
where
  "misc_inst_code STOP = 0x0"
| "misc_inst_code CREATE = 0xf0"
| "misc_inst_code CALL = 0xf1"
| "misc_inst_code CALLCODE = 0xf2"
| "misc_inst_code RETURN = 0xf3"
| "misc_inst_code DELEGATECALL = 0xf4"
| "misc_inst_code SUICIDE = 0xff"

declare misc_inst_code.simps [simp]

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

fun inst_code :: "inst \<Rightarrow> byte list"
where
  "inst_code (Unknown byte) = [byte]"
| "inst_code (Bits b) = [bits_inst_code b]"
| "inst_code (Sarith s) = [sarith_inst_code s]"
| "inst_code (Arith a) = [arith_inst_code a]"
| "inst_code (Info i) = [info_inst_code i]"
| "inst_code (Dup d) = [dup_inst_code d]"
| "inst_code (Memory m) = [memory_inst_code m]"
| "inst_code (Storage s) = [storage_inst_code s]"
| "inst_code (Pc p) = [pc_inst_code p]"
| "inst_code (Stack s) = stack_inst_code s"
| "inst_code (Swap s) = [swap_inst_code s]"
| "inst_code (Log l) = [log_inst_code l]"
| "inst_code (Misc m) = [misc_inst_code m]"
| "inst_code (Annotation _) = []"

declare inst_code.simps [simp]

value "Misc STOP"

type_synonym program = "inst list"

fun drop_bytes :: "program \<Rightarrow> nat \<Rightarrow> program"
where
  "drop_bytes prg 0 = prg"
| "drop_bytes (Stack (PUSH_N v) # rest) bytes = drop_bytes rest (bytes - 1 - length v)"
| "drop_bytes (Annotation _ # rest) bytes = drop_bytes rest bytes"
| "drop_bytes (_ # rest) bytes = drop_bytes rest (bytes - 1)"
| "drop_bytes [] (Suc v) = []"

declare drop_bytes.simps [simp]

fun program_size :: "program \<Rightarrow> nat"
where
  "program_size (Stack (PUSH_N v) # rest) = length v + 1 + program_size rest"
| "program_size (Annotation _ # rest) = program_size rest"
| "program_size (_ # rest) = 1 + program_size rest"
| "program_size [] = 0"

declare program_size.simps [simp]


fun program_code :: "program \<Rightarrow> byte list"
where
  "program_code [] = []"
| "program_code (inst # rest) =
   inst_code inst @ program_code rest"

declare program_code.simps [simp]

end
