(*
   Copyright 2016 Yoichi Hirai

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

section {* EVM Instructions *}

text {* This section lists the EVM instructions and their byte representations.
I also introduce an assertion instruction, whose byte representation is empty.
The assertion instruction is a statement about the state of the EVM at
that position of the program.
*}

text {* In Isabelle/HOL, it is expensive to define a single inductive type
that contains all instructions.  When I do it, Isabelle/HOL automatically proves every
instruction is different from any other instruction, but this process has the computational
complexity of the square of the number of instructions.  Instead, I define multiple
smaller inductive types and unify them at the end.  *}

theory Instructions

imports Main "~~/src/HOL/Word/Word" "./ContractEnv" "./lem/Evm"

begin

subsection "Bit Operations"

text {* The following clause defines a type called \textit{bits\_inst}.
The type has five elements.  It is automatically understood that nothing else
belongs to this type.  It is also understood that every one of these five elements
is different from any of the other four.
*}

text {* Some instructions have \textit{inst\_} in front because names like AND,
OR and XOR are taken by the machine word library.
*}

text {* The instructions have different arities.  They might consume some elements on the stack,
and produce some elements on the stack.  However, the arity of the instructions are not specified
in this section. *}
(*
datatype bits_inst
= inst_AND -- {* bitwise AND *}
| inst_OR  -- {* bitwise OR *}
| inst_XOR -- {* bitwise exclusive or *}
| inst_NOT -- {* bitwise negation *}
| BYTE     -- {* taking one byte out of a word *}
*)
text {* These instructions are represented by the following bytes.
Most opcodes are a single byte.
*}
(*
fun bits_inst_code :: "bits_inst \<Rightarrow> byte"
where
  "bits_inst_code inst_AND = 0x16"
| "bits_inst_code inst_OR = 0x17"
| "bits_inst_code inst_XOR = 0x18"
| "bits_inst_code inst_NOT = 0x19"
| "bits_inst_code BYTE = 0x1a"
*)
declare bits_inst_code.simps [simp]

subsection "Signed Arithmetics"

text {* More similar definitions follow.  Below are instructions for signed arithmetics.
The operations common to signed and unsigned are listed further below in the 
Unsigned Arithmetics section. *}
(*
datatype sarith_inst
= SDIV -- {* signed division *}
| SMOD -- {* signed modulo *}
| SGT  -- {* signed greater-than *}
| SLT  -- {* signed less-than *}
| SIGNEXTEND -- {* extend the size of a signed number *}

fun sarith_inst_code :: "sarith_inst => byte"
where
  "sarith_inst_code SDIV = 0x05"
| "sarith_inst_code SMOD = 0x07"
| "sarith_inst_code SGT = 0x13"
| "sarith_inst_code SLT = 0x12"
| "sarith_inst_code SIGNEXTEND = 0x0b"*)

declare sarith_inst_code.simps [simp]

subsection "Unsigned Arithmetics"

text {* The names GT, EQ and LT are taken in the Cmp library
(which will be used for AVL trees). *} 
(*
datatype arith_inst
= ADD -- {* addition *}
| MUL -- {* multiplication *}
| SUB -- {* subtraction *} 
| DIV -- {* unsigned division *}
| MOD -- {* unsigned modulo *}
| ADDMOD -- {* addition under modulo *}
| MULMOD -- {* multiplication under modulo *}
| EXP -- {* exponentiation *}
| inst_GT -- {* unsigned greater-than *}
| inst_EQ -- {* equality *}
| inst_LT -- {* unsigned less-than *}
| ISZERO -- {* if zero, returns one *}
| SHA3 -- {* Keccak 256, dispite the name *}

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
| "arith_inst_code inst_GT = 0x11"
| "arith_inst_code inst_LT = 0x10"
| "arith_inst_code inst_EQ = 0x14"
| "arith_inst_code ISZERO = 0x15"
| "arith_inst_code SHA3 = 0x20"*)

declare arith_inst_code.simps [simp]

subsection "Informational Instructions"
(*
datatype info_inst =
    ADDRESS -- {* the address of the account currently running *}
  | BALANCE -- {* the Eth balance of the specified account *}
  | ORIGIN -- {* the address of the external account that started the transaction *}
  | CALLER -- {* the immediate caller of this invocation *}
  | CALLVALUE -- {* the Eth amount sent along this invocation *}
  | CALLDATASIZE -- {* The number of bytes sent along this invocation *}
  | CODESIZE -- {* the number of bytes in the currently running code *}
  | GASPRICE -- {* the current gas price *}
  | EXTCODESIZE -- {* the size of the code on the specified account *}
  | BLOCKHASH -- {* the block hash of a specified block among the recent blocks *}
  | COINBASE -- {* the address of the miner that validates the current block *}
  | TIMESTAMP -- {* the date and time of the block *}
  | NUMBER -- {* the block number *}
  | DIFFICULTY -- {* the current difficulty *}
  | GASLIMIT -- {* the current block gas limit *}
  | GAS -- {* the remaining gas for the current execution.  *}
  
  *)
(*
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
| "info_inst_code GAS = 0x5a"*)

declare info_inst_code.simps [simp]

subsection "Duplicating Stack Elements"

text {* There are sixteen instructions for duplicating a stack element.  These instructions take
a stack element and duplicate it on top of the stack. *}

type_synonym dup_inst = nat
(*
abbreviation dup_inst_code :: "dup_inst \<Rightarrow> byte"
where
"dup_inst_code n \<equiv>
   (if n < 1 then undefined (* There is no DUP0 instruction. *)
    else (if n > 16 then undefined (* There are no DUP16 instruction and on. *)
    else (word_of_int (int n)) + 0x7f))"
-- {* 0x80 stands for DUP1 until 0x9f for DUP16. *}
*)

declare dup_inst_code_def [simp]

subsection {* Memory Operations *}
(*
datatype memory_inst =
    MLOAD -- {* reading one word from the memory from the specified offset *}
  | MSTORE -- {* writing one machine word to the memory *}
  | MSTORE8 -- {* writing one byte to the memory *}
  | CALLDATACOPY -- {* copying the caller's data to the memory *}
  | CODECOPY -- {* copying a part of the currently running code to the memory *}
  | EXTCODECOPY -- {* copying a part of the code of the specified account *}
  | MSIZE -- {* the size of the currently used region of the memory. *}

fun memory_inst_code :: "memory_inst \<Rightarrow> byte"
where
  "memory_inst_code MLOAD = 0x51"
| "memory_inst_code MSTORE = 0x52"
| "memory_inst_code MSTORE8 = 0x53"
| "memory_inst_code CALLDATACOPY = 0x37"
| "memory_inst_code CODECOPY = 0x39"
| "memory_inst_code EXTCODECOPY = 0x3c"
| "memory_inst_code MSIZE = 0x59"
*)

declare memory_inst_code.simps [simp]

subsection {* Storage Operations *}

(*
datatype storage_inst =
    SLOAD -- {* reading one word from the storage *}
  | SSTORE -- {* writing one word to the storage. *}
  *)

  (*
fun storage_inst_code :: "storage_inst \<Rightarrow> byte"
where
  "storage_inst_code SLOAD = 0x54"
| "storage_inst_code SSTORE = 0x55"
*)

declare storage_inst_code.simps [simp]

subsection {* Program-Counter Instructions *}

(*
datatype pc_inst =
    JUMP -- {* jumping to the specified location in the code *}
  | JUMPI -- {* jumping to the specified location in the code if a condition is met *}
  | PC -- {* the current location in the code *}
  | JUMPDEST -- {* a no-op instruction located to indicate jump destinations. *}
  
  *)

text {* If a jump occurs to a location where @{term JUMPDEST} is not found, the execution fails.
*}

(*
fun pc_inst_code :: "pc_inst \<Rightarrow> byte"
where
  "pc_inst_code JUMP = 0x56"
| "pc_inst_code JUMPI = 0x57"
| "pc_inst_code PC = 0x58"
| "pc_inst_code JUMPDEST = 0x5b"
*)
declare pc_inst_code.simps [simp]

subsection {* Stack Instructions *}
(*
datatype stack_inst =
    POP -- {* throwing away the topmost element of the stack *}
  | PUSH_N "8 word list" -- {* pushing an element to the stack *}
  | CALLDATALOAD -- {* pushing a word to the stack, taken from the caller's data. *}
  *)

text {* The PUSH instructions have longer byte representations than the other instructions
because they contain immediate values.
Here the immediate value is represented by a list of bytes.  Depending on the
length of the list, the PUSH operation takes different opcodes.
*}

(*  
fun stack_inst_code :: "stack_inst \<Rightarrow> byte list"
where
  "stack_inst_code POP = [0x50]"
| "stack_inst_code (PUSH_N lst) =
   (if (size lst) < 1 then undefined (* there is no PUSH0 instruction *)
    else (if (size lst) > 32 then undefined (* there are no PUSH33 and so on *)
    else word_of_int (int (size lst)) + 0x5f)) # lst" (* 0x60 is PUSH1, ..., 0x7f is PUSH32 *)
| "stack_inst_code CALLDATALOAD = [0x35]"
*)

declare stack_inst_code.simps [simp]

type_synonym swap_inst = nat

(*abbreviation swap_inst_code :: "swap_inst \<Rightarrow> byte"
where
"swap_inst_code n \<equiv>
  (if n < 1 then undefined else   (* there is no SWAP0 *)
  (if n > 16 then undefined else  (* there are no SWAP17 and on *)
   word_of_int (int n) + 0x8f))"  (* 0x90 is SWAP1, ..., 0x9f is SWAP16 *)
   *)

declare swap_inst_code_def [simp]
   
subsection {* Logging Instructions *}

text "There are instructions for logging events with different number of arguments."
(*
datatype log_inst = LOG0 | LOG1 | LOG2 | LOG3 | LOG4

fun log_inst_code :: "log_inst \<Rightarrow> byte"
where
  "log_inst_code LOG0 = 0xa0"
| "log_inst_code LOG1 = 0xa1"
| "log_inst_code LOG2 = 0xa2"
| "log_inst_code LOG3 = 0xa3"
| "log_inst_code LOG4 = 0xa4"
*)

declare log_inst_code.simps [simp]

subsection {* Miscellaneous Instructions *}

text {* This section contains the instructions that alter the account-wise control flow.
In other words, they cause communication between accounts (or at least interaction with
other accounts' code).
*}
(*
datatype misc_inst
  = STOP -- {* finishing the execution normally, with the empty return data *}
  | CREATE -- {* deploying some code in an account *}
  | CALL -- {* calling (i.e. sending a message to) an account *}
  | CALLCODE -- {* calling into the current account with some other account's code *}
  | DELEGATECALL
  -- {* calling into this account, the executed code can be some other account's
                       but the sent value and the sent data are unchanged. *}
  | RETURN -- {* finishing the execution normally with data *}
  | SUICIDE
  -- {* send all remaining Eth balance to the specified account,
        finishing the execution normally, and flagging the current account for deletion. *}

fun misc_inst_code :: "misc_inst \<Rightarrow> byte"
where
  "misc_inst_code STOP = 0x00"
| "misc_inst_code CREATE = 0xf0"
| "misc_inst_code CALL = 0xf1"
| "misc_inst_code CALLCODE = 0xf2"
| "misc_inst_code RETURN = 0xf3"
| "misc_inst_code DELEGATECALL = 0xf4"
| "misc_inst_code SUICIDE = 0xff"
*)

declare misc_inst_code.simps [simp]

subsection {* Annotation Instruction *}

text {* The annotation instruction is just a predicate over @{typ aenv}.
A predicate is modelled as a function returning a boolean.
*}

type_synonym annotation = "aenv \<Rightarrow> bool"

subsection {* The Whole Instruction Set *}

text {* The small inductive sets above are here combined into a single type. *}

(*
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
  *)

text {* And the byte representation of these instructions are defined. *}

(*
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
*)

declare inst_code.simps [simp]

text {* The size of an opcode is useful for parsing a hex representation of an
EVM code.  *}

(*
abbreviation inst_size :: "inst \<Rightarrow> int"
where
"inst_size i \<equiv> int (length (inst_code i))"
*)

declare inst_size_def [simp]

text {* This can also be used to find jump destinations from a sequence of opcodes.
*}
(*
fun drop_bytes :: "inst list \<Rightarrow> nat \<Rightarrow> inst list"
where
  "drop_bytes prg 0 = prg"
| "drop_bytes (Stack (PUSH_N v) # rest) bytes =
    drop_bytes rest (bytes - 1 - length v)"
| "drop_bytes (Annotation _ # rest) bytes = drop_bytes rest bytes"
| "drop_bytes (_ # rest) bytes = drop_bytes rest (bytes - 1)"
| "drop_bytes [] (Suc v) = []"
*)

declare drop_bytes.simps [simp]

text {* Also it is possible to compute the size of a program as the number of bytes, *}

fun program_size :: "inst list \<Rightarrow> nat"
where
  "program_size (Stack (PUSH_N v) # rest) = length v + 1 + program_size rest"
  -- {* I was using @{term inst_size} here, but that contributed to performance problems. *}
| "program_size (Annotation _ # rest) = program_size rest"
| "program_size (_ # rest) = 1 + program_size rest"
| "program_size [] = 0"

declare program_size.simps [simp]

text {* as well as computing the byte representation of the program. *}

fun program_code :: "inst list \<Rightarrow> byte list"
where
  "program_code [] = []"
| "program_code (inst # rest) = inst_code inst @ program_code rest"

declare program_code.simps [simp]

end
