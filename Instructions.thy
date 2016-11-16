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
text {* These instructions are represented by the following bytes.
Most opcodes are a single byte.
*}
declare bits_inst_code.simps [simp]

subsection "Signed Arithmetics"

text {* More similar definitions follow.  Below are instructions for signed arithmetics.
The operations common to signed and unsigned are listed further below in the 
Unsigned Arithmetics section. *}

declare sarith_inst_code.simps [simp]

subsection "Unsigned Arithmetics"

text {* The names GT, EQ and LT are taken in the Cmp library
(which will be used for AVL trees). *} 

declare arith_inst_code.simps [simp]

subsection "Informational Instructions"

declare info_inst_code.simps [simp]

subsection "Duplicating Stack Elements"

text {* There are sixteen instructions for duplicating a stack element.  These instructions take
a stack element and duplicate it on top of the stack. *}

type_synonym dup_inst = nat

declare dup_inst_code_def [simp]

subsection {* Memory Operations *}

declare memory_inst_code.simps [simp]

subsection {* Storage Operations *}

declare storage_inst_code.simps [simp]

subsection {* Program-Counter Instructions *}

text {* If a jump occurs to a location where @{term JUMPDEST} is not found, the execution fails. *}

declare pc_inst_code.simps [simp]

subsection {* Stack Instructions *}
text {* The PUSH instructions have longer byte representations than the other instructions
because they contain immediate values.
Here the immediate value is represented by a list of bytes.  Depending on the
length of the list, the PUSH operation takes different opcodes.
*}

declare stack_inst_code.simps [simp]

declare swap_inst_code_def [simp]
   
subsection {* Logging Instructions *}

text "There are instructions for logging events with different number of arguments."

declare log_inst_code.simps [simp]

subsection {* Miscellaneous Instructions *}

text {* This section contains the instructions that alter the account-wise control flow.
In other words, they cause communication between accounts (or at least interaction with
other accounts' code).
*}

declare misc_inst_code.simps [simp]

subsection {* Annotation Instruction *}

text {* The annotation instruction is just a predicate over @{typ aenv}.
A predicate is modelled as a function returning a boolean.
*}

subsection {* The Whole Instruction Set *}

text {* The small inductive sets above are here combined into a single type. *}

text {* And the byte representation of these instructions are defined. *}

declare inst_code.simps [simp]

text {* The size of an opcode is useful for parsing a hex representation of an
EVM code.  *}

declare inst_size_def [simp]

text {* This can also be used to find jump destinations from a sequence of opcodes.
*}

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
