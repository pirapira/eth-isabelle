section {* Some Data Types for EVM *}

text {* This development depends on Isabelle/HOL's machine word library. *}

theory ContractEnv

imports Main "~~/src/HOL/Word/Word"

begin

text {* Frequently used machine words are named here.  For example, address denotes the type of
160-bit machine words.  The type uint denotes the type of EVM machine words. *}

type_synonym uint = "256 word"
type_synonym address = "160 word"
type_synonym byte = "8 word"

text {* In EVM, the memory contains one byte for each machine word.
The storage contains one machine word for each machine word. *}

type_synonym memory = "uint \<Rightarrow> byte"
type_synonym storage = "uint \<Rightarrow> uint"

text {* The storage is modelled as a function.  For example, the empty storage
is a function that returns zero for every index. *}

definition empty_storage :: storage
where
"empty_storage = (\<lambda> _. 0)"

text {* \noindent During proofs, the definition of @{term empty_storage} is expanded
freely. *}

declare empty_storage_def [simp]

text {* \indent
The following record lists the information available for bytecode-inline assertions.
These assertions will be proved in Isabelle/HOL. *}

(* The environment visible for annotations *)
record aenv =
  aenv_stack :: "uint list"
  aenv_memory :: memory
  aenv_storage :: storage
  aenv_balance :: "address \<Rightarrow> uint"
  aenv_caller :: address
  aenv_value_sent :: uint
  aenv_data_sent :: "byte list"
  aenv_storage_at_call :: storage
  aenv_balance_at_call :: "address \<Rightarrow> uint"
  aenv_this :: address
  aenv_origin :: address

text {* I'm going to add more fields in the @{typ aenv} record. *}
  
end
