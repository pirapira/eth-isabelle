theory ContractEnv

imports Main "~~/src/HOL/Word/Word"

begin

type_synonym uint = "256 word"
type_synonym address = "160 word"
type_synonym byte = "8 word"

type_synonym memory = "uint \<Rightarrow> byte"
type_synonym storage = "uint \<Rightarrow> uint"

definition empty_storage :: storage
where
"empty_storage = (\<lambda> _. 0)"

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

end
