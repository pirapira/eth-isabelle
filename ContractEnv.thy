theory ContractEnv

imports Main "~~/src/HOL/Word/Word"

begin

type_synonym uint = "256 word"
type_synonym address = "160 word"
type_synonym byte = "8 word"

type_synonym memory = "uint \<Rightarrow> byte"
type_synonym storage = "uint \<Rightarrow> uint"

record 'a variable_env' =
  venv_stack :: "uint list"
  venv_memory :: memory
  venv_storage :: storage
  venv_prg_sfx :: 'a
  venv_balance :: "address \<Rightarrow> uint"
  venv_caller :: address
  venv_value_sent :: uint
  venv_data_sent :: "byte list"
  venv_storage_at_call :: storage
  venv_balance_at_call :: "address \<Rightarrow> uint"

record 'a constant_env' =
  cenv_program :: 'a
  cenv_this :: address

end
