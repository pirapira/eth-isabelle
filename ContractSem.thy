text "This is a port of ContractSem.v in pirapira/evmverif"

text "The main difficulty is to avoid the use of coinduction"

text "One way is, in the specification, talk about some concrete state."
text "Maybe that's fine."

theory ContractSem

imports Main "~~/src/HOL/Word/Word" "./Instructions"

begin

type_synonym uint = "256 word"
type_synonym address = "160 word"
type_synonym byte = "8 word"

definition bool_to_uint :: "bool \<Rightarrow> uint"
where
"bool_to_uint b = (if b then 1 else 0)"

definition "drop_one_element = tl"

record call_arguments =
  callarg_gaslimit :: uint
  callarg_code :: address
  callarg_recipient :: address
  callarg_value :: uint
  callarg_data :: "byte list"
  callarg_output_begin :: uint
  callarg_output_size :: uint
  
record return_result =
  return_data :: "byte list"
  return_balance :: "address \<Rightarrow> uint"
  
record call_env =
  callenv_gaslimit :: uint
  callenv_value :: uint
  callenv_data :: "byte list"
  callenv_caller :: address
  callenv_timestamp :: uint
  callenv_blocknum :: uint
  callenv_balane :: "address \<Rightarrow> uint"
  
datatype contract_action =
  ContratCall call_arguments
| ContractFail
| ContractSuicide
| ContractReturn "byte list"

text "response_to_world is not ported"
text "We will be checking the resulting state"

datatype world_action =
  WorldCall call_env
| WorldRet return_result
| WorldFail

type_synonym world = "world_action list"

datatype action =
  ActionByWorld world_action
| ActionByContract contract_action

type_synonym history = "action list"

type_synonym program = "inst list"



end
