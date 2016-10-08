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

fun drop_bytes :: "program \<Rightarrow> nat \<Rightarrow> program"
where
  "drop_bytes prg 0 = prg"
| "drop_bytes (Stack (PUSH_N v) # rest) bytes = drop_bytes rest (bytes - 1 - length v)"
| "drop_bytes (_ # rest) bytes = drop_bytes rest (bytes - 1)"
| "drop_bytes [] (Suc v) = []"

type_synonym memory = "uint \<Rightarrow> byte"
definition empty_memory :: memory
where
"empty_memory _ = 0"

type_synonym storage = "uint \<Rightarrow> uint"

record variable_env =
  venv_stack :: "uint list"
  venv_memory :: memory
  venv_storage :: storage
  venv_prg_sfx :: program
  venv_balance :: "address \<Rightarrow> uint"
  venv_caller :: address
  venv_value_sent :: uint
  venv_data_sent :: "byte list"
  venv_storage_at_call :: storage
  venv_balance_at_call :: "address \<Rightarrow> uint"
  
definition update_balance :: "address \<Rightarrow> (uint \<Rightarrow> uint) \<Rightarrow> (address \<Rightarrow> uint) \<Rightarrow> (address \<Rightarrow> uint)"
where
"update_balance a newbal orig = orig(a := newbal (orig a))"

record constant_env =
  cenv_program :: program
  cenv_this :: address

definition init_variable_env ::
  "storage \<Rightarrow> (address \<Rightarrow> uint) \<Rightarrow> address \<Rightarrow> constant_env \<Rightarrow> uint \<Rightarrow> byte list \<Rightarrow> variable_env"
where
  "init_variable_env s bal caller cenv value data =
     \<lparr> venv_stack = []
     , venv_memory = empty_memory
     , venv_storage = s
     , venv_prg_sfx = cenv_program cenv
     , venv_balance = bal
     , venv_caller = caller
     , venv_value_sent = value
     , venv_data_sent = data
     , venv_storage_at_call = s
     , venv_balance_at_call = bal
     \<rparr>
  "

datatype instruction_result =
  InstructionUnknown (* should be removed at one point *) 
| InstructionContinue variable_env
| InstructionToWorld "contract_action * variable_env option"

definition instruction_failure_result :: instruction_result
where
"instruction_failure_result = InstructionToWorld (ContractFail, None)"

definition instruction_return_result :: "byte list \<Rightarrow> instruction_result"
where
"instruction_return_result x = InstructionToWorld (ContractReturn x, None)"

(* venv_update_x functions are not useful in Isabelle/HOL,
 * where field updates are supported already. *)
 
fun venv_pop_stack :: "nat \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
  "venv_pop_stack 0 v = v"
| "venv_pop_stack (Suc n) v =
   v\<lparr> venv_stack := tl (venv_stack v)\<rparr>"
   
definition venv_stack_top :: "variable_env \<Rightarrow> uint option"
where
"venv_stack_top v =
  (case venv_stack v of
     h # _\<Rightarrow> Some h
   | [] \<Rightarrow> None)"

definition venv_change_sfx :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> variable_env"
where
"venv_change_sfx pos v c =
   v\<lparr>
     venv_prg_sfx := drop_bytes (cenv_program c) pos
   \<rparr>"

(* function_update is already provided in Main library *)

definition venv_update_storage :: "uint \<Rightarrow> uint \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
"venv_update_storage idx val v =
  v\<lparr>venv_storage := (venv_storage v)(idx := val)\<rparr>"

definition venv_first_instruction :: "variable_env \<Rightarrow> inst option"
where
"venv_first_instruction v =
   (case venv_prg_sfx v of
      [] \<Rightarrow> None
    | h # _ \<Rightarrow> Some h)"



end
