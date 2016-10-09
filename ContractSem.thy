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
  ContractCall call_arguments
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

(* TODO: keep track of the gas consumption in variable_env *)
definition gas_limit :: "variable_env \<Rightarrow> uint"
where "gas_limit = undefined"
  
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

definition venv_advance_pc :: "variable_env \<Rightarrow> variable_env"
where
"venv_advance_pc v = v\<lparr> venv_prg_sfx := drop_one_element (venv_prg_sfx v)\<rparr>"

    
definition stack_0_0_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stack_0_0_op v c = InstructionContinue (venv_advance_pc v)"

definition stack_0_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> uint \<Rightarrow> instruction_result"
where
"stack_0_1_op v c w =
   InstructionContinue
      (venv_advance_pc v\<lparr>venv_stack := w # venv_stack v\<rparr>)"

definition stack_1_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint) \<Rightarrow> instruction_result"
where
"stack_1_1_op v c f =
   (case venv_stack v of
      [] \<Rightarrow> instruction_failure_result
      | h # t \<Rightarrow>
         InstructionContinue
           (venv_advance_pc v\<lparr>venv_stack := f h # t\<rparr>)
      )"

definition stack_1_2_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint * uint) \<Rightarrow> instruction_result"
where
"stack_1_2_op v c f =
  (case venv_stack v of
     [] \<Rightarrow> instruction_failure_result
   | h # t \<Rightarrow>
     (case f h of
        (new0, new1) \<Rightarrow>
          InstructionContinue
            (venv_advance_pc v\<lparr>venv_stack := new0 # new1 # venv_stack v\<rparr>)))"

definition stack_2_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint \<Rightarrow> uint) \<Rightarrow> instruction_result"
where
"stack_2_1_op v c f =
  (case venv_stack v of
     operand0 # operand1 # rest \<Rightarrow>
       InstructionContinue
         (venv_advance_pc
            v\<lparr>venv_stack := f operand0 operand1 # rest\<rparr>)
  | _ \<Rightarrow> instruction_failure_result
  )"

definition sload :: "variable_env \<Rightarrow> uint \<Rightarrow> uint"
where
"sload v idx = venv_storage v idx"

definition sstore :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sstore v c =
  (case venv_stack v of
    addr # val # stack_tail \<Rightarrow>
      InstructionContinue
      (venv_advance_pc
        (venv_update_storage addr val v\<lparr>venv_stack := stack_tail\<rparr>))
    | _ \<Rightarrow> instruction_failure_result)"

definition jump :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jump v c =
  (case venv_stack_top v of
     None \<Rightarrow> instruction_failure_result
   | Some pos \<Rightarrow>
     (let v_new = venv_change_sfx (Word.unat pos) (venv_pop_stack 1 v) c in
     (case venv_first_instruction v_new of
        Some (Pc JUMPDEST) \<Rightarrow>
          InstructionContinue v_new
      | None \<Rightarrow> instruction_failure_result )))"
      
definition jumpi :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jumpi v c =
  (case venv_stack v of
      pos # cond # rest \<Rightarrow>
        (if cond = 0 then
           InstructionContinue
             (venv_advance_pc (venv_pop_stack 2 v))
         else
           jump (v\<lparr> venv_stack := pos # rest \<rparr>) c)
    | _ \<Rightarrow> instruction_failure_result)"

definition datasize :: "variable_env \<Rightarrow> uint"
where
"datasize v = Word.word_of_int (int (length (venv_data_sent v)))"

definition read_word_from_bytes :: "nat \<Rightarrow> byte list \<Rightarrow> uint"
where
"read_word_from_bytes idx lst =
   Word.word_rcat (take 32 (drop idx lst))"

definition cut_data :: "variable_env \<Rightarrow> uint \<Rightarrow> uint"
where
"cut_data v idx =
    read_word_from_bytes (Word.unat idx) (venv_data_sent v)"

fun cut_memory :: "uint \<Rightarrow> nat \<Rightarrow> (uint \<Rightarrow> byte) \<Rightarrow> byte list"
where
"cut_memory idx 0 memory = []" |
"cut_memory idx (Suc n) memory = 
  memory idx # cut_memory (idx + 1) n memory"
    
definition call :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"call v c =
  (case venv_stack v of
    e0 # e1 # e2 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
    (if venv_balance v (cenv_this c) < e2 then
       instruction_failure_result
     else
       InstructionToWorld
         (ContractCall
           (\<lparr> callarg_gaslimit = e0,
              callarg_code = Word.ucast e1,
              callarg_recipient = Word.ucast e1,
              callarg_value = e2,
              callarg_data = cut_memory e3 (Word.unat e4) (venv_memory v),
              callarg_output_begin = e5,
              callarg_output_size = e6 \<rparr>),
          Some
            (v\<lparr> venv_stack := rest,
               venv_prg_sfx := drop_one_element (venv_prg_sfx v),
               venv_balance :=
                 update_balance (cenv_this c)
                   (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v)\<rparr>
         ))
       )
  | _ \<Rightarrow> instruction_failure_result
  )"
  
definition
"venv_returned_bytes v =
  (case venv_stack v of
    e0 # e1 # _ \<Rightarrow> cut_memory e0 (Word.unat e1) (venv_memory v)
  | _ \<Rightarrow> []
)"

definition ret :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"ret v c = InstructionToWorld ((ContractReturn (venv_returned_bytes v)), None)"

definition stop :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stop v c = InstructionToWorld (ContractReturn [], None)"

definition pop :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"pop v c = InstructionContinue (venv_advance_pc
             v\<lparr>venv_stack := tl (venv_stack v)\<rparr>)"

fun instruction_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> inst \<Rightarrow> instruction_result"
where
"instruction_sem v c (Stack (PUSH_N lst)) =
     stack_0_1_op v c (Word.word_rcat lst)"
| "instruction_sem v c (Unknown _) = InstructionUnknown"
| "instruction_sem v c (Storage SLOAD) = stack_1_1_op v c (sload v)"
| "instruction_sem v c (Storage SSTORE) = sstore v c"
| "instruction_sem v c (Pc JUMPI) = jumpi v c"
| "instruction_sem v c (Pc JUMP) = jump v c"
| "instruction_sem v c (Pc JUMPDEST) = stack_0_0_op v c"
| "instruction_sem v c (Info CALLDATASIZE) = stack_0_1_op v c (datasize v)"
| "instruction_sem v c (Stack CALLDATALOAD) = stack_1_1_op v c (cut_data v)"
| "instruction_sem v c (Info CALLER) = stack_0_1_op v c (Word.ucast (venv_caller v))"
| "instruction_sem v c (Arith ADD) = stack_2_1_op v c (\<lambda> a b. a + b)"
| "instruction_sem v c (Arith SUB) = stack_2_1_op v c (\<lambda> a b. a - b)"
| "instruction_sem v c (Arith ISZERO) = stack_1_1_op v c (\<lambda> a. if a = 0 then 1 else 0)"
| "instruction_sem v c (Misc CALL) = call v c"
| "instruction_sem v c (Misc RETURN) = ret v c"
| "instruction_sem v c (Misc STOP) = stop v c"
| "instruction_sem v c (Dup (Suc 0)) = stack_1_2_op v c (\<lambda> a. (a, a))"
| "instruction_sem v c (Stack POP) = pop v c"
| "instruction_sem v c (Info GASLIMIT) = stack_0_1_op v c (gas_limit v)"
| "instruction_sem v c (Arith GT) = stack_2_1_op v c (\<lambda> a b. if a > b then 1 else 0)"
| "instruction_sem v c (Arith EQ) = stack_2_1_op v c (\<lambda> a b. if a = b then 1 else 0)"

datatype program_result =
  ProgramStepRunOut
| ProgramToWorld "contract_action * storage * (address => uint) * variable_env option"
| ProgramInvalid

fun program_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> nat \<Rightarrow> program_result"
where
  "program_sem v c 0 = ProgramStepRunOut"
| "program_sem v c (Suc remaining_steps) =
    (case venv_prg_sfx v of
      [] \<Rightarrow> ProgramStepRunOut
    | i # _ \<Rightarrow>
      (case instruction_sem v c i of
        InstructionContinue new_v \<Rightarrow>
          program_sem new_v c remaining_steps
      | InstructionToWorld (ContractFail, opt_pushed_v) \<Rightarrow>
        ProgramToWorld (ContractFail, venv_storage_at_call v, venv_balance_at_call v, opt_pushed_v)
      | InstructionToWorld (ContractCall args, Some new_v) \<Rightarrow>
        ProgramToWorld (ContractCall args, venv_storage new_v, venv_balance new_v, Some new_v)
      | InstructionToWorld (a, opt_pushed_v) \<Rightarrow>
        ProgramToWorld (a, venv_storage v, venv_balance v, opt_pushed_v)
      | InstructionUnknown \<Rightarrow> ProgramInvalid
      )
    )"
    
record account_state =
  account_address :: address
  account_storage :: storage
  account_code :: "inst list"
  account_balance :: uint (* TODO: model the fact that this can be
                             increased at any moment *)
                             
(* account_state_update_storage is not particularly useful in
 * Isabelle/HOL where fields of records can be updated. *)

(* Currently it's shown as if the variable_env is determinined by
 * the other arguments but in reality the balance might increase.
 * This mistake will be kept until we try the managed_account_with_accumulated_income_and_spending
 * and we compare Coq and Isabelle/HOL on the same target.
 *)
 
inductive build_venv_called :: "account_state => call_env => variable_env => bool"
where
venv_called:
  "venv_stack venv = [] \<Longrightarrow>
   venv_memory venv = empty_memory \<Longrightarrow>
   venv_prg_sfx venv = account_code a \<Longrightarrow>
   venv_storage venv = account_storage a \<Longrightarrow>
   venv_balance venv = (* replace this with \<le> *)
     update_balance (account_address a)
       (\<lambda> _. account_balance a + callenv_value env)
       (callenv_balance env) \<Longrightarrow>
   venv_caller venv = callenv_caller env \<Longrightarrow>
   venv_value_sent venv = callenv_value env \<Longrightarrow>
   venv_storage_at_call venv = account_storage a \<Longrightarrow>
   venv_balance_at_call venv = venv_balance venv \<Longrightarrow>
   build_venv_called a env venv"
   
definition build_cenv :: "account_state \<Rightarrow> constant_env"
where
"build_cenv a =
  \<lparr> cenv_program = account_code a,
           cenv_this = account_address a \<rparr>"

inductive build_venv_returned :: "account_state \<Rightarrow> return_result \<Rightarrow> variable_env option \<Rightarrow> bool"
where
venv_returned_no_ongoing:
"  account_ongoing_calls a = [] \<Longrightarrow>
   build_venv_returned a r None"
| venv_returned:
"  hd (account_ongoing_calls a) = recovered \<Longrightarrow>
   build_venv_returned a r
     (Some (
              recovered \<lparr>
                venv_stack := 1 # venv_stack recovered
              , venv_storage := account_storage a
              , venv_balance := (update_balance (account_address a)
                                   (\<lambda> _. account_balance a) (return_balance r))
            \<rparr>))"

end
