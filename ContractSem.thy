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

abbreviation "drop_one_element == tl"

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

declare drop_bytes.simps [simp]

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

abbreviation instruction_failure_result :: instruction_result
where
"instruction_failure_result == InstructionToWorld (ContractFail, None)"

abbreviation instruction_return_result :: "byte list \<Rightarrow> instruction_result"
where
"instruction_return_result x == InstructionToWorld (ContractReturn x, None)"

(* venv_update_x functions are not useful in Isabelle/HOL,
 * where field updates are supported already. *)
 
fun venv_pop_stack :: "nat \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
  "venv_pop_stack 0 v = v"
| "venv_pop_stack (Suc n) v =
   v\<lparr> venv_stack := tl (venv_stack v)\<rparr>"

abbreviation venv_stack_top :: "variable_env \<Rightarrow> uint option"
where
"venv_stack_top v ==
  (case venv_stack v of
     h # _\<Rightarrow> Some h
   | [] \<Rightarrow> None)"

abbreviation venv_change_sfx :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> variable_env"
where
"venv_change_sfx pos v c ==
   v\<lparr>
     venv_prg_sfx := drop_bytes (cenv_program c) pos
   \<rparr>"

(* function_update is already provided in Main library *)

abbreviation venv_update_storage :: "uint \<Rightarrow> uint \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
"venv_update_storage idx val v ==
  v\<lparr>venv_storage := (venv_storage v)(idx := val)\<rparr>"

abbreviation venv_first_instruction :: "variable_env \<Rightarrow> inst option"
where
"venv_first_instruction v ==
   (case venv_prg_sfx v of
      [] \<Rightarrow> None
    | h # _ \<Rightarrow> Some h)"

abbreviation venv_advance_pc :: "variable_env \<Rightarrow> variable_env"
where
"venv_advance_pc v \<equiv> v\<lparr> venv_prg_sfx := drop_one_element (venv_prg_sfx v)\<rparr>"

    
abbreviation stack_0_0_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stack_0_0_op v c == InstructionContinue (venv_advance_pc v)"

abbreviation stack_0_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> uint \<Rightarrow> instruction_result"
where
"stack_0_1_op v c w ==
   InstructionContinue
      (venv_advance_pc v\<lparr>venv_stack := w # venv_stack v\<rparr>)"

abbreviation stack_1_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint) \<Rightarrow> instruction_result"
where
"stack_1_1_op v c f \<equiv>
   (case venv_stack v of
      [] \<Rightarrow> instruction_failure_result
      | h # t \<Rightarrow>
         InstructionContinue
           (venv_advance_pc v\<lparr>venv_stack := f h # t\<rparr>)
      )"

abbreviation stack_1_2_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint * uint) \<Rightarrow> instruction_result"
where
"stack_1_2_op v c f ==
  (case venv_stack v of
     [] \<Rightarrow> instruction_failure_result
   | h # t \<Rightarrow>
     (case f h of
        (new0, new1) \<Rightarrow>
          InstructionContinue
            (venv_advance_pc v\<lparr>venv_stack := new0 # new1 # venv_stack v\<rparr>)))"

abbreviation stack_2_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint \<Rightarrow> uint) \<Rightarrow> instruction_result"
where
"stack_2_1_op v c f \<equiv>
  (case venv_stack v of
     operand0 # operand1 # rest \<Rightarrow>
       InstructionContinue
         (venv_advance_pc
            v\<lparr>venv_stack := f operand0 operand1 # rest\<rparr>)
  | _ \<Rightarrow> instruction_failure_result
  )"

abbreviation sload :: "variable_env \<Rightarrow> uint \<Rightarrow> uint"
where
"sload v idx == venv_storage v idx"

abbreviation sstore :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sstore v c ==
  (case venv_stack v of
    addr # val # stack_tail \<Rightarrow>
      InstructionContinue
      (venv_advance_pc
        (venv_update_storage addr val v\<lparr>venv_stack := stack_tail\<rparr>))
    | _ \<Rightarrow> instruction_failure_result)"

abbreviation jump :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jump v c \<equiv>
  (case venv_stack_top v of
     None \<Rightarrow> instruction_failure_result
   | Some pos \<Rightarrow>
     (let v_new = venv_change_sfx (Word.unat pos) (venv_pop_stack 1 v) c in
     (case venv_first_instruction v_new of
        Some (Pc JUMPDEST) \<Rightarrow>
          InstructionContinue v_new
      | Some _ \<Rightarrow> instruction_failure_result
      | None \<Rightarrow> instruction_failure_result )))"
      
abbreviation jumpi :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jumpi v c ==
  (case venv_stack v of
      pos # cond # rest \<Rightarrow>
        (if cond = 0 then
           InstructionContinue
             (venv_advance_pc (venv_pop_stack 2 v))
         else
           jump (v\<lparr> venv_stack := pos # rest \<rparr>) c)
    | _ \<Rightarrow> instruction_failure_result)"

abbreviation datasize :: "variable_env \<Rightarrow> uint"
where
"datasize v == Word.word_of_int (int (length (venv_data_sent v)))"

abbreviation read_word_from_bytes :: "nat \<Rightarrow> byte list \<Rightarrow> uint"
where
"read_word_from_bytes idx lst ==
   Word.word_rcat (take 32 (drop idx lst))"

abbreviation cut_data :: "variable_env \<Rightarrow> uint \<Rightarrow> uint"
where
"cut_data v idx ==
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

declare call_def [simp]

definition
"venv_returned_bytes v =
  (case venv_stack v of
    e0 # e1 # _ \<Rightarrow> cut_memory e0 (Word.unat e1) (venv_memory v)
  | _ \<Rightarrow> []
)"

abbreviation ret :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"ret v c \<equiv> InstructionToWorld ((ContractReturn (venv_returned_bytes v)), None)"

abbreviation stop :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stop v c \<equiv> InstructionToWorld (ContractReturn [], None)"

abbreviation pop :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"pop v c \<equiv> InstructionContinue (venv_advance_pc
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
  account_ongoing_calls :: "variable_env list"

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
   venv_balance venv \<ge>
     update_balance (account_address a)
       (\<lambda> _. account_balance a + callenv_value env)
       (callenv_balance env) \<Longrightarrow>
   venv_caller venv = callenv_caller env \<Longrightarrow>
   venv_value_sent venv = callenv_value env \<Longrightarrow>
   venv_storage_at_call venv = account_storage a \<Longrightarrow>
   venv_balance_at_call venv = venv_balance venv \<Longrightarrow>
   build_venv_called a env venv"
   
declare build_venv_called.simps [simp]
   
abbreviation build_cenv :: "account_state \<Rightarrow> constant_env"
where
"build_cenv a \<equiv>
  \<lparr> cenv_program = account_code a,
           cenv_this = account_address a \<rparr>"

inductive build_venv_returned :: "account_state \<Rightarrow> return_result \<Rightarrow> variable_env option \<Rightarrow> bool"
where
venv_returned_no_ongoing:
"  account_ongoing_calls a = [] \<Longrightarrow>
   build_venv_returned a r None"
| venv_returned:
"  account_ongoing_calls a = recovered # _ \<Longrightarrow>
   new_bal \<ge> account_balance a \<Longrightarrow>
   build_venv_returned a r
     (Some (
              recovered \<lparr>
                venv_stack := 1 # venv_stack recovered
              , venv_storage := account_storage a
              , venv_balance := (update_balance (account_address a)
                                   (\<lambda> _. new_bal) (return_balance r))
            \<rparr>))"
(* declare build_venv_returned.simps [simp] *)

definition build_venv_fail :: "account_state \<Rightarrow> variable_env option"
where
"build_venv_fail a =
  (case account_ongoing_calls a of
     [] \<Rightarrow> None
   | recovered # _ \<Rightarrow>
      Some (recovered \<lparr>venv_stack := 0 # venv_stack recovered\<rparr>)
  )"

declare build_venv_fail_def [simp]


abbreviation account_state_pop_ongoing_call :: "account_state \<Rightarrow> account_state"
where
"account_state_pop_ongoing_call orig ==
   orig\<lparr> account_ongoing_calls := tl (account_ongoing_calls orig)\<rparr>"
 
abbreviation update_account_state :: "account_state \<Rightarrow> contract_action \<Rightarrow> storage \<Rightarrow> (address \<Rightarrow> uint) \<Rightarrow> variable_env option \<Rightarrow> account_state"
where
"update_account_state prev act st bal v_opt \<equiv>
  (case v_opt of
    None \<Rightarrow>
      prev\<lparr>
        account_storage := st \<rparr>
  | Some pushed \<Rightarrow>
      prev\<lparr>
        account_storage := st,
        account_balance := bal (account_address prev),
        account_ongoing_calls := pushed # (account_ongoing_calls prev)
      \<rparr>
  )
"

(* Replace the coinductional future of the 
 * contract_behavior with just a condition on
 * the resulting account_state *)

type_synonym contract_behavior = "contract_action * (account_state \<Rightarrow> bool)"

record response_to_world =
  when_called :: "call_env \<Rightarrow> contract_behavior"
  when_returned :: "return_result \<Rightarrow> contract_behavior"
  when_failed :: "contract_behavior"

abbreviation respond_to_call_correctly ::
  " (call_env \<Rightarrow> contract_behavior) \<Rightarrow>
       account_state \<Rightarrow>
       (variable_env \<Rightarrow> constant_env \<Rightarrow> bool (* This part should be unnecessary after assertions are introduced *)) =>
       bool"
where "respond_to_call_correctly c a I \<equiv>
  (\<forall> call_env initial_venv resulting_action final_state_pred.
     build_venv_called a call_env initial_venv \<longrightarrow>
     ( (* The invariant holds at the beginning *)
       I initial_venv (build_cenv a)
       \<and>
       ( I initial_venv (build_cenv a) \<longrightarrow>
         (* The specification says the execution should result in these *)
         c call_env = (resulting_action, final_state_pred) \<longrightarrow>
         ( \<forall> steps. (* and for any number of steps *)
           ( let r = program_sem initial_venv (build_cenv a) steps in
             (* either more steps are necessary, or *)
             r = ProgramStepRunOut \<or>
             (* the result matches the specification *)
             (\<exists> pushed_venv st bal.
              r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
              final_state_pred
                (update_account_state a resulting_action st bal pushed_venv))
           )))))
"

abbreviation respond_to_return_correctly ::
  "(return_result \<Rightarrow> contract_behavior) \<Rightarrow>
   account_state \<Rightarrow>
   (variable_env \<Rightarrow> constant_env \<Rightarrow> bool) \<Rightarrow>
   bool"
where
"respond_to_return_correctly r a I \<equiv>
   (\<forall> rr initial_venv final_state_pred resulting_action.
       build_venv_returned a rr (Some initial_venv) \<longrightarrow>
       r rr = (resulting_action, final_state_pred) \<longrightarrow>
       ( \<forall> steps.
          (let r = program_sem initial_venv (build_cenv a) steps in
           r = ProgramStepRunOut \<or>
           (\<exists> pushed_venv st bal.
            r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
            final_state_pred
              (update_account_state (account_state_pop_ongoing_call a) resulting_action st bal pushed_venv))
          )))
"

abbreviation respond_to_fail_correctly ::
  "contract_behavior \<Rightarrow>
   account_state \<Rightarrow>
   (variable_env \<Rightarrow> constant_env \<Rightarrow> bool) \<Rightarrow>
   bool"
where
"respond_to_fail_correctly f a I \<equiv>
   (\<forall> initial_venv final_state_pred resulting_action.
      Some initial_venv = build_venv_fail a \<longrightarrow>
      f = (resulting_action, final_state_pred) \<longrightarrow>
      ( \<forall> steps.
        ( let r = program_sem initial_venv (build_cenv a) steps in
          r = ProgramStepRunOut \<or>
          (\<exists> pushed_venv st bal.
             r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
             final_state_pred (update_account_state (account_state_pop_ongoing_call a) resulting_action st bal pushed_venv)))))"


inductive account_state_responds_to_world ::
  "(account_state \<Rightarrow> bool) \<Rightarrow> response_to_world \<Rightarrow>
   (variable_env \<Rightarrow> constant_env \<Rightarrow> bool) \<Rightarrow> bool"
where
AccountStep:
  "(\<forall> a. precond a \<longrightarrow> respond_to_call_correctly c a I) \<Longrightarrow>
   (\<forall> a. precond a \<longrightarrow> respond_to_return_correctly r a I) \<Longrightarrow>
   (\<forall> a. precond a \<longrightarrow> respond_to_fail_correctly f a I) \<Longrightarrow>
   account_state_responds_to_world precond
   \<lparr> when_called = c, when_returned = r, when_failed = f \<rparr>
   I"

declare word_rcat_def [simp]
        unat_def [simp]
        bin_rcat_def [simp]

end
