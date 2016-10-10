theory AlwaysFail

imports Main "../ContractSem"

begin

definition this_address :: address
where "this_address = undefined"

definition always_fail_code :: "inst list"
where
"always_fail_code =
   Stack (PUSH_N [0]) # Pc JUMP # []"

definition always_fail_account_state :: "uint \<Rightarrow> account_state"
where
"always_fail_account_state balance =
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = always_fail_code
   , account_balance = balance
   , account_ongoing_calls = []
   \<rparr>"
   
definition always_fail_spec :: "uint \<Rightarrow> response_to_world"
where
" always_fail_spec initial_balance =
  \<lparr> when_called = \<lambda> _. (ContractFail, always_fail_account_state initial_balance)
  , when_returned = \<lambda> _. (ContractFail, always_fail_account_state initial_balance)
  , when_failed = (ContractFail, always_fail_account_state initial_balance)
  \<rparr>
"

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "ev (Suc(Suc 0))"

apply(rule evSS)
apply (rule ev0)
done

lemma always_fail_correct:
"
  account_state_responds_to_world
  (always_fail_account_state initial_balance)
  (always_fail_spec initial_balance)
  (\<lambda> _ _. True)
"
apply (simp add: always_fail_spec_def)
apply (rule AccountStep)
  apply(simp add: respond_to_call_correctly_def)
  apply(rule allI)
  apply(rule allI)
  apply(rule impI)
  apply(simp add: always_fail_account_state_def)
  apply(simp add: always_fail_code_def)
  apply(simp add: build_cenv_def)
  apply(simp add: build_venv_called.simps)
  apply(auto)
  apply(case_tac steps)
   apply(auto)
  apply(simp add: stack_0_1_op_def add: venv_advance_pc_def add: drop_one_element_def)
  apply(case_tac nat)
   apply(auto)
  apply(simp add: jump_def add: venv_stack_top_def add: venv_change_sfx_def
             add: venv_first_instruction_def add: word_rcat_def)
  apply(simp add: unat_def)
  apply(simp add: bin_rcat_def)
  apply(simp add: instruction_failure_result_def)
  apply(simp add: update_account_state_def)
 apply(simp add: respond_to_return_correctly_def)
 apply(simp add: always_fail_account_state_def)
 apply(simp add: build_cenv_def)
 apply(simp add: build_venv_returned.simps)
apply(simp add: respond_to_fail_correctly_def)
apply(simp add: build_venv_fail_def)
apply(simp add: always_fail_account_state_def)
done

end
