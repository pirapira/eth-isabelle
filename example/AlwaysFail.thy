theory AlwaysFail

imports Main "../ContractSem" "../RelationalSem"

begin

definition this_address :: address
where "this_address = undefined"

abbreviation always_fail_code :: "inst list"
where
"always_fail_code ==
   Stack (PUSH_N [0])
 # Annotation (\<lambda> aenv. aenv_stack aenv ! 0 = 0)
 # Pc JUMP #
 []"

abbreviation always_fail_account_state :: "uint \<Rightarrow> account_state"
where
"always_fail_account_state balance ==
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = always_fail_code
   , account_balance = balance
   , account_ongoing_calls = []
   \<rparr>"
   
abbreviation always_fail_spec :: "uint \<Rightarrow> response_to_world"
where
" always_fail_spec initial_balance ==
  \<lparr> when_called = \<lambda> _. (ContractFail,
                        \<lambda> a. a = always_fail_account_state initial_balance)
  , when_returned = \<lambda> _. (ContractFail, 
                           \<lambda> a. a = always_fail_account_state initial_balance)
  , when_failed = (ContractFail,
                     \<lambda> a. a = always_fail_account_state initial_balance)
  \<rparr>
"

lemma always_fail_correct:
"
  account_state_responds_to_world
  (\<lambda> a. a = always_fail_account_state initial_balance)
  (always_fail_spec initial_balance)
"
apply(rule AccountStep; auto)
done


lemma no_assertion_failure:
"no_assertion_failure (always_fail_account_state initial_balance)"
apply(simp only: no_assertion_failure_def)
apply(rule allI)
apply(rule reachable_ind)
apply(auto)
 apply(simp add: initial_instruction_result.simps)
apply(simp add: initial_instruction_result.simps)
apply(auto)
apply(simp add: one_step.simps)
apply(simp add: world_turn.simps)
apply(auto)

oops

end
