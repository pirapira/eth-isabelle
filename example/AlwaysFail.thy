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


value "(program_content (program_of_lst always_fail_code))"

abbreviation always_fail_account_state :: "uint \<Rightarrow> account_state"
where
"always_fail_account_state balance ==
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = program_of_lst (always_fail_code)
   , account_balance = balance
   , account_ongoing_calls = []
   , account_killed = False
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

declare eval_annotation_def [simp]

lemma problem :
"node \<langle> x, ll, elm, rr\<rangle> y \<langle>\<rangle> = Node (x + 1) \<langle> x, ll, elm, rr\<rangle> y \<langle>\<rangle> "
apply(simp add: node_def)
done

lemma problem2 :
"node \<langle>\<rangle> y \<langle>x, \<langle>\<rangle>, elm, \<langle>\<rangle>\<rangle> = Node (x + 1) \<langle>\<rangle> y \<langle> x, \<langle>\<rangle>, elm, \<langle>\<rangle>\<rangle>"
apply(simp add: node_def)
done

lemma always_fail_correct:
"
  account_state_responds_to_world
  (\<lambda> a. a = always_fail_account_state initial_balance)
  (always_fail_spec initial_balance)
"
apply(rule AccountStep; auto)
apply(case_tac steps; auto)
done

declare one_step.simps [simp]
declare world_turn.simps [simp]
declare contract_turn.simps [simp]

lemma no_assertion_failure:
"no_assertion_failure (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))"
apply(simp only: no_assertion_failure_def)
apply(simp add: initial_program_result.simps)
apply(auto)
 apply(drule star_case; auto)
 apply(case_tac steps; auto)
 apply(drule star_case; auto)
apply(case_tac steps; auto)
apply(case_tac steps; auto)
done

end
