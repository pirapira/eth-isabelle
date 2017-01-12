theory AlwaysFail

imports Main "../ContractSem" "../RelationalSem" "../lem/EvmNonExec" "../ProgramInAvl"

begin

definition this_address :: address
where "this_address = undefined"

abbreviation always_fail_code :: "inst list"
where
"always_fail_code ==
   Stack (PUSH_N [2])
 # Pc JUMP #
 []"


value "(program_content (program_of_lst always_fail_code program_content_of_lst)) 3"

abbreviation always_fail_account_state :: "w256 \<Rightarrow> account_state"
where
"always_fail_account_state balance \<equiv>
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = program_of_lst always_fail_code program_content_of_lst
   , account_balance = balance
   , account_ongoing_calls = []
   , account_killed = False
   \<rparr>"

abbreviation always_fail_spec :: "w256 \<Rightarrow> response_to_environment"
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

lemma problem :
"node \<langle> x, ll, elm, rr\<rangle> y \<langle>\<rangle> = Node (x + 1) \<langle> x, ll, elm, rr\<rangle> y \<langle>\<rangle> "
apply(simp add: node_def)
done

lemma problem2 :
"node \<langle>\<rangle> y \<langle>x, \<langle>\<rangle>, elm, \<langle>\<rangle>\<rangle> = Node (x + 1) \<langle>\<rangle> y \<langle> x, \<langle>\<rangle>, elm, \<langle>\<rangle>\<rangle>"
apply(simp add: node_def)
done

(* declare program_sem.psimps [simp] *)
(* declare instruction_sem_def [simp del]*)

lemma check_resources_split [split] :
"P (if check_resources v con s i then X else InstructionToEnvironment a b c d e f) =
 (\<not> (check_resources v con s i \<and> \<not> P X \<or> \<not> check_resources v con s i \<and> \<not> P (InstructionToEnvironment a b c d e f)))"
apply(simp only: if_splits(2))
done

declare respond_to_call_correctly_def [simp]
declare respond_to_return_correctly_def [simp]
declare respond_to_fail_correctly_def [simp]
declare inst_stack_numbers.simps [simp]
declare pc_inst_numbers.simps [simp]

lemma always_fail_correct:
"
  account_state_responds_to_environment
  (\<lambda> a. a = always_fail_account_state initial_balance)
  (always_fail_spec initial_balance)
"
apply(rule AccountStep; auto)
apply(case_tac steps; auto)
apply(case_tac nata; auto)
done

declare one_round.simps [simp]
declare environment_turn.simps [simp]
declare contract_turn.simps [simp]

lemma no_assertion_failure:
"no_assertion_failure (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))"
apply(simp add: no_assertion_failure_def)
apply(auto)
apply(drule star_case; auto simp add: no_assertion_failure_post_def)
  apply(case_tac steps; auto)
  apply(case_tac nata; auto)
 apply(case_tac steps; auto)
 apply(case_tac nata; auto)
apply(case_tac steps; auto)
apply(case_tac nata; auto)
done

declare postcondition_pack_def [simp]

lemma balance_no_decrease:
"
pre_post_conditions (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))
(\<lambda> initial_state init_call. True)
(\<lambda> initial_state _ (post_state, _). account_balance initial_state \<le> account_balance post_state)
"
apply(simp add: pre_post_conditions_def; auto)
        apply(drule star_case; auto)
         apply(case_tac steps; auto)
         apply(case_tac nata; auto)
        apply(case_tac steps; auto)
        apply(case_tac nata; auto)
       apply(drule star_case; auto)
       apply(case_tac steps; auto)
       apply(case_tac nata; auto)
      apply(drule star_case; auto)
      apply(case_tac steps; auto)
      apply(case_tac nata; auto)
     apply(drule star_case; auto)
     apply(case_tac steps; auto)
     apply(case_tac nata; auto)
    apply(drule star_case; auto)
    apply(case_tac steps; auto)
    apply(case_tac nata; auto)
   apply(drule star_case; auto)
   apply(case_tac steps; auto)
   apply(case_tac nata; auto)
  apply(drule star_case; auto)
  apply(case_tac steps; auto)
  apply(case_tac nata; auto)
 apply(drule star_case; auto)
 apply(case_tac steps; auto)
 apply(case_tac nata; auto)
 apply(drule star_case; auto)
apply(case_tac steps; auto)
apply(case_tac nata; auto)
done

end
