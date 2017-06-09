theory AlwaysFail

imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl"

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
   , account_storage = (\<lambda> (a::w256). 0)
   , account_code = program_of_lst always_fail_code program_content_of_lst
   , account_balance = balance
   , account_ongoing_calls = []
   , account_killed = False
   \<rparr>"

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
"P (if check_resources v con s i net then X else InstructionToEnvironment a b c) =
 (\<not> (check_resources v con s i net \<and> \<not> P X \<or> \<not> check_resources v con s i net \<and> \<not> P (InstructionToEnvironment a b c)))"
apply(simp only: if_splits(2))
done

declare inst_stack_numbers.simps [simp]
declare pc_inst_numbers.simps [simp]


declare one_round.simps [simp]
declare environment_turn.simps [simp]
declare contract_turn.simps [simp]

lemma no_assertion_failure:
"no_assertion_failure net (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))"
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
pre_post_conditions net (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))
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
