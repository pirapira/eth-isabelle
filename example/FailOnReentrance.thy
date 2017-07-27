theory FailOnReentrance

imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl"

begin

abbreviation fail_on_reentrance_program :: "inst list"
where
"fail_on_reentrance_program ==
  Stack (PUSH_N [0]) #
  Storage SLOAD #
  Dup 0 #
  Stack (PUSH_N [2]) #
  Pc JUMPI #
  Stack (PUSH_N [1]) #
  Arith ADD #
  Stack (PUSH_N [0]) #
  Storage SSTORE #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0xabcdef]) #
  Stack (PUSH_N [30000]) #
  Misc CALL #
  Arith ISZERO #
  Stack (PUSH_N [2]) #
  Pc JUMPI #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Storage SSTORE #
  Misc STOP # []"
  
definition fail_on_reentrance_address :: address
where
"fail_on_reentrance_address = undefined"

inductive fail_on_reentrance_state :: "nat \<Rightarrow> account_state \<Rightarrow> bool"
where
  depth_zero:
    "account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_storage st 0 = 0 \<Longrightarrow>
     account_code st = program_of_lst fail_on_reentrance_program program_content_of_lst \<Longrightarrow>
     account_ongoing_calls st = [] \<Longrightarrow>
     account_killed st = False \<Longrightarrow>
     fail_on_reentrance_state 0 st"
| depth_one:
    "account_code st = program_of_lst fail_on_reentrance_program program_content_of_lst \<Longrightarrow>
     account_storage st 0 = 1 \<Longrightarrow>
     account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_ongoing_calls st = [(ve, 0, 0)] \<Longrightarrow>
     account_killed st = False \<Longrightarrow>
     vctx_pc ve = 28 \<Longrightarrow>
     vctx_storage ve 0 = 1 \<Longrightarrow>
     vctx_storage_at_call ve 0 = 0 \<Longrightarrow>
     fail_on_reentrance_state 1 st"

value "program_of_lst fail_on_reentrance_program"     

declare fail_on_reentrance_state.simps [simp]

inductive fail_on_reentrance_invariant :: "account_state \<Rightarrow> bool"
where
  depth_zero:
    "account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_storage st 0 = 0 \<Longrightarrow>
     account_code st = program_of_lst fail_on_reentrance_program program_content_of_lst \<Longrightarrow>
     account_ongoing_calls st = [] \<Longrightarrow>
     account_killed st = False \<Longrightarrow>
     fail_on_reentrance_invariant st"
| depth_one:
    "account_code st = program_of_lst fail_on_reentrance_program program_content_of_lst \<Longrightarrow>
     account_storage st 0 = 1 \<Longrightarrow>
     account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_ongoing_calls st = [(ve, 0, 0)] \<Longrightarrow>
     account_killed st = False \<Longrightarrow>
     vctx_pc ve = 28 \<Longrightarrow>
     vctx_storage ve 0 = 1 \<Longrightarrow>
     vctx_storage_at_call ve 0 = 0 \<Longrightarrow>
     fail_on_reentrance_invariant st"

value "program_content (program_of_lst fail_on_reentrance_program program_content_of_lst) 8"

declare one_round.simps [simp]
declare environment_turn.simps [simp]
declare contract_turn.simps [simp]

lemma check_resources_split [split] :
"P (if check_resources v con s i net then X else k) =
          (\<not> (\<not> check_resources v con s i net \<and> \<not> P k \<or> check_resources v con s i net \<and> \<not> P X ))"
apply(simp only: if_splits(2))
apply(auto)
done

lemma discard_check_resources [dest!] :
"check_resources v c s i net \<Longrightarrow> True"
apply(auto)
done

declare network_of_block_number_def [simp]
declare at_least_eip150.simps [simp]

lemma invariant_kept:
"at_least_eip150 net \<Longrightarrow> invariant_holds net fail_on_reentrance_invariant"
apply(simp add: invariant_holds_def)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule impI)
apply(drule fail_on_reentrance_invariant.cases; auto)
 apply(drule star_case; auto)
  apply(simp add: invariant_holds_post_def; rule depth_zero; auto)
 apply(case_tac steps; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
 apply(drule star_case; auto) (* called out and coming back *)
   apply(simp add: invariant_holds_post_def; rule depth_one; simp?)
     apply(simp)
    apply(simp)
   apply(simp)
  apply(drule fail_on_reentrance_invariant.cases; auto)
  apply(case_tac steps; auto simp add: fail_on_reentrance_invariant.simps)
  apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
  apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
  apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
  apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
  apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
  apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
  apply(simp add: invariant_holds_post_def; rule depth_zero; simp?)
 apply(case_tac steps; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
 apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
apply(drule star_case; auto)
 apply(simp add: invariant_holds_post_def fail_on_reentrance_invariant.simps)
apply(case_tac steps; auto simp add: fail_on_reentrance_invariant.simps)
apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
apply(case_tac nat; auto simp add: fail_on_reentrance_invariant.simps)
apply(case_tac nata; auto simp add: fail_on_reentrance_invariant.simps)
done

end
