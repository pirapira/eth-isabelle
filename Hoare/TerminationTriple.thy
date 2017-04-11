theory TerminationTriple
imports "EvmFacts" "./Hoare"
  "HoareTripleForInstructions"

begin

definition all_context :: "state_element set_pred" where
"all_context s = (\<exists>c v.  s = contexts_as_set v c)"

lemma context_maximal :
 "(rest ** all_context) (contexts_as_set v1 c) \<Longrightarrow>
  rest {}"
  by (smt Un_upper2 all_context_def inf_sup_absorb maximality sep_def)

lemma all_context_rest :
 "(rest ** all_context) (contexts_as_set v1 c) \<Longrightarrow>
  (rest ** all_context) (contexts_as_set v2 c)"
  by (metis all_context_def context_maximal inf_bot_right sep_def set_pred.commute sup_bot.right_neutral)

definition all_with_gas :: "int \<Rightarrow> state_element set_pred" where
"all_with_gas g s = (\<exists>c v.  s = contexts_as_set v c \<and>
   vctx_gas v = g \<and> vctx_memory_usage v \<ge> 0)"

definition all_with_less_gas :: "int \<Rightarrow> state_element set_pred" where
"all_with_less_gas g s = (\<exists>c v.  s = contexts_as_set v c \<and>
   vctx_gas v < g \<and> vctx_memory_usage v \<ge> 0)"

definition all_perhaps_less_gas :: "int \<Rightarrow> state_element set_pred" where
"all_perhaps_less_gas g s = (\<exists>c v.  s = contexts_as_set v c \<and>
   vctx_gas v \<le> g \<and> vctx_memory_usage v \<ge> 0)"


lemma some_gas_in_context :
"(rest ** all_with_gas g) s \<Longrightarrow>
 (rest ** all_perhaps_less_gas g) s"
apply(auto simp add:rw sep_def  not_continuing_def
   all_context_def
   all_with_gas_def
   all_perhaps_less_gas_def
         failing_def some_gas_def code_def)
done

lemma case_1 :
assumes a :
 "(rest ** all_with_gas g) (contexts_as_set x1 co_ctx)"
shows  "(rest ** not_continuing ** all_perhaps_less_gas g ** failing)
           (insert (ContinuingElm False)
             (insert
               (ContractActionElm (ContractFail lst))
               (contexts_as_set x1 co_ctx)))"
proof -
  let ?set =  "contexts_as_set x1 co_ctx"
  let ?base =  "rest ** all_perhaps_less_gas g"
from a have "?base ?set" using some_gas_in_context by force
then have "(?base ** not_continuing) (insert (ContinuingElm False) ?set)"
  using context_cont1 not_cont_insert by presburger
then have "(?base ** not_continuing)
   (insert (ContinuingElm False) ?set-{ContractActionElm (ContractFail lst)})"
  by (metis (full_types) Diff_empty Diff_insert2 context_cont context_cont1 contexts_as_set_def insert_minus state_element.distinct(685))
then show ?thesis
  by (metis failing_insert insert_commute sep_three set_pred.commute) 
qed

lemma funext : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
by auto

lemma code_emp [simp] : "code {} = emp"
apply (rule funext)
apply (simp add:emp_def code_def)
done

lemma all_with_gas_max :
   "(rest ** all_with_gas g) (contexts_as_set v1 co_ctx) \<Longrightarrow>
    rest {}"
  by (smt all_with_gas_def inf_sup_absorb maximality sep_def sup.cobounded2)

lemma all_with_gas_memu :
   "(rest ** all_with_gas g) (contexts_as_set v1 co_ctx) \<Longrightarrow>
    vctx_memory_usage v1 \<ge> 0"
  by (smt Un_upper2 all_with_gas_def get_condition1 sep_def)

lemma all_with_gas_gas :
   "(rest ** all_with_gas g) (contexts_as_set v1 co_ctx) \<Longrightarrow>
    vctx_gas v1 = g"
  by (smt Un_upper2 all_with_gas_def get_condition1 sep_def)

lemma construct_less_gas :
"vctx_memory_usage v2 \<ge> 0 \<Longrightarrow> vctx_gas v2 < g \<Longrightarrow>
 rest {} \<Longrightarrow>
 (rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
  by (metis all_with_less_gas_def emp_def imp_sepL sep_emp set_pred.commute)

lemma construct_perhaps_gas :
"vctx_memory_usage v2 \<ge> 0 \<Longrightarrow> vctx_gas v2 \<le> g \<Longrightarrow>
 rest {} \<Longrightarrow>
 (rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
  by (metis all_perhaps_less_gas_def emp_def imp_sepL sep_emp set_pred.commute)

lemma add_action :
"rest (insert (ContinuingElm False)
     (contexts_as_set v2 co_ctx)) \<Longrightarrow>
 pred act \<Longrightarrow>
 (action pred ** rest)
     (instruction_result_as_set co_ctx
       (InstructionToEnvironment act v2 x33))"
apply (simp add: instruction_result_as_set_def
              action_def sep_def action_not_context)
apply force
done

lemma normal_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst = InstructionContinue v2"
 shows  "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b continue_decr_gas memu_good by fastforce
  then show ?thesis using construct_less_gas all_with_gas_max a by fastforce
qed

lemma call_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractCall x1) v2 x33"
 shows "(calling ** not_continuing **
           rest ** all_with_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractCall x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b call_decr_gas memu_good_env by fastforce
  then have "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_less_gas all_with_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_with_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis  by (smt add_action calling_def)
qed

lemma delegatecall_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractDelegateCall x1) v2 x33"
 shows "(delegating ** not_continuing **
           rest ** all_with_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractDelegateCall x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b delegatecall_decr_gas memu_good_env by fastforce
  then have "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_less_gas all_with_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_with_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis by (smt add_action delegating_def)
qed

lemma create_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractCreate x1) v2 x33"
 shows "(creating ** not_continuing **
           rest ** all_with_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractCreate x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b create_decr_gas memu_good_env by fastforce
  then have "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_less_gas all_with_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_with_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis by (smt add_action creating_def)
qed

lemma fail_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractFail x1) v2 x33"
 shows "(failing ** not_continuing **
           rest ** all_perhaps_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractFail x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 \<le> g"
   using b memu_good_env env_meter_gas meter_gas_ge_0 by fastforce 
  then have "(rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_perhaps_gas all_with_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_perhaps_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis
    using add_action
      [of "not_continuing ** rest ** all_perhaps_less_gas g" v2 co_ctx
        "\<lambda>y. \<exists>x. ContractFail x = y" "ContractFail x1" x33]
    by (simp add: failing_def)
qed

lemma suicide_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractSuicide x1) v2 x33"
 shows "(destructing ** not_continuing **
           rest ** all_perhaps_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractSuicide x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 \<le> g"
   using b memu_good_env env_meter_gas meter_gas_ge_0 by fastforce 
  then have "(rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_perhaps_gas all_with_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_perhaps_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis
    using add_action
      [of "not_continuing ** rest ** all_perhaps_less_gas g" v2 co_ctx
        "\<lambda>y. \<exists>x. ContractSuicide x = y" "ContractSuicide x1" x33]
    by (simp add: destructing_def)
    
qed

lemma return_case : assumes
 a:"(rest ** all_with_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractReturn x1) v2 x33"
 shows "(returning ** not_continuing **
           rest ** all_perhaps_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractReturn x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 = g"
    using all_with_gas_gas all_with_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 \<le> g"
   using b memu_good_env env_meter_gas meter_gas_ge_0 by fastforce 
  then have "(rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_perhaps_gas all_with_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_perhaps_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis by (smt add_action returning_def)
qed

lemma simple :
"instruction_result_as_set co_ctx
          (InstructionContinue v1) -
         {ContinuingElm True} = contexts_as_set v1 co_ctx"
apply (simp add:instruction_result_as_set_def)
done

lemma using_gas_triple :
   "triple {} (all_with_gas g ** continuing) {}
    (all_with_less_gas g ** continuing 
    ## all_with_less_gas g ** not_continuing **
      (delegating ## calling ## creating)
    ## all_perhaps_less_gas g ** not_continuing **
       (failing ## returning  ## destructing))"
apply(auto simp add: triple_def)
 apply(rule_tac x = 1 in exI)
 apply(case_tac presult; auto)
apply (simp add:sep_add_def  program_sem.simps next_state_def)
apply (case_tac "vctx_next_instruction x1 co_ctx")
apply (auto simp add:case_1 meter_gas_check)
apply (simp add: instruction_result_as_set_def)
using case_1 apply force
defer
defer
apply (simp add: instruction_result_as_set_def)
using case_1 apply force
using meter_gas_check apply force
using meter_gas_check apply force
apply (simp add: instruction_result_as_set_def)
using case_1 apply force
subgoal for co_ctx rest v1 inst
apply (case_tac "instruction_sem v1 co_ctx inst"; auto)
apply (simp add: instruction_result_as_set_def)
using no_annotation_inst apply simp
apply (case_tac x31; auto simp:simple)
using call_case apply force
using delegatecall_case apply force
using create_case apply force
using fail_case apply force
using suicide_case apply force
using return_case apply force
done
subgoal for co_ctx rest v1 inst
apply (case_tac "instruction_sem v1 co_ctx inst"; auto)
apply (simp add: instruction_result_as_set_def)
using normal_case apply simp
using no_annotation_inst apply simp
apply (case_tac x31; auto simp:simple)
using call_case apply force
using delegatecall_case apply force
using create_case apply force
using fail_case apply force
using suicide_case apply force
using return_case apply force
done
done

(* need to start from beginning, more general or perhaps less
   strict *)

lemma perhaps_less :
  "all_perhaps_less_gas g = all_with_less_gas (g+1)"
apply (auto simp:all_perhaps_less_gas_def all_with_less_gas_def)
done

lemma case_2 :
assumes a :
 "(rest ** all_perhaps_less_gas g) (contexts_as_set x1 co_ctx)"
shows  "(rest ** not_continuing ** all_perhaps_less_gas g ** failing)
           (insert (ContinuingElm False)
             (insert
               (ContractActionElm (ContractFail lst))
               (contexts_as_set x1 co_ctx)))"
proof -
  let ?set =  "contexts_as_set x1 co_ctx"
  let ?base =  "rest ** all_perhaps_less_gas g"
from a have "(?base ** not_continuing) (insert (ContinuingElm False) ?set)"
  using context_cont1 not_cont_insert by presburger
then have "(?base ** not_continuing)
   (insert (ContinuingElm False) ?set-{ContractActionElm (ContractFail lst)})"
  by (metis (full_types) Diff_empty Diff_insert2 context_cont context_cont1 contexts_as_set_def insert_minus state_element.distinct(685))
then show ?thesis
  by (metis failing_insert insert_commute sep_three set_pred.commute) 
qed

lemma perhaps_gas_max :
   "(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx) \<Longrightarrow>
    rest {}"
  by (smt all_perhaps_less_gas_def inf_sup_absorb maximality sep_def sup.cobounded2)

lemma perhaps_gas_memu :
   "(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx) \<Longrightarrow>
    vctx_memory_usage v1 \<ge> 0"
  by (smt Un_upper2 all_perhaps_less_gas_def get_condition1 sep_def)

lemma perhaps_gas_gas :
   "(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx) \<Longrightarrow>
    vctx_gas v1 \<le> g"
  by (smt Un_upper2 all_perhaps_less_gas_def get_condition1 sep_def)



lemma normal_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst = InstructionContinue v2"
 shows  "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b continue_decr_gas memu_good by fastforce
  then show ?thesis
   using construct_less_gas perhaps_gas_max a by fastforce
qed

lemma call_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractCall x1) v2 x33"
 shows "(calling ** not_continuing **
           rest ** all_with_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractCall x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b call_decr_gas memu_good_env by fastforce
  then have "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_less_gas perhaps_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_with_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis  by (smt add_action calling_def)
qed

lemma delegatecall_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractDelegateCall x1) v2 x33"
 shows "(delegating ** not_continuing **
           rest ** all_with_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractDelegateCall x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b delegatecall_decr_gas memu_good_env by fastforce
  then have "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_less_gas perhaps_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_with_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis by (smt add_action delegating_def)
qed

lemma create_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractCreate x1) v2 x33"
 shows "(creating ** not_continuing **
           rest ** all_with_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractCreate x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 < g"
   using b create_decr_gas memu_good_env by fastforce
  then have "(rest ** all_with_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_less_gas perhaps_gas_max a by fastforce
  then have "(not_continuing ** rest ** all_with_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis by (smt add_action creating_def)
qed

lemma fail_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractFail x1) v2 x33"
 shows "(failing ** not_continuing **
           rest ** all_perhaps_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractFail x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 \<le> g"
   using b memu_good_env env_meter_gas meter_gas_ge_0 by smt
  then have "(rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_perhaps_gas perhaps_gas_max a by blast
  then have "(not_continuing ** rest ** all_perhaps_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis
    using add_action
      [of "not_continuing ** rest ** all_perhaps_less_gas g" v2 co_ctx
        "\<lambda>y. \<exists>x. ContractFail x = y" "ContractFail x1" x33]
    by (simp add: failing_def)
qed

lemma suicide_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractSuicide x1) v2 x33"
 shows "(destructing ** not_continuing **
           rest ** all_perhaps_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractSuicide x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 \<le> g"
   using b memu_good_env env_meter_gas meter_gas_ge_0 by smt
  then have "(rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_perhaps_gas perhaps_gas_max a by blast
  then have "(not_continuing ** rest ** all_perhaps_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis
    using add_action
      [of "not_continuing ** rest ** all_perhaps_less_gas g" v2 co_ctx
        "\<lambda>y. \<exists>x. ContractSuicide x = y" "ContractSuicide x1" x33]
    by (simp add: destructing_def)
    
qed

lemma return_case2 : assumes
 a:"(rest ** all_perhaps_less_gas g) (contexts_as_set v1 co_ctx)" and
 b:"instruction_sem v1 co_ctx inst =
    InstructionToEnvironment (ContractReturn x1) v2 x33"
 shows "(returning ** not_continuing **
           rest ** all_perhaps_less_gas g)
           (instruction_result_as_set co_ctx
             (InstructionToEnvironment
               (ContractReturn x1) v2 x33))"
proof -
  from a have "vctx_memory_usage v1 \<ge> 0 \<and> vctx_gas v1 \<le> g"
    using perhaps_gas_gas perhaps_gas_memu by auto
  then have "vctx_memory_usage v2 \<ge> 0 \<and> vctx_gas v2 \<le> g"
   using b memu_good_env env_meter_gas meter_gas_ge_0 by smt
  then have "(rest ** all_perhaps_less_gas g) (contexts_as_set v2 co_ctx)"
   using construct_perhaps_gas perhaps_gas_max a by blast
  then have "(not_continuing ** rest ** all_perhaps_less_gas g)
    (insert (ContinuingElm False) (contexts_as_set v2 co_ctx))"
    by (simp add: not_continuing_sep)
  then show ?thesis by (smt add_action returning_def)
qed

lemma using_gas_triple2 :
   "triple {} (all_perhaps_less_gas g ** continuing) {}
    (all_with_less_gas g ** continuing 
    ## all_with_less_gas g ** not_continuing **
      (delegating ## calling ## creating)
    ## all_perhaps_less_gas g ** not_continuing **
       (failing ## returning  ## destructing))"
apply(auto simp add: triple_def)
 apply(rule_tac x = 1 in exI)
 apply(case_tac presult; auto)
apply (simp add:sep_add_def  program_sem.simps next_state_def)
apply (case_tac "vctx_next_instruction x1 co_ctx")
apply (auto simp add:case_1 meter_gas_check)
apply (simp add: instruction_result_as_set_def)
using case_2 apply force
defer
defer
apply (simp add: instruction_result_as_set_def)
using case_2 apply force
using meter_gas_check apply force
using meter_gas_check apply force
apply (simp add: instruction_result_as_set_def)
using case_2 apply force
subgoal for co_ctx rest v1 inst
apply (case_tac "instruction_sem v1 co_ctx inst"; auto)
apply (simp add: instruction_result_as_set_def)
using no_annotation_inst apply simp
apply (case_tac x31; auto simp:simple)
using call_case2 apply force
using delegatecall_case2 apply force
using create_case2 apply force
using fail_case2 apply force
using suicide_case2 apply force
using return_case2 apply force
done
subgoal for co_ctx rest v1 inst
apply (case_tac "instruction_sem v1 co_ctx inst"; auto)
apply (simp add: instruction_result_as_set_def)
using normal_case2 apply simp
using no_annotation_inst apply simp
apply (case_tac x31; auto simp:simple)
using call_case2 apply force
using delegatecall_case2 apply force
using create_case2 apply force
using fail_case2 apply force
using suicide_case2 apply force
using return_case2 apply force
done
done

(*
lemma using_gas_triple3 :
   "triple {} (all_perhaps_less_gas g ** \<langle>g > 0\<rangle> ** continuing) {}
    (all_with_less_gas g  ** \<langle>g-1 > 0\<rangle> ** continuing 
    ## all_with_less_gas g ** not_continuing **
      (delegating ## calling ## creating)
    ## all_perhaps_less_gas g ** not_continuing **
       (failing ## returning  ## destructing))"
apply(auto simp add: triple_def)
 apply(rule_tac x = 1 in exI)
 apply(case_tac presult; auto)
apply (simp add:sep_add_def  program_sem.simps next_state_def)
apply (case_tac "vctx_next_instruction x1 co_ctx")
apply (auto simp add:case_1 meter_gas_check)
apply (simp add: instruction_result_as_set_def)
using case_2 apply force
defer
defer
apply (simp add: instruction_result_as_set_def)
using case_2 apply force
using meter_gas_check apply force
using meter_gas_check apply force
apply (simp add: instruction_result_as_set_def)
using case_2 apply force
subgoal for co_ctx rest v1 inst
apply (case_tac "instruction_sem v1 co_ctx inst"; auto)
apply (simp add: instruction_result_as_set_def)
using no_annotation_inst apply simp
apply (case_tac x31; auto simp:simple)
using call_case2 apply force
using delegatecall_case2 apply force
using create_case2 apply force
using fail_case2 apply force
using suicide_case2 apply force
using return_case2 apply force
done
subgoal for co_ctx rest v1 inst
apply (case_tac "instruction_sem v1 co_ctx inst"; auto)
apply (simp add: instruction_result_as_set_def)
using normal_case2 apply simp
using no_annotation_inst apply simp
apply (case_tac x31; auto simp:simple)
using call_case2 apply force
using delegatecall_case2 apply force
using create_case2 apply force
using fail_case2 apply force
using suicide_case2 apply force
using return_case2 apply force
done
done
*)
lemma test :
  " all_perhaps_less_gas (if 0 \<le> g then g else 0) **
       \<langle> 0 < (if 0 \<le> g then g else 0) \<rangle> =
    all_perhaps_less_gas g ** \<langle> 0 < g \<rangle>"
apply (cases "0 \<le> g")
apply auto
done

lemma false_zero : "\<langle> False \<rangle> = zero"
apply (auto simp:zero_def pure_def)
done

lemma termination_triple :
   "\<exists>y. y < 0 \<and>
    triple {} (all_perhaps_less_gas g ** continuing) {}
    (all_perhaps_less_gas y ** continuing ##
      (all_with_less_gas g ** not_continuing **
      (delegating ## calling ## creating)
    ## all_perhaps_less_gas g ** not_continuing **
       (failing ## returning  ## destructing)))"
apply (rule loop_triple_int [of "\<lambda>g. all_perhaps_less_gas g ** continuing"
  "all_with_less_gas g ** not_continuing **
      (delegating ## calling ## creating)
    ## all_perhaps_less_gas g ** not_continuing **
       (failing ## returning  ## destructing)" g])

using loop_triple_int [of "\<lambda>g. all_perhaps_less_gas g ** continuing"
  "all_with_less_gas g ** not_continuing **
      (delegating ## calling ## creating)
    ## all_perhaps_less_gas g ** not_continuing **
       (failing ## returning  ## destructing)" g]
apply (auto simp:test false_zero zero_mul zero_add)


end
