theory TerminationTriple
imports "./Hoare" "./HoareTripleForInstructions" "EvmFacts"

begin

definition all :: "state_element set_pred" where
"all s = True"

definition ex :: "('a \<Rightarrow> 'b set_pred) \<Rightarrow> 'b set_pred" where
"ex f s = (\<exists>x. f x s)"

definition gas_smaller :: "int \<Rightarrow> state_element set_pred" where
"gas_smaller x s = (\<exists>y. y < x \<and> gas_pred y s)"

definition some_gas :: "state_element set_pred" where
"some_gas s = (\<exists>y. gas_pred y s)"

definition sep_add :: "'a set_pred \<Rightarrow> 'a set_pred \<Rightarrow> 'a set_pred"
  where
    "sep_add p q == (\<lambda> s. p s \<or> q s)"

notation sep_add (infixr "##" 59)

lemma sep_add_assoc [simp]: "((a ## b) ## c) = (a ## b ## c)"
  by (simp add: sep_add_def)

lemma sep_add_commute [simp]: "(a ## b)= (b ## a)"
 by (simp add: sep_add_def) blast

definition never :: "'a set_pred" where
"never == (\<lambda>s. False)"

lemma sep_add_never [simp] : "r ## never = r"
by (simp add: never_def sep_add_def)

lemma sep_add_distr [simp] : "a ** (b ## c) = a**b ## a**c"
by (simp add: sep_def sep_add_def) blast

definition failing :: "state_element set_pred" where
"failing s = (\<exists>x. ContractActionElm (ContractFail x) \<in> s)"

definition returning :: "state_element set_pred" where
"returning s = (\<exists>x. ContractActionElm (ContractReturn x) \<in> s)"

definition destructing :: "state_element set_pred" where
"destructing s = (\<exists>x. ContractActionElm (ContractSuicide x) \<in> s)"

definition calling :: "state_element set_pred" where
"calling s = (\<exists>x. ContractActionElm (ContractCall x) \<in> s)"

definition creating :: "state_element set_pred" where
"creating s = (\<exists>x. ContractActionElm (ContractCreate x) \<in> s)"

definition delegating :: "state_element set_pred" where
"delegating s = (\<exists>x. ContractActionElm (ContractDelegateCall x) \<in> s)"

lemmas rw = instruction_sem_def instruction_failure_result_def
  subtract_gas.simps stack_2_1_op_def stack_1_1_op_def
  stack_3_1_op_def stack_0_1_op_def  general_dup_def
  mload_def mstore_def mstore8_def calldatacopy_def
  codecopy_def stack_0_0_op_def jump_def jumpi_def
  extcodecopy_def sstore_def pc_def pop_def swap_def log_def
  stop_def create_def call_def delegatecall_def ret_def
  suicide_def callcode_def strict_if_def blocked_jump_def
blockedInstructionContinue_def

lemma inst_no_reasons :
"instruction_sem v c aa \<noteq>
       InstructionToEnvironment
        (ContractFail []) a b"
apply (cases aa)
apply (simp add:rw)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw sha3_def
   split:list.split if_split)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a
                (vctx_memory v))"; auto simp:rw)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;
  auto simp:rw split:list.split option.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
defer
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw
   split:list.split option.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw
   split:list.split option.split)
apply (case_tac "vctx_next_instruction (v
               \<lparr>vctx_stack := x22,
                  vctx_pc := uint x21\<rparr>)
                  c"; auto simp:rw)
subgoal for x y aaa
apply (case_tac aaa; auto simp:rw)
apply (case_tac x9; auto simp:rw)
done
apply (case_tac "vctx_next_instruction (v
               \<lparr>vctx_stack := x22,
                  vctx_pc := uint x21\<rparr>)
                  c"; auto simp:rw)
subgoal for x y z aaa
apply (case_tac aaa; auto simp:rw)
apply (case_tac x9; auto simp:rw)
done
done

lemma no_reasons_next :
   "failed_for_reasons {}
   (next_state stopper c (InstructionContinue v)) = False"
apply (auto simp:failed_for_reasons_def)
apply (cases "vctx_next_instruction v c"; auto)
apply (auto simp:check_resources_def)
apply (case_tac "case inst_stack_numbers aa of
        (consumed, produced) \<Rightarrow>
          int (length (vctx_stack v)) +
          produced -
          consumed
          \<le> 1024 \<and>
          meter_gas aa v c \<le> vctx_gas v")
apply auto
using inst_no_reasons apply fastforce
using length_greater_0_conv apply fastforce
using n_not_Suc_n apply fastforce
done

lemma program_annotation :
"program_sem stopper c n InstructionAnnotationFailure =
 InstructionAnnotationFailure"
apply (induction n)
apply (auto simp:program_sem.simps)
done

lemma program_environment :
"program_sem stopper c n (InstructionToEnvironment a b d) =
 (InstructionToEnvironment a b d)"
apply (induction n)
apply (auto simp:program_sem.simps)
done

declare next_state_def [simp del]

lemma no_reasons [simp] :
   "failed_for_reasons {}
   (program_sem stopper c n (InstructionContinue v)) = False"
apply (induction n arbitrary:v)
apply (simp add:program_sem.simps failed_for_reasons_def
  program_annotation no_reasons_next)
apply (simp add:program_sem.simps no_reasons_next
  failed_for_reasons_def)
apply (case_tac "next_state stopper c
             (InstructionContinue v)")
using no_reasons_next
apply force
using program_annotation
apply force
using no_reasons_next 
apply (auto simp add: program_environment failed_for_reasons_def)
done

lemmas context_rw = contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def data_sent_as_set_def ext_program_as_set_def

lemma not_cont_insert :
 "x (s-{ContinuingElm False}) \<Longrightarrow>
  (x ** not_continuing) (insert (ContinuingElm False) s)"
apply(auto simp add:rw sep_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
done

lemma context_cont :
  "contexts_as_set x1 co_ctx -
      {ContinuingElm a, ContractActionElm b} =
   contexts_as_set x1 co_ctx"
apply(auto simp add:rw sep_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
done

lemma context_cont1 :
  "contexts_as_set x1 co_ctx - {ContinuingElm a} =
   contexts_as_set x1 co_ctx"
apply(auto simp add:rw sep_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
done

lemma failing_insert :
 "x (s-{ContractActionElm (ContractFail b)}) \<Longrightarrow>
  (x ** failing) (insert (ContractActionElm (ContractFail b)) s)"
apply(auto simp add:rw sep_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
done

lemma some_gas_in_context :
"(rest ** gas_pred g) s \<Longrightarrow>
(rest ** some_gas ) s"
apply(auto simp add:rw sep_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
done

lemma case_1 :
assumes a :
 "(rest ** all ** code {} ** gas_pred g)
   (contexts_as_set x1 co_ctx)"
shows  "(rest ** not_continuing ** all ** failing ** some_gas ** code {})
           (insert (ContinuingElm False)
             (insert
               (ContractActionElm (ContractFail lst))
               (contexts_as_set x1 co_ctx)))"
proof -
  let ?set =  "contexts_as_set x1 co_ctx"
  let ?base =  "rest ** all ** code {} ** some_gas"
from a have "?base ?set"
  by (metis set_pred.assoc some_gas_in_context)
then have "(?base ** not_continuing) (insert (ContinuingElm False) ?set)"
  by (simp add: not_continuing_sep)
then have "(?base ** not_continuing)
   (insert (ContinuingElm False) ?set-{ContractActionElm (ContractFail lst)})"
  by simp
then show ?thesis
  by (metis failing_insert insert_commute sep_three set_pred.commute) 
qed

lemma meter_gas_check :
  "\<not> meter_gas a x1 co_ctx \<le> vctx_gas x1 \<Longrightarrow>
   check_resources x1 co_ctx (vctx_stack x1) a \<Longrightarrow>
   False"
apply (simp add:check_resources_def)
done

lemmas instruction_sem_simps =
  rw sha3_def vctx_update_storage_def
  vctx_pop_stack_def

lemma env_meter_gas :
"instruction_sem v1 c inst =
 InstructionToEnvironment act v2 x33 \<Longrightarrow>
 vctx_gas v2 = vctx_gas v1 - meter_gas inst v1 c"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; 
          clarsimp simp: rw
           split:list.splits)
         apply (case_tac x2 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: instruction_sem_simps split:list.splits)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a (vctx_memory v1))")
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x8 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x9; clarsimp simp: instruction_sem_simps Let_def split: list.splits  pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
done

lemma continue_meter_gas :
"instruction_sem v1 c inst =
 InstructionContinue v2 \<Longrightarrow>
 vctx_gas v2 = vctx_gas v1 - meter_gas inst v1 c"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; 
          clarsimp simp: rw
           split:list.splits)
         apply (case_tac x2 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: instruction_sem_simps split:list.splits)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a (vctx_memory v1))")
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x8 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x9; clarsimp simp: instruction_sem_simps Let_def split: list.splits  pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
done

lemma no_annotation_inst :
"instruction_sem v c a \<noteq> InstructionAnnotationFailure"
apply (cases a)
apply (simp add:rw)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw sha3_def
   split:list.split if_split)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a
                (vctx_memory v))"; auto simp:rw)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;
  auto simp:rw split:list.split option.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
defer
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw
   split:list.split option.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw split:list.split)
apply (rename_tac inst; case_tac inst;auto simp:rw
   split:list.split option.split)
apply (case_tac "vctx_next_instruction (v
               \<lparr>vctx_stack := x22,
                  vctx_pc := uint x21\<rparr>)
                  c"; auto simp:rw)
subgoal for x y aaa
apply (case_tac aaa; auto simp:rw)
apply (case_tac x9; auto simp:rw)
done
apply (case_tac "vctx_next_instruction (v
               \<lparr>vctx_stack := x22,
                  vctx_pc := uint x21\<rparr>)
                  c"; auto simp:rw)
subgoal for x y z aaa
apply (case_tac aaa; auto simp:rw)
apply (case_tac x9; auto simp:rw)
done
done

lemma call_instruction :
"instruction_sem v c inst =
 InstructionToEnvironment (ContractCall args) x32 x33 \<Longrightarrow>
 inst = Misc CALL \<or> inst = Misc CALLCODE"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; 
          clarsimp simp: rw
           split:list.splits)
         apply (case_tac x2 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: instruction_sem_simps split:list.splits)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a (vctx_memory v))")
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x8 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x9; clarsimp simp: instruction_sem_simps Let_def split: list.splits  pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
done

lemma call_decr_gas :
   assumes a:"instruction_sem v1 co_ctx a =
       InstructionToEnvironment (ContractCall x1a)
        v2 x33"
   and good:"vctx_memory_usage v1 \<ge> 0"
  shows  "vctx_gas v1 \<ge> vctx_gas v2"
proof -
  have inst: "a = Misc CALL \<or> a = Misc CALLCODE"
   using call_instruction and a by force
  then have "meter_gas a v1 co_ctx > 0"
   using good and meter_gas_gt_0 by blast
  then show ?thesis using env_meter_gas and a by force
qed

(* Perhaps "all" will have to hog absolutely everything
 ??? *)

(*
lemma gas_decreases_in_triples :
 "g1 \<ge> g2 \<Longrightarrow>
  GasElm g1 \<in> s1 \<Longrightarrow>
  GasElm g2 \<in> s2 \<Longrightarrow>
  (\<forall>h1. GasElm h1 \<in> s1 \<longrightarrow> h1 = g1) \<Longrightarrow>
  (\<forall>h2. GasElm h2 \<in> s2 \<longrightarrow> h2 = g2) \<Longrightarrow>
  (all ** gas_pred g) s1 \<Longrightarrow>
  (all ** gas_smaller g) s2"
apply(auto simp add:rw sep_def gas_smaller_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
*)

(* need to make a better 'all' should have a feature
   like this *)

lemma gas_decreases_in_triples :
 "(rest ** all) (contexts_as_set v1 c) \<Longrightarrow>
  (rest ** all) (contexts_as_set v2 c)"


lemma gas_decreases_in_triples :
 "vctx_gas v2 \<ge> vctx_gas v1 \<Longrightarrow>
  (all ** gas_pred g) (contexts_as_set v1 c) \<Longrightarrow>
  (all ** gas_smaller g) (contexts_as_set v2 c)"


apply (simp add:cont)

lemma using_gas_triple :
   "triple {} (gas_pred g ** continuing ** all) {}
    (gas_smaller g ** continuing ** all
    ## gas_smaller g ** all ** not_continuing **
      (delegating ## calling ## creating ## destructing)
    ## all ** some_gas ** not_continuing **
       (failing ## returning))"
apply(auto simp add: triple_def)
 apply(rule_tac x = 1 in exI)
 apply(case_tac presult; auto)
apply (simp add:sep_add_def instruction_result_as_set_def
  program_sem.simps next_state_def)
apply (case_tac "vctx_next_instruction x1 co_ctx")
apply auto
apply (simp add:case_1)
defer
defer
apply (simp add:case_1)
using meter_gas_check apply force
using meter_gas_check apply force
apply (simp add:case_1)
apply (case_tac "instruction_sem x1 co_ctx a"; auto)
using no_annotation_inst apply force
apply (case_tac x31; auto)


(*
 auto simp add: instruction_result_as_set_def sep_def sep_add_def)
*)
end
