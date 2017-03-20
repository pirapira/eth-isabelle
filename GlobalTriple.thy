theory GlobalTriple

imports "./Hoare" "./lem/Block"

begin

datatype global_element =
  State "state_element"
| AccountStorage "address" "w256" "w256"
| BackupStorage "address" "w256" "w256"
| SavedStorage "nat" "address" "w256" "w256"
| SavedState "nat" "state_element"

type_synonym global_pred = "global_element set \<Rightarrow> bool"

definition state_as_set :: "(address \<Rightarrow> account) \<Rightarrow> global_element set" where
"state_as_set st = {AccountStorage a p e | a p e. e = account_storage0 (st a) p}"

definition backup_as_set :: "(address \<Rightarrow> account) \<Rightarrow> global_element set" where
"backup_as_set st = {BackupStorage a p e | a p e. e = account_storage0 (st a) p}"

definition sstorage_as_set :: "nat \<Rightarrow> (address \<Rightarrow> account) \<Rightarrow> global_element set" where
"sstorage_as_set n st = {SavedStorage n a p e | a p e. e = account_storage0 (st a) p}"

definition saved_as_set :: "nat \<Rightarrow> (address\<Rightarrow>account) \<Rightarrow> constant_ctx \<Rightarrow>
  variable_ctx \<Rightarrow> stack_hint \<Rightarrow> global_element set" where
"saved_as_set n st c v hint =
    sstorage_as_set n st \<union> State ` contexts_as_set v c"

fun saved_stack_as_set ::
 "(world_state * variable_ctx * constant_ctx * stack_hint) list \<Rightarrow> global_element set" where
"saved_stack_as_set Nil = {}"
| "saved_stack_as_set ((st,v,c,h)#lst) =
     saved_as_set (length lst) st c v h \<union> saved_stack_as_set lst"

fun global_as_set :: "global_state \<Rightarrow> global_element set" where
  "global_as_set (Finished fin) = state_as_set (f_state fin)"
| "global_as_set (Continue g) = state_as_set (g_current g) \<union>
    State ` instruction_result_as_set (g_cctx g) (g_vmstate g) \<union>
    backup_as_set (g_orig g)"

fun iter :: "nat \<Rightarrow> global_state \<Rightarrow> global_state" where
"iter 0 x = x"
| "iter (Suc n) x = next0 (iter n x)"

fun good_context :: "global_state \<Rightarrow> bool" where
"good_context (Continue g) = no_assertion (g_cctx g)"
| "good_context _ = True"

definition global_triple ::
 "global_pred \<Rightarrow> global_pred \<Rightarrow> bool"
where
  "global_triple pre post ==
    \<forall> presult rest. good_context presult \<longrightarrow>
       (pre ** rest) (global_as_set presult) \<longrightarrow>
       (\<exists> k. (post ** rest) (global_as_set (iter k presult)))"

definition lift_pred :: "state_element set_pred \<Rightarrow> global_pred" where
"lift_pred p s = p {x|x. State x \<in> s}"

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

lemma no_reasons :
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

lemma lift_triple :
   "triple {} (pre**continuing) inst post \<Longrightarrow>
    global_triple
      (lift_pred (pre ** continuing ** code inst))
      (lift_pred (post ** code inst))"
apply (auto simp:triple_def global_triple_def)
apply clarsimp

end
