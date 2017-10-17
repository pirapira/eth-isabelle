theory GlobalTriple

imports "./Hoare/Hoare" "./lem/Block"

begin

datatype global_element =
  State "state_element"
| AccountStorage "address" "w256" "w256"
| BackupStorage "address" "w256" "w256"
| SavedStorage "nat" "address" "w256" "w256"
| SavedState "nat" "state_element"

type_synonym global_pred = "global_element set \<Rightarrow> bool"

definition state_as_set :: "(address \<Rightarrow> block_account) \<Rightarrow> global_element set" where
"state_as_set st = {AccountStorage a p e | a p e. e = block_account_storage (st a) p}"

definition backup_as_set :: "(address \<Rightarrow> block_account) \<Rightarrow> global_element set" where
"backup_as_set st = {BackupStorage a p e | a p e. e = block_account_storage (st a) p}"

definition sstorage_as_set :: "nat \<Rightarrow> (address \<Rightarrow> block_account) \<Rightarrow> global_element set" where
"sstorage_as_set n st = {SavedStorage n a p e | a p e. e = block_account_storage (st a) p}"

definition saved_as_set :: "nat \<Rightarrow> (address\<Rightarrow>block_account) \<Rightarrow> constant_ctx \<Rightarrow>
  variable_ctx \<Rightarrow> stack_hint \<Rightarrow> global_element set" where
"saved_as_set n st c v hint =
    sstorage_as_set n st \<union> SavedState n ` contexts_as_set v c"

fun saved_stack_as_set ::
 "(world_state * variable_ctx * constant_ctx * stack_hint) list \<Rightarrow> global_element set" where
"saved_stack_as_set Nil = {}"
| "saved_stack_as_set ((st,v,c,h)#lst) =
     saved_as_set (length lst) st c v h \<union> saved_stack_as_set lst"

fun global_as_set :: "global_state \<Rightarrow> global_element set" where
  "global_as_set (Finished fin) = state_as_set (f_state fin)"
| "global_as_set (Continue g) = state_as_set (g_current g) \<union>
    State ` instruction_result_as_set (g_cctx g) (g_vmstate g) \<union>
    backup_as_set (g_orig g) \<union>
    saved_stack_as_set (g_stack g)"

fun iter :: "network \<Rightarrow> nat \<Rightarrow> global_state \<Rightarrow> global_state" where
"iter net 0 x = x"
| "iter net (Suc n) x = step net (iter net n x)"

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
"lift_pred p s == p {x|x. State x \<in> s} \<and> s \<subseteq> {State x|x. State x \<in> s}"

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

lemma sep_lift_commute :
  "lift_pred (a**b) t = (lift_pred a ** lift_pred b) t"
apply (auto simp:lift_pred_def sep_def)
subgoal for u v 
apply (rule_tac exI[of _ "{State uu| uu. uu \<in> u}"]; auto)
apply (rule_tac exI[of _ "{State uv| uv. uv \<in> v}"]; auto)
apply (case_tac x; auto)
done
subgoal for u v 
apply (rule_tac exI[of _ "{uu| uu. State uu \<in> u}"]; auto)
done
done

lemma state_lifted_aux :
  "State x \<notin> saved_stack_as_set lst"
apply (induction lst)
apply (auto simp:saved_as_set_def  sstorage_as_set_def)
done

lemma state_lifted :
  "State x \<in> global_as_set (Continue res) \<Longrightarrow>
   x \<in> instruction_result_as_set (g_cctx res) (g_vmstate res)"
apply (auto simp:state_as_set_def backup_as_set_def)
apply (auto simp:state_lifted_aux)
done

lemma state_finished :
  "State x \<in> global_as_set (Finished res) \<Longrightarrow>
   False"
apply (auto simp:state_as_set_def)
done

lemma get_continue_elem :
"(lift_pred continuing ** rest) (global_as_set presult) \<Longrightarrow>
 State (ContinuingElm True) \<in> global_as_set presult"
apply (auto simp: sep_def lift_pred_def continuing_def)
done

declare global_as_set.simps [simp del]

lemma continuing_false :
 "ContinuingElm True \<in> contexts_as_set v c \<Longrightarrow> False"
apply (auto simp:contexts_as_set_def constant_ctx_as_set_def
   program_as_set_def variable_ctx_as_set_def
   stack_as_set_def data_sent_as_set_def
   ext_program_as_set_def)
done

lemma continuing_extract:
"(lift_pred continuing ** rest) (global_as_set presult) \<Longrightarrow>
 \<exists>x y. presult = Continue x \<and> g_vmstate x = InstructionContinue y"
apply (cases presult; auto)
apply (case_tac "g_vmstate x1")
apply simp
using get_continue_elem and state_lifted
apply force
subgoal for x1 x31 x32 x33
using get_continue_elem [of rest presult]
  and state_lifted [of "ContinuingElm True" x1]
apply (auto simp: instruction_result_as_set_def)
apply (rule continuing_false; auto)
done
using state_finished and get_continue_elem
apply force
done

lemma lift_triple_finished :
assumes a:"(rest ** lift_pred (continuing ** pre ** code inst))
        (global_as_set (Finished st))"
shows  "False"
proof -
  have b:"lift_pred (continuing ** pre ** code inst) =
    lift_pred continuing ** lift_pred (pre ** code inst)"
   by (auto simp:sep_lift_commute)
  then have
   "rest ** lift_pred (continuing ** pre ** code inst) =
    lift_pred continuing ** (rest ** lift_pred (pre ** code inst))"
  by auto
  then show ?thesis
    by (metis assms get_continue_elem state_finished)
qed

declare contiuning_sep [simp del]
declare sep_continuing_sep [simp del]
declare sep_code [simp del]
declare code_sep [simp del]
declare  sep_code_sep [simp del]
declare sep_sep_code [simp del] 

lemmas cont = contiuning_sep sep_continuing_sep


definition unlift :: "global_state \<Rightarrow> global_element set_pred \<Rightarrow>
  state_element set_pred" where
"unlift st p t = p
  ((global_as_set st - {State x | x. State x \<in> global_as_set st}) \<union>
   {State x | x. x \<in> t})"

lemma leibniz :
 "r s \<Longrightarrow> s = t \<Longrightarrow> r t"
apply auto
done

lemma state_include :
   "x \<in> instruction_result_as_set (g_cctx res) (g_vmstate res) \<Longrightarrow>
   State x \<in> global_as_set (Continue res)"
apply (auto simp: global_as_set.simps)
done

lemma unlift_lemma :
  "v \<subseteq> {State x |x. State x \<in> v} \<Longrightarrow>
   u \<union> v = global_as_set (Continue res) \<Longrightarrow>
   u \<inter> v = {} \<Longrightarrow>
   x \<in> instruction_result_as_set (g_cctx res) (g_vmstate res) \<Longrightarrow>
  State x \<notin> u \<Longrightarrow> State x \<in> v"
using state_include[of x res]
  by blast

lemma unlift_imp :
  "(rest ** lift_pred p) (global_as_set (Continue res)) \<Longrightarrow>
    (unlift (Continue res) rest ** p)
        (instruction_result_as_set (g_cctx res)
          (g_vmstate res))"
apply (auto simp:unlift_def
  lift_pred_def sep_def)
subgoal for u v
apply (rule exI[of _ "{uu | uu. State uu \<in> v}"])
apply clarsimp
apply (rule exI[of _ "{uu | uu. State uu \<in> u}"])
apply auto
apply (rule leibniz [of rest])
apply blast
apply auto
  using state_lifted apply auto[1]
  using state_lifted apply fastforce
using unlift_lemma
apply force
done
done

lemma continuing_env :
"(continuing **  rest)
    (instruction_result_as_set (g_cctx x1)
          (InstructionToEnvironment x31 x32 x33)) \<Longrightarrow>
 False"
  using continuing_false contiuning_sep instruction_result_as_set_def by fastforce

lemma smallest_k :
"program_sem (\<lambda>stopper. ()) c (Suc k)
         (InstructionContinue v) = x \<Longrightarrow>
\<exists>l v2.
   program_sem (\<lambda>stopper. ()) c l
      (InstructionContinue v) = InstructionContinue v2 \<and>
  next_state (\<lambda>stopper. ()) c (InstructionContinue v2) = x"
apply (induction k arbitrary:v)
using program_sem.simps(1) program_sem.simps(2) apply fastforce
subgoal for k v
apply (cases "next_state (\<lambda>stopper. ()) c
        (InstructionContinue v)")
defer
  apply (simp add: program_annotation program_sem.simps(2))
  using program_environment program_sem.simps(2) apply auto[1]
  by (metis program_sem.simps(2))
done

lemma unlift_imp2 :
   "(post ** unlift (Continue x1) rest)
     (instruction_result_as_set (g_cctx x1) (g_vmstate x1)) \<Longrightarrow>
    (rest ** lift_pred post) (global_as_set (Continue x1))"
apply (auto simp:unlift_def
  lift_pred_def sep_def)
subgoal for u v
apply (rule exI[of _ "global_as_set (Continue x1) -
      {State x |x.
       State x
       \<in> global_as_set (Continue x1)} \<union>
      {State x |x. x \<in> v}"])
apply clarsimp
apply (rule exI[of _ "{State uu | uu. uu \<in> u}"])
apply auto
  using state_include apply auto[1]
  using state_include apply auto[1]
  using state_lifted by auto
done

lemma change_vmstate :
 "global_as_set (Continue (x\<lparr>g_vmstate := res\<rparr>)) =
  (global_as_set (Continue x) -
   {State u | u. u \<in> instruction_result_as_set
     (g_cctx x) (g_vmstate x)}) \<union>
  {State u | u. u \<in> instruction_result_as_set
     (g_cctx x) res}"
apply (auto simp:rw global_as_set.simps)
  apply (metis Int_iff global0.select_convs(3) global0.select_convs(4) global0.select_convs(6) global_as_set.simps(2) inf_sup_absorb state_lifted)
  apply (metis Un_iff global0.select_convs(1) global0.select_convs(4) global0.select_convs(6)  global_as_set.simps(2) state_lifted)
  by (simp add: state_lifted_aux)


lemma unlift_imp2_gen :
   "(post ** unlift (Continue x1) rest)
     (instruction_result_as_set (g_cctx x1) res) \<Longrightarrow>
    (rest ** lift_pred post) (global_as_set (Continue (x1\<lparr> g_vmstate := res \<rparr>)))"
apply (auto simp:unlift_def
  lift_pred_def sep_def)
subgoal for u v
apply (rule exI[of _ "global_as_set (Continue x1) -
      {State x |x.
       State x
       \<in> global_as_set (Continue x1)} \<union>
      {State x |x. x \<in> v}"])
apply clarsimp
apply (rule exI[of _ "{State uu | uu. uu \<in> u}"])
apply auto
apply (simp add:change_vmstate)
  apply auto[1]
  using state_include apply auto[1]
apply (simp add:change_vmstate)
  apply auto[1]
apply (simp add:change_vmstate)
  apply auto[1]
apply (simp add:change_vmstate)
  using state_lifted by auto

done

lemma iter_simp: "next0 (iter k st) = iter k (next0 st)"
apply (induction k arbitrary:st)
apply auto
done

lemma do_iter :
  "g_vmstate x1 = InstructionContinue v \<Longrightarrow>
   program_sem (\<lambda>s. ()) (g_cctx x1) l
      (InstructionContinue v) =
      InstructionContinue v2 \<Longrightarrow>
   iter (Suc l) (Continue x1) = (Continue (x1\<lparr>
       g_vmstate :=  next_state (\<lambda>s. ()) (g_cctx x1)
      (InstructionContinue v2)
 \<rparr>))"
apply (induction l arbitrary: x1 v)
apply (auto simp:next0_def program_sem.simps)[1]
subgoal for l x1 v
apply (subst (asm) program_sem.simps)
apply (cases "next_state (\<lambda>s. ()) (g_cctx x1)
       (InstructionContinue v)")
defer
apply (auto)[1]
  apply (simp add: program_annotation)
  apply (simp add: program_environment)
apply (subst iter.simps)
apply (subst iter_simp)
apply (auto simp:next0_def)
done
done

lemma smallest_k2 :
"\<exists>l v2.
   program_sem (\<lambda>stopper. ()) c l
      (InstructionContinue v) = InstructionContinue v2 \<and>
  next_state (\<lambda>stopper. ()) c (InstructionContinue v2) =
  program_sem (\<lambda>stopper. ()) c (Suc k) (InstructionContinue v)"
using smallest_k
apply force
done

lemma lift_triple :
   "triple {} (pre**continuing) inst post \<Longrightarrow>
    global_triple
      (lift_pred (pre ** continuing ** code inst))
      (lift_pred (post ** code inst))"
apply (auto simp:global_triple_def no_reasons)
apply (case_tac presult)
defer
using lift_triple_finished
apply fastforce
subgoal for presult rest x1
apply (auto simp:triple_def)

apply (drule spec[where x="g_cctx x1"])
apply clarsimp
apply (drule spec2[where x="g_vmstate x1" and y = "unlift (Continue x1) rest"])
apply auto
using unlift_imp [of rest "continuing ** pre ** code inst" x1]
apply auto
apply (drule spec[where x= "\<lambda>x.()"])
apply auto
defer
apply (cases "g_vmstate x1")
apply auto
using no_reasons
apply force
using contiuning_sep apply auto[1]
using continuing_env apply force
apply (cases "g_vmstate x1")
defer
using contiuning_sep apply auto[1]
using continuing_env apply force
subgoal for k v
apply (cases k)
apply (rule exI[of _ k])
apply (auto simp:program_sem.simps)[1]
using unlift_imp2 apply force
subgoal for ka
using smallest_k2 [of "g_cctx x1" v ka]
apply auto
subgoal for l v2
apply (rule exI[of _ "Suc l"])
using do_iter [of x1 v l v2]
apply auto
using unlift_imp2_gen
apply force
done
done
done
done
done


end
