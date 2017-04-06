(*
   Copyright 2017 Sidney Amani
   Copyright 2017 Maksym Bortin

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
theory EvmFacts
  imports "Hoare"
begin

lemmas gas_simps = Gverylow_def Glow_def Gmid_def Gbase_def Gzero_def Glogtopic_def 
    Gsha3word_def Gsha3_def Gextcode_def Gcopy_def Gblockhash_def Gexpbyte_def Gexp_def
    Gbalance_def Gsload_def Gsreset_def Gsset_def Gjumpdest_def Ghigh_def
    Glogdata_def  Glog_def Gcreate_def Ccall_def 
    Cgascap_def Cextra_def Gnewaccount_def Cxfer_def Cnew_def
    Gcall_def Gcallvalue_def 

termination log256floor by lexicographic_order

lemma log256floor_ge_0:
  "0 \<le> log256floor s"
  apply (induct s rule: log256floor.induct)
  subgoal for x
    by (case_tac "\<not> x \<le> 255")
       (clarsimp simp: log256floor.simps)+
  done
declare  log256floor.simps[simp del ]

lemma Cextra_gt_0:
  "0 < Cextra  a b c"
  by (simp add:  gas_simps)

lemma Cgascap_gt_0:
  "f \<ge> 0 \<Longrightarrow> 0 \<le> Cgascap a b c d e f + f"
apply (auto simp add:  gas_simps L_def min_def)
done

lemma Ccall_gt_0:
  "memu \<ge> 0 \<Longrightarrow>  0 < Ccall s0 s1 s2 recipient_empty
            remaining_gas blocknumber memu + memu"

  unfolding Ccall_def
apply (auto)
  apply (simp add: Cextra_gt_0 add.commute add_nonneg_pos)
  by (metis Cextra_gt_0 Cgascap_gt_0 add.commute add.left_commute add_strict_increasing)

lemma Csuicide_gt_0:
  "Gsuicide blocknumber \<noteq> 0 \<Longrightarrow> 0 < Csuicide recipient_empty blocknumber"
  unfolding Csuicide_def
  by (auto split: if_splits
           simp add: gas_simps Gsuicide_def)

lemma thirdComponentOfC_gt_0:
  "i \<noteq> Misc STOP \<Longrightarrow> i \<noteq> Misc RETURN \<Longrightarrow> (\<forall>v. i \<noteq> Unknown v) \<Longrightarrow>
   i = Misc SUICIDE \<longrightarrow> Gsuicide blocknumber \<noteq> 0 \<Longrightarrow>
   i = Misc DELEGATECALL \<longrightarrow> blocknumber \<ge> homestead_block  \<Longrightarrow>
   memu \<ge> 0 \<Longrightarrow>
  0 < thirdComponentOfC i s0 s1 s2 s3 recipient_empty orig_val
      new_val remaining_gas blocknumber memu + memu"
  unfolding thirdComponentOfC_def
  apply (case_tac i ; simp add: gas_simps )
            apply fastforce
           apply (case_tac x2; simp add: gas_simps)
          apply (case_tac x3; simp add: gas_simps )
         apply (case_tac x4 ; simp add: gas_simps)
         using log256floor_ge_0[where s="uint s1"]
                 apply (simp add: )
              apply (clarsimp; simp add: word_less_def word_neq_0_conv)
                apply (case_tac x5; simp add: gas_simps)
              apply (case_tac x7; simp add: gas_simps)
                apply (case_tac "s2 = 0" ; auto simp: word_less_def word_neq_0_conv)
                apply (case_tac "s2 = 0" ; auto simp: word_less_def word_neq_0_conv)
              apply (case_tac "s3 = 0" ; auto simp: word_less_def word_neq_0_conv)
            apply (case_tac x8; simp add: gas_simps Csstore_def)
            apply (case_tac x9; simp add: gas_simps Csstore_def)
           apply (case_tac x10; simp add: gas_simps Csstore_def)
          apply ( case_tac x12; case_tac "s1 = 0"; 
             simp add: gas_simps word_less_def word_neq_0_conv)
         apply (clarsimp split: misc_inst.splits)
         apply (rule conjI, clarsimp simp add: gas_simps L_def)
         apply (rule conjI)
          apply (auto simp add: Ccall_gt_0)+
         apply (smt Csuicide_gt_0)
         apply (smt Csuicide_gt_0)
done

lemma Cmem_lift:
  "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> Cmem x \<le> Cmem y"
  apply (simp add: Cmem_def Gmemory_def)
  apply (case_tac "x = y")
   apply clarsimp
  apply (drule (1) order_class.le_neq_trans)
  apply simp
  apply (rule add_mono, simp)
  apply (rule zdiv_mono1[rotated], simp)
  apply (rule mult_mono ; simp)
  done

lemma thirdComponentOfC_gt_0_massaged :
  "i \<noteq> Misc STOP \<Longrightarrow> i \<noteq> Misc RETURN \<Longrightarrow> (\<forall>v. i \<noteq> Unknown v) \<Longrightarrow>
   i = Misc SUICIDE \<longrightarrow> Gsuicide blocknumber \<noteq> 0 \<Longrightarrow>
   i = Misc DELEGATECALL \<longrightarrow> blocknumber \<ge> homestead_block  \<Longrightarrow>
   x \<ge> y \<Longrightarrow>
  0 < x - y + thirdComponentOfC i s0 s1 s2 s3 recipient_empty orig_val
      new_val remaining_gas blocknumber (x-y)"
  by (metis add.commute diff_ge_0_iff_ge thirdComponentOfC_gt_0)

lemma vctx_memory_usage_never_decreases:
  "vctx_memory_usage var \<le> new_memory_consumption inst var"
  by (case_tac inst)
     (rename_tac x, case_tac x; auto simp add: new_memory_consumption.simps M_def)+

lemma meter_gas_gt_0:
  " inst \<noteq> Misc STOP \<Longrightarrow>
    inst \<noteq> Misc RETURN \<Longrightarrow>
   blocknumber = (unat (block_number (vctx_block var))) \<Longrightarrow>
   inst = Misc SUICIDE \<longrightarrow> Gsuicide blocknumber \<noteq> 0 \<Longrightarrow>
   inst = Misc DELEGATECALL \<longrightarrow> blocknumber \<ge> homestead_block  \<Longrightarrow>
    inst \<notin> range Unknown \<Longrightarrow>
   0 \<le> vctx_memory_usage var \<Longrightarrow>
   0 < meter_gas inst var const"
  using Cmem_lift[OF _ vctx_memory_usage_never_decreases[where inst=inst and var=var]]
  apply (simp add: C_def meter_gas_def)
apply (rule thirdComponentOfC_gt_0_massaged)
apply auto
done

(*
lemma instruction_sem_not_continuing:
  "\<lbrakk> inst \<in> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown \<rbrakk> \<Longrightarrow>
\<forall>v. instruction_sem var const inst \<noteq> InstructionContinue v"
  apply (case_tac inst; clarsimp simp: instruction_sem_def instruction_failure_result_def subtract_gas.simps)
  subgoal for opcode v
   apply (case_tac opcode; simp add: ret_def suicide_def image_def stop_def instruction_sem_def instruction_failure_result_def subtract_gas.simps split:list.splits)
   done
  done

lemma instruction_sem_continuing:
  "\<lbrakk> instruction_sem var const inst = InstructionContinue v \<rbrakk> \<Longrightarrow>
inst \<notin> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown"
  apply (case_tac inst; clarsimp simp: instruction_sem_def instruction_failure_result_def subtract_gas.simps)
  subgoal for opcode
   apply (case_tac opcode; simp add: ret_def suicide_def image_def stop_def instruction_sem_def instruction_failure_result_def subtract_gas.simps split:list.splits)
   done
  done
*)


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
  using context_cont1 not_cont_insert by presburger
then have "(?base ** not_continuing)
   (insert (ContinuingElm False) ?set-{ContractActionElm (ContractFail lst)})"
  by (metis (full_types) Diff_empty Diff_insert2 context_cont context_cont1 contexts_as_set_def insert_minus state_element.distinct(685))
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
  vctx_pop_stack_def vctx_advance_pc_def
blockedInstructionContinue_def blocked_jump_def

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
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2a"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
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
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2a"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: Let_def instruction_sem_simps  split: pc_inst.splits option.splits)
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
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2a"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: Let_def instruction_sem_simps  split: pc_inst.splits option.splits)
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

definition all_stack :: "state_element set_pred" where
"all_stack s = (\<exists>t. s = stack_as_set t)"

definition all_but_gas :: "state_element set_pred" where
"all_but_gas s = (\<exists>c v.
   s = contexts_as_set v c - {GasElm (vctx_gas v)})"

lemma maximality_stack_aux :
   "stack_as_set s1 \<subseteq> stack_as_set s2 \<Longrightarrow>
    i < length s1 \<Longrightarrow>
    rev s1!i = rev s2!i"
apply(auto simp add:context_rw)
apply blast
done

lemma maximality_stack_length :
   "stack_as_set s1 \<subseteq> stack_as_set s2 \<Longrightarrow>
    length s1 = length s2"
by (auto simp add:context_rw)

lemma list_eq :
   "length l1 = length l2 \<Longrightarrow>
    (\<forall>i. i < length l1 \<longrightarrow> l1!i = l2!i) \<Longrightarrow>
    rev l1 = rev l2"
apply (rule List.nth_equalityI)
apply auto
  by (simp add: Suc_diff_Suc rev_nth)


lemma maximality_stack_aux2 :
 "stack_as_set s1 \<subseteq> stack_as_set s2 \<Longrightarrow>
  rev s1 = rev s2"
apply (rule list_eq)
using maximality_stack_length
apply force
apply auto
subgoal for i
using maximality_stack_aux [of s1 s2 "length s2 - i -1"]
  and maximality_stack_length [of s1 s2]
proof -
  assume a1: "i < length s1"
  assume a2: "stack_as_set s1 \<subseteq> stack_as_set s2"
  have f3: "\<not> stack_as_set s1 \<subseteq> stack_as_set s2 \<or> length s1 = length s2"
    by (metis \<open>stack_as_set s1 \<subseteq> stack_as_set s2 \<Longrightarrow> length s1 = length s2\<close>)
  have f4: "length s2 - i - 1 = length s2 - Suc i"
    using diff_Suc_eq_diff_pred diff_commute by presburger
  have "0 < length s2"
    using f3 a2 a1 by linarith
  then have "rev s1 ! (length s2 - i - 1) = rev s2 ! (length s2 - i - 1)"
    using f4 f3 a2 \<open>\<lbrakk>stack_as_set s1 \<subseteq> stack_as_set s2; length s2 - i - 1 < length s1\<rbrakk> \<Longrightarrow> rev s1 ! (length s2 - i - 1) = rev s2 ! (length s2 - i - 1)\<close> diff_Suc_less by presburger
  then show ?thesis
    using f4 f3 a2 a1 by (metis (no_types) nth_rev_alt)
qed
done

lemma maximality_stack :
 "stack_as_set s1 \<subseteq> stack_as_set s2 \<Longrightarrow>
  s1 = s2"
using maximality_stack_aux2
  by auto

lemma stack_height_at_context :
 "StackHeightElm x \<in> contexts_as_set v2 c2 \<Longrightarrow>
  StackHeightElm x \<in> stack_as_set (vctx_stack v2)"
apply(simp add:context_rw)
done

lemma stack_elem_at_context :
 "StackElm (x,y) \<in> contexts_as_set v2 c2 \<Longrightarrow>
  StackElm (x,y) \<in> stack_as_set (vctx_stack v2)"
apply(simp add:context_rw)
done

lemma stack_at_context :
 "stack_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  stack_as_set s1 \<subseteq> stack_as_set (vctx_stack v2)"
apply auto
apply (case_tac x)
apply auto
using stack_height_at_context
apply force
using stack_elem_at_context
apply force
apply(auto simp add:context_rw)
done

lemma stack_from_context :
 "stack_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_stack v2 = s1"
using stack_at_context [of s1 v2 c2]
  and maximality_stack [of s1 "vctx_stack v2"]
by force

lemma maximality_data_aux :
   "data_sent_as_set s1 \<subseteq> data_sent_as_set s2 \<Longrightarrow>
    i < length s1 \<Longrightarrow>
    s1!i = s2!i"
apply(auto simp add:context_rw)
apply blast
done

lemma maximality_data_length :
   "data_sent_as_set s1 \<subseteq> data_sent_as_set s2 \<Longrightarrow>
    length s1 = length s2"
by (auto simp add:context_rw)

lemma maximality_data_sent :
 "data_sent_as_set s1 \<subseteq> data_sent_as_set s2 \<Longrightarrow>
  s1 = s2"
apply (rule List.nth_equalityI)
using maximality_data_length
apply force
apply auto
subgoal for i
using maximality_data_aux [of s1 s2 i]
apply simp
done
done

lemma data_size_at_context :
 "SentDataLengthElm x \<in> contexts_as_set v2 c2 \<Longrightarrow>
  SentDataLengthElm x \<in> data_sent_as_set (vctx_data_sent v2)"
apply(simp add:context_rw)
done

lemma data_elem_at_context :
 "SentDataElm (x,y) \<in> contexts_as_set v2 c2 \<Longrightarrow>
  SentDataElm (x,y) \<in> data_sent_as_set (vctx_data_sent v2)"
apply(simp add:context_rw)
done

lemma data_at_context :
 "data_sent_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  data_sent_as_set s1 \<subseteq> data_sent_as_set (vctx_data_sent v2)"
apply (auto)
apply (case_tac x)
apply (auto simp:data_size_at_context data_elem_at_context)
apply(auto simp add:context_rw)
done

lemma data_from_context :
 "data_sent_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_data_sent v2 = s1"
using data_at_context [of s1 v2 c2]
  and maximality_data_sent [of s1 "vctx_data_sent v2"]
by force


(*
lemma maximality :
   "contexts_as_set v1 c1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
    a \<in> contexts_as_set v2 c2 \<Longrightarrow>
    a \<in> contexts_as_set v1 c1"
apply(simp add:context_rw)
apply clarsimp
*)

end
