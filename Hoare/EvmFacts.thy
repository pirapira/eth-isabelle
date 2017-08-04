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

declare memory_as_set_def [simp del]
declare storage_as_set_def [simp del]
declare balance_as_set_def [simp del]
declare log_as_set_def [simp del]


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
       (clarsimp)+
  done
declare  log256floor.simps[simp del ]

lemma Cextra_gt_0:
  "0 < Cextra  a b c"
  by (simp add:  gas_simps)

lemma L_compare : "x \<ge> 0 \<Longrightarrow> L x \<ge> 0"
by (simp add:L_def)

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
  apply (metis Cextra_gt_0 Cgascap_gt_0 add.commute add.left_commute add_strict_increasing)
  by (simp add: Cextra_gt_0 add.commute add_nonneg_pos)

lemma Ccall_ge_0:
  "memu \<ge> 0 \<Longrightarrow>  0 \<le> Ccall s0 s1 s2 recipient_empty
            remaining_gas blocknumber memu + memu"
using Ccall_gt_0
  by (simp add: dual_order.order_iff_strict)


lemma Csuicide_gt_0:
  "at_least_eip150 net \<Longrightarrow> 0 < Csuicide recipient_empty net"
  unfolding Csuicide_def
  by (auto split: if_splits
           simp add: gas_simps Gsuicide_def)

lemma thirdComponentOfC_gt_0:
  "i \<noteq> Misc STOP \<Longrightarrow> i \<noteq> Misc RETURN \<Longrightarrow> (\<forall>v. i \<noteq> Unknown v) \<Longrightarrow>
   i = Misc SUICIDE \<longrightarrow> at_least_eip150 net \<Longrightarrow>
   i = Misc DELEGATECALL \<longrightarrow> \<not> (before_homestead net)  \<Longrightarrow>
   memu \<ge> 0 \<Longrightarrow>
  0 < thirdComponentOfC i s0 s1 s2 s3 recipient_empty orig_val
      new_val remaining_gas net memu + memu"
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
          apply (auto simp add: Ccall_gt_0 at_least_eip150.simps)+
         apply (smt Csuicide_gt_0)
         apply (smt Csuicide_gt_0)
done

lemma thirdComponentOfC_ge_0:
  "memu \<ge> 0 \<Longrightarrow>
  0 \<le> thirdComponentOfC i s0 s1 s2 s3 recipient_empty orig_val
      new_val remaining_gas net memu + memu"
  unfolding thirdComponentOfC_def
  apply (case_tac i ; simp add: gas_simps )
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
          apply (auto simp add: Ccall_ge_0 Gcreate_def Gzero_def
                Csuicide_def Gsuicide_def Gnewaccount_def)+
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

(*
lemma thirdComponentOfC_gt_0_massaged :
  "i \<noteq> Misc STOP \<Longrightarrow> i \<noteq> Misc RETURN \<Longrightarrow> (\<forall>v. i \<noteq> Unknown v) \<Longrightarrow>
   i = Misc SUICIDE \<longrightarrow> at_least_eip150 net \<Longrightarrow>
   i = Misc DELEGATECALL \<longrightarrow> \<not> before_homestead net \<Longrightarrow>
   x \<ge> y \<Longrightarrow>
  0 < x - y + thirdComponentOfC i s0 s1 s2 s3 recipient_empty orig_val
      new_val remaining_gas net (x-y)"
  by (metis add.commute diff_ge_0_iff_ge thirdComponentOfC_gt_0)
*)

lemma vctx_memory_usage_never_decreases:
  "orig \<le> new_memory_consumption inst orig s0 s1 s2 s3 s4 s5 s6"
  by (case_tac inst)
     (rename_tac x, case_tac x; auto simp add: new_memory_consumption.simps M_def)+

lemma obvious_principle :
"0 < (t::int) + (m1-m2) \<Longrightarrow>
 m1 \<ge> m2 \<Longrightarrow>
 m2 \<ge> 0 \<Longrightarrow>
 0 < m1 - m2 + t"
by auto

lemma Cmem_zero : "Cmem 0 = 0"
by (auto simp:Cmem_def)

lemma meter_gas_gt_0:
  " inst \<noteq> Misc STOP \<Longrightarrow>
    inst \<noteq> Misc RETURN \<Longrightarrow>
   inst = Misc SUICIDE \<longrightarrow> at_least_eip150 net \<Longrightarrow>
   inst = Misc DELEGATECALL \<longrightarrow> \<not>before_homestead net  \<Longrightarrow>
    inst \<notin> range Unknown \<Longrightarrow>
   0 \<le> vctx_memory_usage var \<Longrightarrow>
   0 < meter_gas inst var const net"
  apply (simp add: C_def meter_gas_def)
apply (rule obvious_principle)
apply (rule thirdComponentOfC_gt_0)
apply simp
apply simp
apply force
apply simp
apply simp
using Cmem_lift vctx_memory_usage_never_decreases
apply force
using Cmem_lift vctx_memory_usage_never_decreases
apply force
using Cmem_lift Cmem_zero
apply force
done

lemma obvious_principle2 :
"0 \<le> (t::int) + (m1-m2) \<Longrightarrow>
 m1 \<ge> m2 \<Longrightarrow>
 m2 \<ge> 0 \<Longrightarrow>
 0 \<le> m1 - m2 + t"
by auto

lemma meter_gas_ge_0:
  "0 \<le> vctx_memory_usage var \<Longrightarrow>
   0 \<le> meter_gas inst var const net"
  apply (simp add: C_def meter_gas_def)
apply (rule obvious_principle2)
apply (rule thirdComponentOfC_ge_0)
using Cmem_lift vctx_memory_usage_never_decreases
apply force
using Cmem_lift vctx_memory_usage_never_decreases
apply force
using Cmem_lift Cmem_zero
apply force
done

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

notation sep_add (infixr "\<or>*" 59)

lemma sep_add_assoc [simp]: "((a \<or>* b) \<or>* c) = (a \<or>* b \<or>* c)"
  by (simp add: sep_add_def)

lemma sep_add_commute [simp]: "(a \<or>* b)= (b \<or>* a)"
 by (simp add: sep_add_def) blast

definition never :: "'a set_pred" where
"never == (\<lambda>s. False)"

lemma sep_add_never [simp] : "r \<or>* never = r"
by (simp add: never_def sep_add_def)

(*
lemma sep_add_distr [simp] : "a ** (b \<or>* c) == (a**b) \<or>* (a**c)"
apply (simp add: sep_add_def sep_conj_def sep_distinct_def)
apply blast
*)

definition action ::
   "(contract_action \<Rightarrow> bool) \<Rightarrow> state_element set_pred" where
"action p s = (\<exists>x. {ContractActionElm x} = s \<and> p x)"

definition failing :: "state_element set_pred" where
"failing = action (\<lambda>y. \<exists>x. ContractFail x = y)"

definition returning :: "state_element set_pred" where
"returning = action (\<lambda>y. \<exists>x. ContractReturn x = y)"

definition destructing :: "state_element set_pred" where
"destructing = action (\<lambda>y. \<exists>x. ContractSuicide x = y)"

definition calling :: "state_element set_pred" where
"calling = action (\<lambda>y. \<exists>x. ContractCall x = y)"

definition creating :: "state_element set_pred" where
"creating = action (\<lambda>y. \<exists>x. ContractCreate x = y)"

definition delegating :: "state_element set_pred" where
"delegating = action (\<lambda>y. \<exists>x. ContractDelegateCall x = y)"

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
"instruction_sem v c aa net \<noteq>
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
   (next_state stopper c net (InstructionContinue v)) = False"
by (auto simp:failed_for_reasons_def)

lemma program_environment :
"program_sem stopper c n net (InstructionToEnvironment a b d) =
 (InstructionToEnvironment a b d)"
by (induction n, auto simp:program_sem.simps next_state_def)


lemma no_reasons [simp] :
   "failed_for_reasons {}
   (program_sem stopper c n net (InstructionContinue v)) = False"
apply (induction n arbitrary:v)
apply (auto simp add:program_sem.simps failed_for_reasons_def
  no_reasons_next)
done

(*
lemmas context_rw = contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def data_sent_as_set_def ext_program_as_set_def
      account_balance_as_set_def
*)

(*
lemma not_cont_insert :
 "x (s-{ContinuingElm False}) \<Longrightarrow>
  (x ** not_continuing) (insert (ContinuingElm False) s)"
apply(auto simp add:rw sep_conj_def  not_continuing_def all_def
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
         action_def failing_def some_gas_def code_def gas_pred_def context_rw)
done

lemma some_gas_in_context :
"(rest ** gas_pred g) s \<Longrightarrow>
(rest ** some_gas ) s"
apply(auto simp add:rw sep_def  not_continuing_def all_def
         failing_def some_gas_def code_def gas_pred_def context_rw)
done

*)

lemma meter_gas_check :
  "\<not> meter_gas a x1 co_ctx net \<le> vctx_gas x1 \<Longrightarrow>
   check_resources x1 co_ctx (vctx_stack x1) a net \<Longrightarrow>
   False"
by (simp add:check_resources_def)

lemmas instruction_sem_simps =
  rw sha3_def vctx_update_storage_def
  vctx_pop_stack_def vctx_advance_pc_def
vctx_memory_usage_never_decreases

lemma env_meter_gas :
"instruction_sem v1 c inst net =
 InstructionToEnvironment act v2 x33 \<Longrightarrow>
 vctx_gas v2 = vctx_gas v1 - meter_gas inst v1 c net"
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
"instruction_sem v1 c inst net =
 InstructionContinue v2 \<Longrightarrow>
 vctx_gas v2 = vctx_gas v1 - meter_gas inst v1 c net"
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

lemma memu_good :
"instruction_sem v1 c inst net = InstructionContinue v2 \<Longrightarrow>
 vctx_memory_usage v2 \<ge> vctx_memory_usage v1"
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

lemma memu_good_env :
"instruction_sem v1 c inst net = InstructionToEnvironment act v2 zz \<Longrightarrow>
 vctx_memory_usage v2 \<ge> vctx_memory_usage v1"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; 
          clarsimp simp: instruction_sem_simps
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


lemma call_instruction :
"instruction_sem v c inst net =
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

lemma create_instruction :
"instruction_sem v c inst net =
 InstructionToEnvironment (ContractCreate args) x32 x33 \<Longrightarrow>
 inst = Misc CREATE"
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


lemma continue_instruction :
 "instruction_sem v c inst net = InstructionContinue v2 \<Longrightarrow>
  inst \<noteq> Misc STOP \<and> inst \<noteq> Misc RETURN \<and>
  inst \<noteq> Misc SUICIDE \<and> inst \<noteq> Misc DELEGATECALL \<and>
  inst \<notin> range Unknown"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; clarsimp simp: rw split:list.splits)
apply (case_tac "x13"; clarsimp simp: instruction_sem_simps
    split: pc_inst.splits option.splits list.splits if_splits)
done

lemma delegatecall_instruction :
"instruction_sem v c inst net =
 InstructionToEnvironment (ContractDelegateCall args) x32 x33 \<Longrightarrow>
 inst = Misc DELEGATECALL \<and> \<not> before_homestead net"
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

lemma delegatecall_decr_gas :
   assumes a:"instruction_sem v1 co_ctx a net =
       InstructionToEnvironment (ContractDelegateCall x1a)
        v2 x33"
   and good:"vctx_memory_usage v1 \<ge> 0"
  shows  "vctx_gas v1 > vctx_gas v2"
proof -
  have inst: "a = Misc DELEGATECALL \<and>
 \<not> before_homestead net"
   using delegatecall_instruction and a by force
  then have "meter_gas a v1 co_ctx net > 0"
   using good and meter_gas_gt_0 by blast
  then show ?thesis using env_meter_gas and a by force
qed

lemma create_decr_gas :
   assumes a:"instruction_sem v1 co_ctx a net =
       InstructionToEnvironment (ContractCreate x1a)
        v2 x33"
   and good:"vctx_memory_usage v1 \<ge> 0"
  shows  "vctx_gas v1 > vctx_gas v2"
proof -
  have inst: "a = Misc CREATE"
   using create_instruction and a by force
  then have "meter_gas a v1 co_ctx net > 0"
   using good and meter_gas_gt_0 by blast
  then show ?thesis using env_meter_gas and a by force
qed

lemma call_decr_gas :
   assumes a:"instruction_sem v1 co_ctx a net =
       InstructionToEnvironment (ContractCall x1a)
        v2 x33"
   and good:"vctx_memory_usage v1 \<ge> 0"
  shows  "vctx_gas v1 > vctx_gas v2"
proof -
  have inst: "a = Misc CALL \<or> a = Misc CALLCODE"
   using call_instruction and a by force
  then have "meter_gas a v1 co_ctx net > 0"
   using good and meter_gas_gt_0 by blast
  then show ?thesis using env_meter_gas and a by force
qed

lemma continue_decr_gas :
   assumes a:"instruction_sem v1 co_ctx a net = InstructionContinue v2"
   and good:"vctx_memory_usage v1 \<ge> 0"
  shows  "vctx_gas v1 > vctx_gas v2"
proof -
  have "meter_gas a v1 co_ctx net > 0"
   using a and good and meter_gas_gt_0 and continue_instruction
   by auto
  then show ?thesis using continue_meter_gas and a by force
qed

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

(* reconstruct memory *)

lemma maximality_memory :
 "memory_as_set m1 \<subseteq> memory_as_set m2 \<Longrightarrow>
  m1 = m2"
apply(auto simp add:context_rw)
done

lemma memory_at_context :
 "memory_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  memory_as_set s1 \<subseteq> memory_as_set (vctx_memory v2)"
apply(auto simp add:context_rw)
done

lemma memory_from_context :
 "memory_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_memory v2 = s1"
using memory_at_context [of s1 v2 c2]
  and maximality_memory [of s1 "vctx_memory v2"]
by force

(* reconstruct storage *)

lemma maximality_storage :
 "storage_as_set m1 \<subseteq> storage_as_set m2 \<Longrightarrow>
  m1 = m2"
apply(auto simp add:context_rw)
done

lemma storage_at_context :
 "storage_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  storage_as_set s1 \<subseteq> storage_as_set (vctx_storage v2)"
apply(auto simp add:context_rw)
done

lemma storage_from_context :
 "storage_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_storage v2 = s1"
using storage_at_context [of s1 v2 c2]
  and maximality_storage [of s1 "vctx_storage v2"]
by force

(* balance *)

lemma maximality_balance :
 "balance_as_set m1 \<subseteq> balance_as_set m2 \<Longrightarrow>
  m1 = m2"
apply(auto simp add:context_rw)
done

lemma balance_at_context :
 "balance_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  balance_as_set s1 \<subseteq> balance_as_set (vctx_balance v2)"
apply(auto simp add:context_rw)
done

lemma balance_from_context :
 "balance_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_balance v2 = s1"
  by (metis balance_at_context maximality_balance)

(* block info *)

lemma maximality_block :
 "blockhash_as_elm m1 \<subseteq> blockhash_as_elm m2 \<Longrightarrow>
  m1 = m2"
apply(auto simp add:context_rw)
done

lemma block_at_context :
 "blockhash_as_elm s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  blockhash_as_elm s1 \<subseteq>
    blockhash_as_elm (block_blockhash (vctx_block v2))"
apply(auto simp add:context_rw)
done

lemma block_from_context :
 "blockhash_as_elm s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  block_blockhash (vctx_block v2) = s1"
using block_at_context [of s1 v2 c2]
 and maximality_block [of s1 " block_blockhash (vctx_block v2)"]
by force

(* program *)

definition program_inst :: "program \<Rightarrow> int \<Rightarrow> inst" where
"program_inst p i =
   (case program_content p i of None \<Rightarrow> Misc STOP | Some i \<Rightarrow> i)"

definition program_as_set2 :: "program \<Rightarrow> state_element set" where
"program_as_set2 p =
 { CodeElm (pos, i) | pos i. program_inst p pos = i  }"

lemma maximality_program_aux :
 "program_as_set2 m1 \<subseteq> program_as_set2 m2 \<Longrightarrow>
  program_inst m1 = program_inst m2"
apply(auto simp add:context_rw program_as_set2_def)
done

lemma program_as_set_eq : "program_as_set p = program_as_set2 p"
apply (auto simp:program_as_set_def
  program_as_set2_def program_inst_def split:option.split)
done

lemma maximality_program :
 "program_as_set m1 \<subseteq> program_as_set m2 \<Longrightarrow>
  program_inst m1 = program_inst m2"
by (auto simp:program_as_set_eq maximality_program_aux)

lemma program_at_context :
 "program_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  program_as_set s1 \<subseteq> program_as_set (cctx_program c2)"
apply(auto simp add:context_rw)
apply blast
apply force
done

lemma program_from_context :
 "program_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  program_inst (cctx_program c2) = program_inst s1"
  by (metis program_at_context maximality_program)

lemma program_inst_same :
   "program_inst p1 = program_inst p2 \<Longrightarrow>
    program_as_set p1 = program_as_set p2"
apply (auto simp:program_as_set_def
  program_as_set2_def program_inst_def split:option.split)
  apply (metis option.case_eq_if option.expand option.sel option.simps(3) program_inst_def)
  apply (metis option.case_eq_if option.sel option.simps(3) program_inst_def)
  apply (metis option.case_eq_if  option.sel option.simps(3) program_inst_def)
  apply (metis option.case_eq_if option.expand option.sel option.simps(3) program_inst_def)
  apply (metis option.case_eq_if  option.sel option.simps(3) program_inst_def)
  apply (metis option.case_eq_if  option.sel option.simps(3) program_inst_def)
done

(* reconstruct logs *)

lemma maximality_log_aux :
   "log_as_set s1 \<subseteq> log_as_set s2 \<Longrightarrow>
    i < length s1 \<Longrightarrow>
    rev s1!i = rev s2!i"
apply(auto simp add:context_rw)
apply blast
done

lemma maximality_log_length :
   "log_as_set s1 \<subseteq> log_as_set s2 \<Longrightarrow>
    length s1 = length s2"
by (auto simp add:context_rw)

lemma maximality_log :
 "log_as_set s1 \<subseteq> log_as_set s2 \<Longrightarrow>
  s1 = s2"
using maximality_log_aux [of s1 s2]
  and maximality_log_length [of s1 s2]
  and list_eq [of s1 s2]
  by (metis length_rev nth_equalityI rev_is_rev_conv)

lemma log_length_at_context :
 "LogNumElm x \<in> contexts_as_set v2 c2 \<Longrightarrow>
  LogNumElm x \<in> log_as_set (vctx_logs v2)"
apply(simp add:context_rw)
done

lemma log_elem_at_context :
 "LogElm (x,y) \<in> contexts_as_set v2 c2 \<Longrightarrow>
  LogElm (x,y) \<in> log_as_set (vctx_logs v2)"
apply(simp add:context_rw)
done

lemma log_at_context_aux :
 "log_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  x \<in> log_as_set s1 \<Longrightarrow>
  x \<in> log_as_set (vctx_logs v2)"
apply (case_tac x)
apply (auto simp:log_length_at_context log_elem_at_context)
apply(auto simp add:context_rw)
done

lemma log_at_context :
 "log_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  log_as_set s1 \<subseteq> log_as_set (vctx_logs v2)"
using log_at_context_aux
apply (auto)
done

lemma log_from_context :
 "log_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_logs v2 = s1"
using log_at_context [of s1 v2 c2]
  and maximality_log [of s1 "vctx_logs v2"]
by force

(* external programs *)

lemma maximal_ext_length :
   "ext_program_as_set s1 \<subseteq> ext_program_as_set s2 \<Longrightarrow>
    program_length (s1 addr) = program_length (s2 addr)"
apply(auto simp add:context_rw)
done

lemma maximal_ext_content :
   "ext_program_as_set s1 \<subseteq> ext_program_as_set s2 \<Longrightarrow>
    program_as_natural_map (s1 addr) =
    program_as_natural_map (s2 addr)"
apply(auto simp add:context_rw)
apply blast
done

lemma ext_at_context :
 "ext_program_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  ext_program_as_set s1 \<subseteq> ext_program_as_set (vctx_ext_program v2)"
apply(auto simp add:context_rw)
apply blast
done

lemma ext_length_from_context :
 "ext_program_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  program_length (vctx_ext_program v2 addr) = program_length (s1 addr)"
using ext_at_context [of s1 v2 c2]
  and maximal_ext_length [of s1 "vctx_ext_program v2"]
by force

lemma ext_content_from_context :
 "ext_program_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  program_as_natural_map (vctx_ext_program v2 addr) =
  program_as_natural_map (s1 addr)"
using ext_at_context [of s1 v2 c2]
  and maximal_ext_content [of s1 "vctx_ext_program v2"]
by force

lemma ext_program_same :
   "(\<forall>addr. program_length (p1 addr) = program_length (p2 addr)) \<Longrightarrow>
    (\<forall>addr. program_as_natural_map (p1 addr) =
            program_as_natural_map (p2 addr)) \<Longrightarrow>
    ext_program_as_set p1 = ext_program_as_set p2"
apply(simp add:ext_program_as_set_def)
done

(* account existence *)

lemma maximality_existence :
 "account_existence_as_set m1 \<subseteq> account_existence_as_set m2 \<Longrightarrow>
  m1 = m2"
apply(auto simp add:context_rw)
done

lemma existence_at_context :
 "account_existence_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  account_existence_as_set s1 \<subseteq> account_existence_as_set (vctx_account_existence v2)"
apply(auto simp add:context_rw)
done

lemma existence_from_context :
 "account_existence_as_set s1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
  vctx_account_existence v2 = s1"
 by (metis existence_at_context maximality_existence)


(* lemmas for all obvious subsets *)

lemma stack_subset :
  "stack_as_set (vctx_stack v1) \<subseteq> contexts_as_set v1 c1"
by(auto simp add:context_rw)

lemma memory_subset :
  "memory_as_set (vctx_memory v1) \<subseteq> contexts_as_set v1 c1"
by(auto simp add:context_rw)

lemma storage_subset :
  "storage_as_set (vctx_storage v1) \<subseteq> contexts_as_set v1 c1"
by(auto simp add:context_rw)

lemma balance_subset :
  "balance_as_set (vctx_balance v1) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)

lemma existence_subset :
  "account_existence_as_set (vctx_account_existence v1) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)

lemma data_sent_subset :
  "data_sent_as_set (vctx_data_sent v1) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)

lemma ext_program_subset :
  "ext_program_as_set (vctx_ext_program v1) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)

lemma log_subset :
  "log_as_set (vctx_logs v1) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)

lemma block_subset :
  "blockhash_as_elm (block_blockhash (vctx_block v1)) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)


lemma program_subset :
  "program_as_set (cctx_program c1) \<subseteq> contexts_as_set v1 c1"
by (auto simp add:context_rw)

lemma get_condition1 :
   "contexts_as_set v1 c1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
    vctx_memory_usage v1 =
    vctx_memory_usage v2 \<and>
    vctx_caller v1 = vctx_caller v2 \<and>
    vctx_value_sent v1 =
    vctx_value_sent v2 \<and>
    vctx_origin v1 = vctx_origin v2 \<and>
    vctx_gas v1 = vctx_gas v2 \<and>
    vctx_pc v1 = vctx_pc v2 \<and>
    block_coinbase (vctx_block v1) =
    block_coinbase (vctx_block v2) \<and>
    block_timestamp (vctx_block v1) =
    block_timestamp (vctx_block v2) \<and>
    block_difficulty (vctx_block v1) =
    block_difficulty (vctx_block v2) \<and>
    block_gaslimit (vctx_block v1) =
    block_gaslimit (vctx_block v2) \<and>
    block_number (vctx_block v1) =
    block_number (vctx_block v2) \<and>
    cctx_this c1 = cctx_this c2"
apply(simp add:context_rw)
done

lemma eq_class :
    "vctx_memory_usage v1 = vctx_memory_usage v2 \<Longrightarrow>
    vctx_caller v1 = vctx_caller v2 \<Longrightarrow>
    vctx_value_sent v1 = vctx_value_sent v2 \<Longrightarrow>
    vctx_gasprice v1 = vctx_gasprice v2 \<Longrightarrow>
    vctx_origin v1 = vctx_origin v2 \<Longrightarrow>
    vctx_gas v1 = vctx_gas v2 \<Longrightarrow>
    vctx_pc v1 = vctx_pc v2 \<Longrightarrow>
    vctx_data_sent v1 = vctx_data_sent v2 \<Longrightarrow>
    block_coinbase (vctx_block v1) =
    block_coinbase (vctx_block v2) \<Longrightarrow>
    block_blockhash (vctx_block v1) =
    block_blockhash (vctx_block v2) \<Longrightarrow>
    block_timestamp (vctx_block v1) =
    block_timestamp (vctx_block v2) \<Longrightarrow>
    block_difficulty (vctx_block v1) =
    block_difficulty (vctx_block v2) \<Longrightarrow>
    block_gaslimit (vctx_block v1) =
    block_gaslimit (vctx_block v2) \<Longrightarrow>
    block_number (vctx_block v1) = block_number (vctx_block v2) \<Longrightarrow>
    vctx_logs v1 = vctx_logs v2 \<Longrightarrow>
    vctx_stack v1 = vctx_stack v2 \<Longrightarrow>
    vctx_memory v1 = vctx_memory v2 \<Longrightarrow>
    vctx_storage v1 = vctx_storage v2 \<Longrightarrow>
    vctx_balance v1 = vctx_balance v2 \<Longrightarrow>
    vctx_account_existence v1 = vctx_account_existence v2 \<Longrightarrow>
    program_inst (cctx_program c1) = program_inst (cctx_program c2) \<Longrightarrow>
    cctx_this c1 = cctx_this c2 \<Longrightarrow>
    (\<forall>addr. program_length (vctx_ext_program v1 addr) =
            program_length (vctx_ext_program v2 addr)) \<Longrightarrow>
    (\<forall>addr. program_as_natural_map (vctx_ext_program v1 addr) =
            program_as_natural_map (vctx_ext_program v2 addr)) \<Longrightarrow>
    contexts_as_set v1 c1 = contexts_as_set v2 c2"
apply(simp add:contexts_as_set_def constant_ctx_as_set_def
  variable_ctx_as_set_def)
apply auto
using program_inst_same apply blast
using ext_program_same apply blast
using program_inst_same apply blast
using ext_program_same apply blast
done

lemma maximality :
   "contexts_as_set v1 c1 \<subseteq> contexts_as_set v2 c2 \<Longrightarrow>
    contexts_as_set v1 c1 = contexts_as_set v2 c2"
apply (rule eq_class)
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
  apply (metis data_from_context data_sent_subset order.trans)
apply(simp add:context_rw)
using block_from_context and block_subset
apply force
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
apply(simp add:context_rw)
using log_from_context and log_subset
apply force
using stack_from_context and stack_subset
apply force
using memory_from_context and memory_subset
apply force
using storage_from_context and storage_subset
apply force
using balance_from_context and balance_subset apply force
using existence_from_context and existence_subset apply force
using program_from_context and program_subset apply force
apply(simp add:context_rw)
using ext_length_from_context and ext_program_subset apply force
using ext_content_from_context and ext_program_subset apply force
done

(* Looping *)
(*
definition zero :: "'a set_pred" where
"zero = (\<lambda>x. False)"

lemma zero_add : "zero ## a = a"
apply (simp add:zero_def sep_add_def)
done

lemma zero_mul : "zero ** a = zero"
apply (simp add:zero_def sep_def)
done

lemma zero_triple : "triple net {} zero {} p"
apply (auto simp add:zero_mul triple_def zero_def sep_def)
done

lemma loop_triple :
  "(\<forall>x. \<exists>y. y < x \<and> triple net {} (p x) {} (p y ## q)) \<Longrightarrow>
    p (0::nat) = zero \<Longrightarrow>
    triple net {} (p x) {} q"
apply auto
done

lemma triple_three :
  "triple net {} p2 {} (q ## p1) \<Longrightarrow>
   triple net {} p1 {} (q ## p0) \<Longrightarrow>
   triple net {} p2 {} (q ## p0)"
apply (auto simp:triple_def failed_for_reasons_def)
apply(drule_tac x = co_ctx in spec)
apply(drule_tac x = co_ctx in spec)
apply auto
apply(drule_tac x = presult in spec)
apply(drule_tac x = rest in spec)
apply auto
apply(drule_tac x = stopper in spec)
apply auto
apply (auto simp:sep_add_def)
apply(drule_tac x = "program_sem stopper co_ctx k net presult" in spec)
apply(drule_tac x = rest in spec)
apply auto
apply(drule_tac x = stopper in spec)
apply auto
done

lemma loop_triple2 :
  "(\<forall>x. triple net {} (p x) {} (p (x-1) ## q)) \<Longrightarrow>
    triple net {} (p x) {} (p (0::nat) ## q)"
apply (induction x)
apply auto
  apply (metis diff_0_eq_0)
apply(drule_tac x = "Suc x" in spec)
apply auto
apply (rule triple_three)
apply auto
done

lemma loop_triple_int :
  "(\<forall>x. triple net {} (p x) {} (p (x-1) ## q)) \<Longrightarrow>
    \<exists>y. y < (0::int) \<and> triple net {} (p x) {} (p y ## q)"
apply (induction x)
subgoal for n
apply (induction n)
  apply force
apply auto
apply(drule_tac x = "int (Suc n)" in spec)
apply auto
using triple_three
  by blast
  by force

definition stable :: "network \<Rightarrow> state_element set_pred \<Rightarrow> bool" where
"stable net pre ==
    \<forall> co_ctx presult rest stopper. no_assertion co_ctx \<longrightarrow>
       (pre ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       (\<forall> k.
         (pre ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)))"


lemma triple_stable :
   "triple net {} p {} (q##r) \<Longrightarrow>
    triple net {} (p##r) {} (q##r)"
  using triple_tauto triple_three by fastforce

lemma triple_stable2 :
   "triple net {} p {} (q##s) \<Longrightarrow>
    triple net {} s {} r \<Longrightarrow>
    triple net {} (p##r) {} (q##r)"
  by (metis sep_add_def triple_stable triple_three weaken_post)

lemma loop_triple_int2 :
  "(\<forall>x. triple net {} (p x) {} (p (x-1) ## q x)) \<Longrightarrow>
   (\<forall>x. triple net {} (q x) {} (q (x+1))) \<Longrightarrow>
   \<exists>y. y < (0::int) \<and> triple net {} (p x) {} (p y ## q x)"
apply (induction x)
subgoal for n
apply (induction n)
  apply (smt semiring_1_class.of_nat_simps(1))
apply auto
apply(drule_tac x = "int (Suc n)" in spec)
apply(drule_tac x = "int n" in spec)
apply auto
subgoal for n y
apply (rule exI[of _ y])
apply auto
  by (smt sep_add_assoc sep_add_commute sep_add_never triple_stable2 triple_three)
done
  by (smt negative_zle)

lemma loop_triple_int3 :
  "(\<forall>x. triple net {} (p x) {} (p (x-1) ## q x)) \<Longrightarrow>
   (\<forall>x. triple net {} (q x) {} (q (x+1))) \<Longrightarrow>
   \<exists>y. y < (0::int) \<and> y \<le> x \<and> triple net {} (p x) {} (p y ## q x)"
apply (induction x)
subgoal for n
apply (induction n)
  apply (smt semiring_1_class.of_nat_simps(1))
apply auto
apply(drule_tac x = "int (Suc n)" in spec)
apply(drule_tac x = "int n" in spec)
apply auto
subgoal for n y
apply (rule exI[of _ y])
apply auto
  by (smt sep_add_assoc sep_add_commute sep_add_never triple_stable2 triple_three)
done
  by (smt negative_zle)




definition ex_pred :: "('b \<Rightarrow> 'a set_pred) \<Rightarrow> 'a set_pred" where
"ex_pred pred = (\<lambda>s. \<exists>y. pred y s)"

definition s_triple :: "network \<Rightarrow> state_element set_pred \<Rightarrow> state_element set_pred \<Rightarrow> bool" where
"s_triple net pre post ==
    \<forall> co_ctx presult rest stopper. no_assertion co_ctx \<longrightarrow>
       (pre ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k.
         (post ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)))"


lemma s_triple_eq : "s_triple net p q = triple net {} p {} q"
apply (auto simp add: triple_def s_triple_def failed_for_reasons_def)
done

definition failures :: "failure_reason set \<Rightarrow> state_element set_pred" where
"failures fails = (\<lambda>s.
   \<exists>lst. set lst \<subseteq> fails \<and> set lst \<noteq> {} \<and>
   s = {ContinuingElm False,
    ContractActionElm (ContractFail lst)})"

lemma s_triple_eq2 :
   "s_triple net (p**code c) (q**code c) = triple net {} p c q"
apply (auto simp add: triple_def s_triple_def failed_for_reasons_def)
done

lemma no_annotation_failure :
 "no_assertion co_ctx \<Longrightarrow>
  presult \<noteq> InstructionAnnotationFailure \<Longrightarrow>
  program_sem stopper co_ctx k net presult \<noteq> InstructionAnnotationFailure"
apply(cases presult)
apply (simp add:program_sem.simps failed_for_reasons_def
  program_annotation no_reasons_next)
subgoal for v1
apply (induction k arbitrary:v1 presult)
apply (auto simp add:program_sem.simps failed_for_reasons_def
  program_annotation no_reasons_next)
apply (case_tac "next_state stopper co_ctx net
             (InstructionContinue v1)")
apply auto
defer
  apply (simp add: program_environment)
apply(simp add:next_state_def)
apply(case_tac "vctx_next_instruction v1 co_ctx"; auto)
apply(case_tac "check_resources v1 co_ctx (vctx_stack v1) a net"; auto)
using no_annotation_inst by force
  apply (auto simp add: program_environment)
done

lemma code_elm_preserved :
"no_assertion co_ctx \<Longrightarrow>
 CodeElm (pos, i) \<in> instruction_result_as_set co_ctx presult \<Longrightarrow>
 CodeElm (pos, i) \<in> instruction_result_as_set co_ctx
 (program_sem stopper co_ctx k net presult)"
apply (cases presult; auto)
apply(case_tac "program_sem stopper co_ctx k net
             (InstructionContinue x1)")
apply (auto simp add:context_rw instruction_result_as_set_def)
using no_annotation_failure apply force
using no_annotation_failure apply force
apply(case_tac "program_sem stopper co_ctx k net
             presult")
apply (auto simp add:context_rw instruction_result_as_set_def)
using no_annotation_failure apply force
apply(case_tac "program_sem stopper co_ctx k net
             presult")
apply (auto simp add:context_rw instruction_result_as_set_def)
using no_annotation_failure apply force
done

lemma continue_elm_false :
"ContinuingElm False \<notin>
       instruction_result_as_set co_ctx
        (InstructionContinue x1)"
apply(auto simp:context_rw instruction_result_as_set_def)
done

lemma get_action_elm :
"ContractActionElm act \<in>
       instruction_result_as_set co_ctx
        (InstructionToEnvironment act2 v2 zz) \<Longrightarrow>
 act = act2"
apply(auto simp:context_rw instruction_result_as_set_def)
done

lemma s_triple_imp :
   "s_triple net (p**code c) (q**code c ##failures f) \<Longrightarrow>
    triple net f p c q"
apply (auto simp add: triple_def s_triple_def sep_add_def)
apply (drule_tac x = co_ctx in spec)
apply clarsimp
apply (drule_tac x = presult and y = rest in spec2)
apply clarsimp
apply (drule_tac x = stopper in spec)
apply clarsimp
subgoal for co_ctx presult rest stopper k
apply (rule_tac exI[of _ k])
apply auto
using code_elm_preserved apply fastforce

apply (auto simp add:sep_def failures_def
  failed_for_reasons_def)
subgoal for u ua v va
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
apply auto
proof -
  assume a1: "rest ua"
  assume a2: "ua \<union> va = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)"
  assume a3: "ua \<inter> va = {}"
  assume "{CodeElm (pos, i) |pos i. (pos, i) \<in> c} \<subseteq> va"
  then have f4: "ua \<inter> {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = {}"
    using a3 by blast
  have "\<forall>S. (va - S) \<inter> ua = {} \<or> {} - ua \<inter> S \<noteq> {}"
    using a3 by blast
  then have "(va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> ua = {} \<and> ua \<union> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = ua \<union> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c})"
    using f4 by (simp add: Diff_triv Un_Diff)
  then show "\<exists>S. rest S \<and> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> S = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult) - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<and> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> S = {}"
    using a2 a1 by auto
qed
apply (cases "program_sem stopper co_ctx k net presult")
apply simp
subgoal for u ua v lst x1
using continue_elm_false[of co_ctx x1]
apply auto
done
apply simp
subgoal for u ua v lst act vctx x33
apply (cases act; simp)
using get_action_elm
 [of "ContractFail lst" co_ctx act vctx x33]
  apply (metis contract_action.distinct(5) insertI1 insert_commute)
using get_action_elm
 [of "ContractFail lst" co_ctx act vctx x33]
  apply (metis contract_action.distinct insertI1 insert_commute)
using get_action_elm
 [of "ContractFail lst" co_ctx act vctx x33]
  apply (metis contract_action.distinct insertI1 insert_commute)
defer
using get_action_elm
 [of "ContractFail lst" co_ctx act vctx x33]
  apply (metis contract_action.distinct insertI1 insert_commute)
using get_action_elm
 [of "ContractFail lst" co_ctx act vctx x33]
  apply (metis contract_action.distinct insertI1 insert_commute)
  by (metis \<open>ContractActionElm (ContractFail lst) \<in> instruction_result_as_set co_ctx (InstructionToEnvironment act vctx x33) \<Longrightarrow> ContractFail lst = act\<close> contract_action.inject(4) insertI1 insert_commute)

apply (cases "program_sem stopper co_ctx k net presult")
apply simp

subgoal for u ua v va x1
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
apply auto
proof -
  assume a1: "rest ua"
  assume a2: "ua \<union> va = instruction_result_as_set co_ctx (InstructionContinue x1)"
  assume a3: "ua \<inter> va = {}"
  assume a4: "{CodeElm (pos, i) |pos i. (pos, i) \<in> c} \<subseteq> va"
  have f5: "\<forall>S. {} - ua \<inter> S = ua \<inter> (va - S)"
    using a3 by auto
  have "ua \<union> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = ua \<union> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c})"
    using a4 a3 by auto
  then have "(va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> ua = {} \<and> ua \<union> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> ua"
    using f5 by (simp add: inf_sup_aci(1) inf_sup_aci(5))
  then show "\<exists>S. rest S \<and> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> S = instruction_result_as_set co_ctx (InstructionContinue x1) - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<and> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> S = {}"
    using a2 a1 by auto
qed
apply simp
subgoal for u ua v va
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
apply auto
done
subgoal for u ua v va act vctx x33
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
proof -
  assume a1: "rest ua"
  assume a2: "ua \<inter> va = {}"
  assume a3: "{CodeElm (pos, i) |pos i. (pos, i) \<in> c} \<subseteq> va"
  assume a4: "q (va - {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"
  assume "program_sem stopper co_ctx k net presult = InstructionToEnvironment act vctx x33"
  assume a5: "ua \<union> va = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)"
  have "ua \<inter> {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = {}"
    using a3 a2 by blast
  then have "va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> ua = ua \<union> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<and> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> ua = {}"
    using a2 by (simp add: Diff_Int_distrib Diff_triv Un_Diff inf_sup_aci(1) inf_sup_aci(5))
  then show "q (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<and> (\<exists>S. rest S \<and> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> S = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult) - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<and> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> S = {})"
    using a5 a4 a1 by auto
qed
done
done

definition failures2 :: "failure_reason set \<Rightarrow> state_element set_pred" where
"failures2 fails = (\<lambda>s.
   \<exists>lst. set lst \<subseteq> fails \<and> set lst \<noteq> {} \<and>
   ContinuingElm False \<in> s \<and>
   ContractActionElm (ContractFail lst) \<in> s)"

lemma s_triple_imp2 :
   "s_triple net (p**code c) (q**code c ##failures2 f) \<Longrightarrow> triple net f p c q"
apply (auto simp add: triple_def s_triple_def sep_add_def)
apply (drule_tac x = co_ctx in spec)
apply clarsimp
apply (drule_tac x = presult and y = rest in spec2)
apply clarsimp
apply (drule_tac x = stopper in spec)
apply clarsimp
subgoal for co_ctx presult rest stopper k
apply (rule_tac exI[of _ k])
apply auto
using code_elm_preserved apply fastforce

apply (auto simp add:sep_def failures2_def
  failed_for_reasons_def)
subgoal for u ua v va
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
apply auto
proof -
  assume a1: "rest ua"
  assume a2: "ua \<union> va = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)"
  assume a3: "ua \<inter> va = {}"
  assume "{CodeElm (pos, i) |pos i. (pos, i) \<in> c} \<subseteq> va"
  then have f4: "ua \<inter> {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = {}"
    using a3 by blast
  have "\<forall>S. (va - S) \<inter> ua = {} \<or> {} - ua \<inter> S \<noteq> {}"
    using a3 by blast
  then have "(va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> ua = {} \<and> ua \<union> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = ua \<union> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c})"
    using f4 by (simp add: Diff_triv Un_Diff)
  then show "\<exists>S. rest S \<and> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> S = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult) - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<and> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> S = {}"
    using a2 a1 by auto
qed
apply (cases "program_sem stopper co_ctx k net presult")
apply simp
subgoal for u ua v va lst x1
using continue_elm_false[of co_ctx x1]
apply auto
done
apply auto
apply (cases "program_sem stopper co_ctx k net presult")
apply auto
subgoal for u ua v va lst x31 x32 x33
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
apply auto
  apply (metis Un_upper2 get_action_elm subset_iff)
  by (metis Un_upper2 get_action_elm subset_iff)
subgoal for u ua v va
apply (rule exI [of _ "(va -
          {CodeElm (pos, i) |pos i. (pos, i) \<in> c})"])
apply auto
proof -
  assume a1: "rest ua"
  assume a2: "ua \<union> va = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)"
  assume a3: "ua \<inter> va = {}"
  assume "{CodeElm (pos, i) |pos i. (pos, i) \<in> c} \<subseteq> va"
  then have "ua \<inter> {} = ua \<inter> {CodeElm (i, ia) |i ia. (i, ia) \<in> c}"
  using a3 by auto
  then have "ua \<union> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} = va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> ua"
    by auto
  then show "\<exists>S. rest S \<and> va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<union> S = instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult) - {CodeElm (i, ia) |i ia. (i, ia) \<in> c} \<and> (va - {CodeElm (i, ia) |i ia. (i, ia) \<in> c}) \<inter> S = {}"
    using a3 a2 a1 by auto
  qed
done
done

lemma s_triple_imp2 :
   "triple net f p c q \<Longrightarrow> s_triple net (p**code c) (q**code c ##failures2 f)"
apply (auto simp add: triple_def s_triple_def sep_add_def)
apply (drule_tac x = co_ctx in spec)
apply clarsimp
apply (drule_tac x = presult and y = rest in spec2)
apply clarsimp
apply (drule_tac x = stopper in spec)
apply clarsimp
subgoal for co_ctx presult rest stopper k
apply (rule_tac exI[of _ k])
apply auto

apply (auto simp add:sep_def failures_def
  failed_for_reasons_def)[1]
subgoal for u ua v va
apply (rule exI [of _ va])
apply clarsimp
apply (rule exI [of _
 "ua \<union> {CodeElm (pos, i) |pos i. (pos, i) \<in> c}"])
apply auto
  by (metis (no_types, lifting) Diff_cancel Int_Diff Un_Diff inf_commute inf_sup_absorb inf_sup_aci(1) sup_bot.right_neutral)

apply (cases "program_sem stopper co_ctx k net presult")
apply (simp add:failed_for_reasons_def)
apply (simp add:failed_for_reasons_def)
apply (simp add:failed_for_reasons_def)
apply clarsimp
oops
*)

end
