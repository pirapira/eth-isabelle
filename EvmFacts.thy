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
  imports "lem/Evm"
      "Hoare/Hoare"
begin

lemmas gas_simps = Gverylow_def Glow_def Gmid_def Gbase_def Gzero_def Glogtopic_def 
    Gsha3word_def Gsha3_def Gextcode_def Gcopy_def Gblockhash_def Gexpbyte_def Gexp_def
    Gbalance_def Gsload_def Gsreset_def Gsset_def Gjumpdest_def Ghigh_def
    Glogdata_def  Glog_def Gcreate_def Ccall_def 
    Cgascap_def Cextra_def Gnewaccount_def Cxfer_def Cnew_def
    Gcall_def Gcallvalue_def Csstore_def Csuicide_def

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
  " 0 \<le> Cgascap a b c d e f"
  apply (simp add: Cgascap_def L_def )
  apply clarsimp
  apply (rule zdiv_le_dividend)
  apply linarith
  apply simp
done
(*  by (case_tac " b = 0" ; auto simp:L_def gas_simps)+*)

lemma Ccall_gt_0:
  "0 < Ccall s0 s1 s2 recipient_empty
            remaining_gas net mmu_extra"
  unfolding Ccall_def
  using Cextra_gt_0 Cgascap_gt_0
  by (clarsimp simp add: ordered_comm_monoid_add_class.add_nonneg_pos)+

lemma Csuicide_gt_0:
  "Gsuicide net \<noteq> 0 \<Longrightarrow> 0 < Csuicide recipient_empty net"
  unfolding Csuicide_def
  by (auto split: if_splits
           simp add: gas_simps Gsuicide_def)

lemma thirdComponentOfC_gt_0:
  "i \<noteq> Misc STOP \<Longrightarrow> i \<noteq> Misc RETURN \<Longrightarrow> (\<forall>v. i \<noteq> Unknown v) \<Longrightarrow>
   i = Misc SUICIDE \<longrightarrow> Gsuicide net \<noteq> 0 \<Longrightarrow>
   i \<notin>  (if before_homestead net then {Misc DELEGATECALL} else {}) \<Longrightarrow>
  0 < thirdComponentOfC  i s0 s1 s2 s3 recipient_empty orig_val new_val remaining_gas net mmu_extra"
  unfolding thirdComponentOfC_def
  apply (case_tac i ; simp add: gas_simps del: Cextra_def )
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
         apply (clarsimp simp: Csuicide_gt_0 Ccall_gt_0  split:if_splits)
         done

lemma Cmem_lift:
  "max 0 x \<le> y \<Longrightarrow> Cmem (max 0 x) \<le> Cmem y"
  apply (simp add: Cmem_def Gmemory_def)
  apply (case_tac "x = y")
   apply (clarsimp simp: max_def)
  apply clarsimp
  apply (drule (1) order_class.le_neq_trans)
  apply simp
  apply (rule add_mono, simp)
  apply (rule zdiv_mono1[rotated], simp)
  apply (rule mult_mono ; simp)
  done

lemma vctx_memory_usage_never_decreases:
  "max 0 (vctx_memory_usage v) \<le> (new_memory_consumption i(max 0 (vctx_memory_usage   v)) (vctx_stack_default(( 0 :: int)) v) (vctx_stack_default(( 1 :: int)) v) (vctx_stack_default(( 2 :: int)) v) (vctx_stack_default(( 3 :: int)) v)
      (vctx_stack_default(( 4 :: int)) v) (vctx_stack_default(( 5 :: int)) v) (vctx_stack_default(( 6 :: int)) v))"
apply(case_tac i)
apply(rename_tac x, case_tac x; simp add: new_memory_consumption.simps vctx_stack_default_def M_def max_def)+
done

lemma meter_gas_gt_0:
  " inst \<noteq> Misc STOP \<Longrightarrow>
    inst \<noteq> Misc RETURN \<Longrightarrow>
    inst \<noteq> Misc SUICIDE \<Longrightarrow>
    inst \<notin> range Unknown \<Longrightarrow>
    inst \<notin>  (if before_homestead net then {Misc DELEGATECALL} else {}) \<Longrightarrow>
program_content (cctx_program const) (vctx_pc var) = Some inst \<Longrightarrow>
   0 < meter_gas inst var const net"

  using Cmem_lift[OF
    vctx_memory_usage_never_decreases[where i=inst and v=var]]
  apply (clarsimp simp add: C_def meter_gas_def Cmem_def Gmemory_def Let_def)
  apply(case_tac inst)
apply( simp add: new_memory_consumption.simps vctx_next_instruction_default_def vctx_next_instruction_def;
   fastforce  intro: ordered_comm_monoid_add_class.add_nonneg_pos 
          thirdComponentOfC_gt_0) +
done

lemma subtract_gas_lower_gas:
   "subtract_gas m k (InstructionContinue var) = InstructionContinue v
    \<Longrightarrow> 0 < m \<Longrightarrow> vctx_gas v < vctx_gas var "
  by (auto simp add: subtract_gas.simps)

lemmas stack_op_simps = stack_0_0_op_def stack_0_1_op_def
   stack_2_1_op_def stack_1_1_op_def stack_3_1_op_def

lemmas op_simps = mstore8_def mload_def sha3_def
  general_dup_def mstore_def swap_def ret_def create_def
  call_def suicide_def calldatacopy_def codecopy_def
  extcodecopy_def sstore_def jump_def jumpi_def
  pc_def pop_def log_def callcode_def delegatecall_def
  
lemmas instruction_sem_simps =
  stack_op_simps instruction_failure_result_def
  subtract_gas.simps vctx_advance_pc_def
  op_simps vctx_update_storage_def
  blocked_jump_def blockedInstructionContinue_def
  strict_if_def vctx_pop_stack_def
  vctx_next_instruction_def 

lemma instruction_sem_not_continuing:
  "\<lbrakk> inst \<in> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown \<rbrakk> \<Longrightarrow>
\<forall>v. instruction_sem var const inst net \<noteq> InstructionContinue v"
  apply (case_tac inst; clarsimp simp: instruction_sem_def instruction_failure_result_def subtract_gas.simps)
  subgoal for opcode 
   apply (case_tac opcode; simp add: ret_def suicide_def image_def stop_def instruction_sem_def instruction_failure_result_def subtract_gas.simps split:list.splits)
   done
  done

lemma instruction_sem_continuing:
  "\<lbrakk> instruction_sem var const inst net = InstructionContinue v \<rbrakk> \<Longrightarrow>
inst \<notin> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown \<union> (if  before_homestead net then {Misc DELEGATECALL} else {})"
  apply (case_tac inst; clarsimp simp: instruction_sem_def instruction_failure_result_def subtract_gas.simps)
  subgoal for opcode
   apply (case_tac opcode; simp add: ret_def suicide_def image_def stop_def instruction_sem_def instruction_failure_result_def subtract_gas.simps split:list.splits if_split_asm)
   done
  done

lemma inst_sem_gas_consume:
  "instruction_sem var const inst net = InstructionContinue v \<Longrightarrow>
   inst \<notin> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown \<union> (if before_homestead net then {Misc DELEGATECALL} else {}) \<Longrightarrow>
  \<not> vctx_gas var \<le> 0 \<Longrightarrow>
  program_content (cctx_program const) (vctx_pc var) = Some inst \<Longrightarrow>
  vctx_gas v < vctx_gas var"
  apply (cut_tac meter_gas_gt_0[where inst=inst and var=var and const=const and net=net]; simp)
  apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
             apply (case_tac x2 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: Let_def instruction_sem_simps split:list.splits if_splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x8 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x9 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x2; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
  apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
    done

termination program_sem_t
  apply (relation "measure (\<lambda>(c,net,ir). nat (case ir of InstructionContinue v \<Rightarrow>  vctx_gas v | _ \<Rightarrow> 0))")
   apply (simp)
  apply clarsimp
  subgoal for const net var inst
    apply (case_tac "instruction_sem var const inst net" ; simp)
    apply (clarsimp simp add: check_resources_def prod.case_eq_if )
     apply (frule instruction_sem_continuing)
     apply (erule (2) inst_sem_gas_consume)
  apply (simp add: vctx_next_instruction_def split:option.splits)
    done
done
    
lemma program_sem_t_no_gas_not_continuing:
  "\<lbrakk>vctx_gas var \<le> 0 \<rbrakk> \<Longrightarrow>
\<forall>v. program_sem_t const net (InstructionContinue var) \<noteq> InstructionContinue v"
  apply (clarsimp simp add: check_resources_def prod.case_eq_if  split:option.split)
  apply (drule instruction_sem_continuing)
  subgoal for i inst
  using meter_gas_gt_0[where inst=i and var=var and const=const and net=net]
  apply (simp add: vctx_next_instruction_def split:option.splits)
  done
 done

declare program_sem_t.simps[simp del]
declare next_state_def[simp del]

lemma program_sem_t_imp_program_sem:
  notes if_split[split del]
  shows
 "\<exists>k. program_sem_t const net ir = program_sem (\<lambda>_. ()) const k net ir"
  apply (induct rule:program_sem_t.induct)
  apply (case_tac p)
    apply clarify
    apply (rename_tac c net p inst)
    apply (drule_tac x=inst in meta_spec)
    apply (case_tac "vctx_next_instruction inst c", simp add: vctx_next_instruction_def split:option.splits)
    apply (rename_tac nxt_inst)
    apply (drule_tac x="nxt_inst" in meta_spec)
    apply (erule meta_impE , simp)
    apply (erule meta_impE , simp)
    apply (subst program_sem_t.simps)
    apply (simp)
    apply (split if_split)
    apply (rule conjI)
    apply clarify
    apply (drule meta_mp, simp)
    apply (split if_split)
    apply (rule conjI)
     apply clarsimp
     apply (rule exI[where x="Suc 0"])
     apply (simp add: program_sem.simps next_state_def )
    apply (rule impI)
    apply (clarsimp split:if_split)
    apply (rule_tac x="Suc k" in exI)
    apply (simp add: program_sem.simps next_state_def)
   apply (clarsimp )
   apply (rule exI[where x="Suc 0"])
   apply (clarsimp simp: program_sem.simps next_state_def)
  apply (rule exI[where x="Suc 0"])
  apply (clarsimp simp: program_sem_t.simps program_sem.simps next_state_def)
  done
  
lemma program_sem_ItoE :
"program_sem (\<lambda>_. ()) const k net (InstructionToEnvironment a b c) = InstructionToEnvironment a b c"
  apply(induct_tac k, simp add: program_sem.simps next_state_def split: if_split)
  apply(simp add: program_sem.simps next_state_def split: if_split)
  done

(* perhaps rename this to 'program_sem_no_gas_not_continuing' and 
   the above to 'program_sem_t_no_gas_not_continuing' *)    
lemma program_sem_no_gas_not_continuing' :
  "\<lbrakk>vctx_gas var \<le> 0  \<rbrakk> \<Longrightarrow>
\<forall>k>0. \<forall>v. program_sem (\<lambda>_. ()) c k net (InstructionContinue var) \<noteq> InstructionContinue v"
  apply clarify
  apply(case_tac k, simp)
  apply (simp add: program_sem.simps next_state_def split: if_split_asm)
  apply (case_tac "vctx_next_instruction var c", simp  split:option.splits)
   apply(simp add: program_sem_ItoE)
    apply(simp split: if_split_asm)
    apply (clarsimp simp add: check_resources_def prod.case_eq_if split:option.split)
    apply(clarsimp simp: vctx_next_instruction_def split:option.splits)
     apply(simp add: instruction_sem_def stop_def subtract_gas.simps)
     apply(simp add: program_sem_ItoE)
    apply(rename_tac inst)
    apply(case_tac "instruction_sem var c inst net")
      apply(drule instruction_sem_continuing, clarsimp)
    apply(drule_tac const=c in meter_gas_gt_0[where net=net], assumption+)
      apply fastforce
     apply clarsimp
    apply(simp add: program_sem_ItoE)
   apply(simp add: program_sem_ItoE)
  apply(simp add: program_sem_ItoE)
  done

theorem program_sem_t_in_program_sem:
  notes if_split[split del]
  shows
 "\<exists>k. program_sem_t const net ir  = program_sem (\<lambda>_. ()) const k net  ir \<and>
     (\<forall>l\<ge>k. \<forall>z. program_sem (\<lambda>_. ()) const l net ir \<noteq> InstructionContinue z) \<and>
     (\<forall>l<k. \<exists>z. program_sem (\<lambda>_. ()) const l net ir = InstructionContinue z)"
  apply(induct_tac const net ir rule: program_sem_t.induct) 
  apply(case_tac p)
   apply clarify
   apply(rename_tac c net p inst) 
   apply(drule_tac x=inst in meta_spec)
   apply(case_tac "vctx_next_instruction inst c", simp add: vctx_next_instruction_def split:option.splits)
   apply(rename_tac nxt_inst) 
   apply(drule_tac x="nxt_inst" in meta_spec)
   apply(erule meta_impE, simp)
   apply(subst program_sem_t.simps)
   apply(simp only: instruction_result.simps)
   apply (drule meta_mp, simp)
   apply simp
   apply(split if_split)    
   apply(rule conjI)    
    apply clarify
    apply (drule meta_mp, simp)
    apply(split if_split)
    apply(rule conjI)
    apply clarify
    apply(rule exI[where x="Suc 0"])    
    apply(simp add: program_sem.simps next_state_def split: if_split)
    apply(drule_tac c=c and net=net in program_sem_no_gas_not_continuing')
    apply fastforce
    apply(rule impI, simp)
    apply(erule exE)
    apply(rule_tac x="k + 1" in exI, clarify)
    apply(simp add: program_sem.simps next_state_def)
    apply(rule conjI)
     apply(rule allI, rule impI)
     apply(case_tac l, simp)
     apply(rename_tac l')
     apply(drule_tac x=l' in spec, drule mp, simp)
     apply(simp add: program_sem.simps next_state_def)       
    apply(rule allI, rule impI)
    apply(case_tac l, simp add: program_sem.simps)
    apply(rename_tac l', clarify)
    apply(drule_tac x=l' in spec, drule mp, assumption)   
    apply(clarsimp simp: program_sem.simps next_state_def)
   apply(rule impI)
   apply(rule exI[where x="Suc 0"])  
   apply(simp add: program_sem.simps next_state_def)
   apply clarify
   apply(case_tac l, simp)
   apply clarify
   apply(simp add: program_sem.simps next_state_def)    
  apply(simp add: program_sem_ItoE)   
  apply(simp add: program_sem.simps next_state_def)
  apply(simp add: program_sem_ItoE program_sem_t.simps)
  apply fastforce
  done

corollary program_sem_t_fix :
"program_sem (\<lambda>_. ()) const n net (program_sem_t const net ir) =
 program_sem_t const net ir"
  apply(insert program_sem_t_in_program_sem[of const net ir])
  apply clarify
  apply(erule ssubst)
  apply(drule_tac x="k" in spec, drule mp, simp)
  apply(case_tac "program_sem (\<lambda>_. ()) const k net ir")
    apply fastforce
   apply(erule ssubst)
  apply(simp add: program_sem_ItoE)
  done

end
