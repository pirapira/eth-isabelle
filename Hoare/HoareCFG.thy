(*
   Copyright 2017 Myriam Begel

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

theory "HoareCFG"

imports "HoareTripleForInstructions"
"../attic/CFG"
"../EvmFacts"

begin
type_synonym pred = "(state_element set \<Rightarrow> bool)"

(* We define here the program logic for CFGs *)
(* We start with Hoare triples valid for the execution of one instruction *)

(* We have add more instructions here *)
inductive triple_inst :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_push_n :
    "triple_inst
      (\<langle> h \<le> 1023 \<and> length lst > 0 \<and> 32 \<ge> length lst \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* program_counter n \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred g \<and>* rest)
      (n, Stack (PUSH_N lst))
      (continuing \<and>* memory_usage m \<and>*
       program_counter (n + 1 + int (length lst)) \<and>*
       stack_height (Suc h) \<and>* gas_pred (g - Gverylow) \<and>*
       stack h (word_rcat lst) \<and>* rest)"
| inst_stop :
    "triple_inst
      (\<langle> h \<le> 1024 \<and> 0 \<le> g \<and> m \<ge> 0\<rangle> \<and>* continuing \<and>* memory_usage m \<and>*
       program_counter n \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Misc STOP)
      (stack_height h \<and>* not_continuing \<and>* memory_usage m \<and>*
       program_counter n \<and>* action (ContractReturn []) \<and>*
       gas_pred g \<and>* rest)"
| inst_jumpdest :
    "triple_inst 
      (\<langle> h \<le> 1024 \<and> Gjumpdest \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Pc JUMPDEST)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred (g - Gjumpdest) \<and>* rest)"
| inst_strengthen_pre: 
    "triple_inst p i q \<Longrightarrow> (\<And>s. r s \<longrightarrow> p s) \<Longrightarrow> triple_inst r i q"
| inst_false_pre: 
    "triple_inst \<langle>False\<rangle> i post"

inductive triple_seq :: "pred \<Rightarrow> pos_inst list \<Rightarrow> pred \<Rightarrow> bool" where
  seq_inst : 
  "\<lbrakk>triple_inst pre x q;
    triple_seq q xs post \<rbrakk> \<Longrightarrow>
   triple_seq pre (x#xs) post"
| seq_empty: 
  "(\<And>s. pre s \<longrightarrow> post s) \<Longrightarrow>
   triple_seq pre [] post"
| seq_strengthen_pre: 
  "triple_seq p xs q \<Longrightarrow>
   (\<And>s. r s \<longrightarrow> p s) \<Longrightarrow>
   triple_seq r xs q"
| seq_false_pre: 
  "triple_seq \<langle>False\<rangle> xs post"

inductive triple_cfg :: "cfg \<Rightarrow> pred \<Rightarrow> vertex \<Rightarrow> pred \<Rightarrow> bool" where
  cfg_no : 
  "triple_seq pre insts post \<Longrightarrow>
   triple_cfg cfg pre (n, insts, No) post"
| cfg_next : 
  "\<lbrakk>cfg_edges cfg n = Some (i, None);
    cfg_blocks cfg i = Some (bi, ti);
    triple_seq pre insts (program_counter i \<and>* q);
    triple_cfg cfg (program_counter i \<and>* q) (i, bi, ti) post\<rbrakk> \<Longrightarrow>
   triple_cfg cfg pre (n, insts, Next) post"
| cfg_jump : 
  "\<lbrakk>cfg_edges cfg n = Some (dest, None);
    cfg_blocks cfg dest = Some (bi, ti);
    triple_seq pre insts
      (program_counter p \<and>* gas_pred g \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (word_of_int dest::256 word) \<and>*
       \<langle> h \<le> 1023 \<and> Gmid \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* rest);
    triple_cfg cfg
      (program_counter dest \<and>* gas_pred (g - Gmid) \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       continuing \<and>* rest) 
      (dest, bi, ti) post\<rbrakk> \<Longrightarrow>
   triple_cfg cfg pre (n, insts, Jump) post"
| cfg_jumpi : 
  "\<lbrakk>cfg_edges cfg n = Some (dest, Some j);
    cfg_blocks cfg dest = Some (bi, ti);
    cfg_blocks cfg j = Some (bj, tj);
    triple_seq pre insts
      ((\<langle> h \<le> 1022  \<and> Ghigh \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       stack_height (Suc (Suc h)) \<and>*
       stack (Suc h) (word_of_int dest::256 word) \<and>*
       stack h cond \<and>* gas_pred g \<and>*
       continuing \<and>* memory_usage m \<and>*
       program_counter p \<and>* rest));
    r = (stack_height h \<and>* gas_pred (g - Ghigh) \<and>*
         continuing \<and>* memory_usage m \<and>* rest);
    (cond \<noteq> 0 \<Longrightarrow> triple_cfg cfg (r \<and>* program_counter dest) (dest, bi, ti) post);
    (cond = 0 \<Longrightarrow> triple_cfg cfg (r \<and>* program_counter j) (j, bj, tj) post)\<rbrakk> \<Longrightarrow>
   triple_cfg cfg pre (n, insts, Jumpi) post"
| cfg_false_pre: 
  "triple_cfg cfg \<langle>False\<rangle> i post"

(* Group lemmas *)
lemmas as_set_simps =
balance_as_set_def contract_action_as_set_def annotation_failure_as_set
contexts_as_set_def constant_ctx_as_set_def memory_as_set_def storage_as_set_def
data_sent_as_set_def log_as_set_def stack_as_set_def instruction_result_as_set_def
program_as_set_def variable_ctx_as_set_def constant_ctx_as_set_def ext_program_as_set_def

lemmas sep_tools_simps =
emp_sep sep_true pure_sepD pure_sep sep_lc sep_three imp_sepL sep_impL

lemmas sep_fun_simps =
caller_sep  sep_caller sep_caller_sep
balance_sep sep_balance sep_balance_sep
not_continuing_sep sep_not_continuing_sep
this_account_sep sep_this_account sep_this_account_sep
action_sep sep_action sep_action_sep
memory8_sepD memory8_sepI memory8_sep_h_cancelD sep_memory8 sep_memory8_sep memory8_sep
memory_usage_sep sep_memory_usage sep_memory_usage_sep
memory_range_sep sep_memory_range
continuing_sep sep_continuing_sep
gas_pred_sep sep_gas_pred
gas_any_sep sep_gas_any_sep sep_gas_pred_sep sep_gas_pred gas_pred_sep
program_counter_sep sep_program_counter sep_program_counter_sep
stack_height_sep sep_stack_height sep_stack_height_sep
stack_sep sep_stack sep_stack_sep
block_number_pred_sep sep_block_number_pred_sep
sep_log_number_sep sep_logged
storage_sep sep_storage
code_sep sep_code sep_sep_code sep_code_sep

lemmas inst_numbers_simps =
dup_inst_numbers_def storage_inst_numbers.simps stack_inst_numbers.simps
pc_inst_numbers.simps info_inst_numbers.simps inst_stack_numbers.simps
arith_inst_numbers.simps sarith_inst_nums.simps storage_inst_numbers.simps
bits_stack_nums.simps memory_inst_numbers.simps swap_inst_numbers_def
log_inst_numbers.simps  misc_inst_numbers.simps

lemmas inst_size_simps =
inst_size_def inst_code.simps bits_inst_code.simps sarith_inst_code.simps
arith_inst_code.simps info_inst_code.simps dup_inst_code_def
memory_inst_code.simps storage_inst_code.simps pc_inst_code.simps
stack_inst_code.simps swap_inst_code_def log_inst_code.simps misc_inst_code.simps

lemmas stack_simps=
stack_0_0_op_def stack_0_1_op_def stack_1_1_op_def
stack_2_1_op_def stack_3_1_op_def

lemmas gas_value_simps =
Gjumpdest_def Gzero_def Gbase_def Gcodedeposit_def Gcopy_def
Gmemory_def Gverylow_def Glow_def Gsha3word_def Gcall_def
Gtxcreate_def Gtxdatanonzero_def Gtxdatazero_def Gexp_def
Ghigh_def Glogdata_def Gmid_def Gblockhash_def Gsha3_def
Gsreset_def Glog_def Glogtopic_def  Gcallstipend_def Gcallvalue_def
Gcreate_def Gnewaccount_def Gtransaction_def Gexpbyte_def
Gsset_def Gsuicide_def Gbalance_def Gsload_def Gextcode_def

lemmas instruction_sem_simps =
instruction_sem_def constant_mark_def stack_simps
subtract_gas.simps vctx_advance_pc_def
check_resources_def vctx_next_instruction_def
meter_gas_def C_def Cmem_def M_def
new_memory_consumption.simps
thirdComponentOfC_def pop_def
vctx_next_instruction_default_def vctx_next_instruction_def
blockedInstructionContinue_def vctx_pop_stack_def
blocked_jump_def strict_if_def
general_dup_def

lemmas advance_simps=
vctx_advance_pc_def vctx_next_instruction_def

lemmas instruction_memory =
mload_def mstore_def mstore8_def calldatacopy_def
codecopy_def extcodecopy_def

lemmas instruction_simps =
instruction_failure_result_def sha3_def
instruction_sem_simps gas_value_simps
inst_size_simps inst_numbers_simps
instruction_memory

(* Define the semantic for triple_inst and prove it sound *)
definition triple_inst_sem :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
"triple_inst_sem pre inst post ==
    \<forall>co_ctx presult rest stopper n.
			no_assertion co_ctx \<longrightarrow>
      (pre \<and>* code {inst} \<and>* rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
      ((post \<and>* code {inst} \<and>* rest) (instruction_result_as_set co_ctx
          (program_sem stopper co_ctx 1 n presult)))"

lemma inst_strengthen_pre_sem:
  assumes  "triple_inst_sem P c Q"
  and      "(\<forall> s. R s \<longrightarrow> P s)"
  shows    " triple_inst_sem R c Q"
  using assms(1)
  apply (simp add: triple_inst_sem_def)
  apply(clarify)
  apply(drule_tac x = co_ctx in spec)
  apply(simp)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply simp
  apply (erule impE)
   apply (sep_drule assms(2)[rule_format])
   apply assumption
  apply simp
done

lemma inst_false_pre_sem:
  "triple_inst_sem \<langle>False\<rangle> i q"
by(simp add: triple_inst_sem_def sep_basic_simps pure_def)

lemma inst_stop_sem:
"triple_inst_sem
  (\<langle> h \<le> 1024 \<and> 0 \<le> g \<and> m \<ge> 0\<rangle> \<and>* continuing \<and>* memory_usage m  \<and>* program_counter n \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
  (n, Misc STOP)
  (stack_height h \<and>* not_continuing \<and>* memory_usage m \<and>* program_counter n \<and>* action (ContractReturn []) \<and>* gas_pred g \<and>* rest )"
 apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps sep_conj_ac)
 apply(clarify)
 apply(simp split: instruction_result.splits)
 apply(simp add: vctx_next_instruction_def)
 apply(split option.splits)
 apply(simp add: sep_conj_commute[where P="rest"] sep_conj_assoc)
 apply(clarify)
 apply(rule conjI)
  apply(clarsimp split:option.splits)
 apply(subgoal_tac "(case program_content (cctx_program co_ctx) n of
               None \<Rightarrow> Some (Misc STOP) | Some i \<Rightarrow> Some i) =
              Some (Misc STOP)")
  apply(clarsimp)
  apply(rule conjI; rule impI; rule conjI; clarsimp;
  simp add: instruction_sem_simps stop_def gas_value_simps inst_numbers_simps)
  apply(simp add: sep_not_continuing_sep sep_action_sep del:sep_program_counter_sep)
  apply(sep_select 2; simp only:sep_fun_simps;simp)
 apply(simp split: option.splits)
 apply(rule allI; rule impI; simp)
done

lemma inst_push_sem:
"triple_inst_sem 
  (\<langle> h \<le> 1023 \<and> length lst > 0 \<and> 32 \<ge> length lst \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
   continuing \<and>* program_counter n \<and>*
   memory_usage m \<and>* stack_height h \<and>*
   gas_pred g \<and>* rest)
  (n, Stack (PUSH_N lst))
  (continuing \<and>* memory_usage m \<and>*
   program_counter (n + 1 + int (length lst)) \<and>*
   stack_height (Suc h) \<and>* gas_pred (g - Gverylow) \<and>*
   stack h (word_rcat lst) \<and>* rest)"
 apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps sep_conj_ac)
 apply(clarify)
 apply(simp split: instruction_result.splits)
 apply(simp add: vctx_next_instruction_def)
 apply(simp add: sep_conj_commute[where P="rest"] sep_conj_assoc)
 apply(simp add: instruction_sem_simps inst_numbers_simps)
 apply(simp add: advance_simps inst_size_simps)
 apply(clarify)
 apply clarsimp
 apply(rename_tac rest0 vctx)
 apply (erule_tac P="(rest0 \<and>* rest)" in back_subst)
 apply(auto simp add: as_set_simps)
done

lemma inst_jumpdest_sem:
"triple_inst_sem
  (\<langle> h \<le> 1024 \<and> Gjumpdest \<le> g \<and> 0 \<le> m \<rangle> \<and>*
   continuing \<and>* memory_usage m \<and>*
   program_counter n \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
  (n, Pc JUMPDEST)
  (continuing \<and>* program_counter (n + 1) \<and>*
   memory_usage m \<and>* stack_height h \<and>* gas_pred (g - Gjumpdest) \<and>* rest)"
 apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps sep_conj_ac)
 apply(clarify)
 apply(simp split: instruction_result.splits)
 apply(simp add: vctx_next_instruction_def)
 apply(simp add: sep_conj_commute[where P="rest"] sep_conj_assoc)
 apply(simp add: instruction_sem_simps inst_numbers_simps)
 apply(simp add: advance_simps inst_size_simps)
 apply(clarify)
 apply(rename_tac rest0 vctx)
 apply (erule_tac P="(rest0 \<and>* rest)" in back_subst)
 apply(auto simp add: as_set_simps)
done

lemma triple_inst_soundness:
  "triple_inst p i q \<Longrightarrow> triple_inst_sem p i q"
  apply(induction rule:triple_inst.induct)
      apply(simp only: inst_push_sem)
     apply(simp only: inst_stop_sem)
    apply(simp only: inst_jumpdest_sem)
   apply(simp add: inst_strengthen_pre_sem)
  apply(simp add: inst_false_pre_sem)
done

end
