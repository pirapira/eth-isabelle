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

(* Define the semantic of triple_seq and prove it sound *)

definition triple_seq_sem :: "pred \<Rightarrow> pos_inst list \<Rightarrow> pred \<Rightarrow> bool" where
"triple_seq_sem pre insts post ==
    \<forall>co_ctx presult rest stopper net.
			no_assertion co_ctx \<longrightarrow>
      (pre ** code (set insts) ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
      ((post ** code (set insts) ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx (length insts) net presult)))"

lemma inst_seq_eq:
"triple_inst P i Q \<Longrightarrow> triple_seq_sem P [i] Q"
 apply(drule triple_inst_soundness)
 apply(simp add: triple_inst_sem_def triple_seq_sem_def)
 apply(fastforce)
done

lemma seq_compose_soundness:
notes sep_fun_simps[simp del]
shows
"triple_seq_sem P xs R \<Longrightarrow> triple_seq_sem R ys Q \<Longrightarrow> triple_seq_sem P (xs@ys) Q "
 apply(simp (no_asm) add: triple_seq_sem_def)
 apply clarsimp
 apply(subst (asm) triple_seq_sem_def[where pre=P])
 apply clarsimp
 apply(rename_tac co_ctx presult rest stopper net)
 apply(drule_tac x = "co_ctx" in spec, simp)
 apply(drule_tac x = "presult" in spec)
 apply(drule_tac x = "code ((set ys) - (set xs)) ** rest" in spec)
 apply(simp add: code_more sep_conj_ac)
 apply(drule_tac x = stopper in spec)
 apply(drule_tac x = "net" in spec)
 apply(clarsimp simp add: triple_seq_sem_def)
 apply(drule_tac x = "co_ctx" in spec; simp)
 apply(drule_tac x = "program_sem stopper co_ctx (length xs) net presult" in spec)
 apply(drule_tac x = "code ((set xs) - (set ys)) ** rest" in spec)
 apply(simp add: code_more sep_conj_ac code_union_comm)
 apply(drule_tac x = stopper in spec)
 apply(drule_tac x = "net" in spec)
 apply(simp add: execution_continue)
done

lemma triple_seq_empty:
"(\<And>s. pre s \<longrightarrow> post s) \<Longrightarrow> triple_seq_sem pre [] post"
 apply (simp add: triple_seq_sem_def program_sem.simps imp_sepL)
 apply(clarify)
 apply(drule allI)
 apply(simp add: imp_sepL)
done

lemma seq_strengthen_pre_sem:
  assumes  "triple_seq_sem P c Q"
  and      "(\<forall> s. R s \<longrightarrow> P s)"
  shows    " triple_seq_sem R c Q"
  using assms(1)
  apply (simp add: triple_seq_sem_def)
  apply(clarify)
  apply(drule_tac x = co_ctx in spec)
  apply(simp)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply simp
  apply(erule impE)
   apply(sep_drule assms(2)[rule_format])
   apply assumption
  apply simp
done

lemma triple_seq_soundness:
"triple_seq P xs Q \<Longrightarrow> triple_seq_sem P xs Q"
 apply(induction rule: triple_seq.induct)
    apply(drule inst_seq_eq)
    apply(rename_tac pre x q xs post)
    apply(subgoal_tac "x#xs = [x]@xs")
     apply(simp only: seq_compose_soundness)
    apply(simp)
   apply(simp add: triple_seq_empty)
  apply(simp add: seq_strengthen_pre_sem)
 apply(simp add: triple_seq_sem_def)
done

(* Re-define program_sem_t and prove the new one equivalent to the original one *)
(* It makes some proofs easier *)

(*val program_sem_t_alt: constant_ctx -> network -> instruction_result -> instruction_result*)
function (sequential,domintros)  program_sem_t_alt  :: " constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result \<Rightarrow> instruction_result "  where 
"program_sem_t_alt c net  (InstructionToEnvironment x y z) = (InstructionToEnvironment x y z)"
|" program_sem_t_alt c net InstructionAnnotationFailure = InstructionAnnotationFailure"
|" program_sem_t_alt c net (InstructionContinue v) =
     (if \<not> (check_annotations v c) then InstructionAnnotationFailure else
     (case  vctx_next_instruction v c of
        None => InstructionToEnvironment (ContractFail [ShouldNotHappen]) v None
      | Some i =>
        if check_resources v c(vctx_stack   v) i net then
          (* This if is required to prove that vctx_gas is stictly decreasing on program_sem's recursion *)
          (if(vctx_gas   v) \<le>( 0 :: int) then
              instruction_sem v c i net
          else  program_sem_t_alt c net (instruction_sem v c i net))
        else
          InstructionToEnvironment (ContractFail
              ((case  inst_stack_numbers i of
                 (consumed, produced) =>
                 (if (((int (List.length(vctx_stack   v)) + produced) - consumed) \<le>( 1024 :: int)) then [] else [TooLongStack])
                  @ (if meter_gas i v c net \<le>(vctx_gas   v) then [] else [OutOfGas])
               )
              ))
              v None
     ))" 
by pat_completeness auto

termination program_sem_t_alt
  apply (relation "measure (\<lambda>(c,net,ir). nat (case ir of InstructionContinue v \<Rightarrow>  vctx_gas v | _ \<Rightarrow> 0))")
   apply (simp)
  apply clarsimp
  subgoal for const net var inst
    apply (case_tac "instruction_sem var const inst net" ; simp)
    apply (clarsimp simp add: check_resources_def prod.case_eq_if )
     apply (frule instruction_sem_continuing)
     apply (erule (3) inst_sem_gas_consume)
  apply (simp add: vctx_next_instruction_def split:option.splits)
    done
done
declare program_sem_t_alt.simps[simp del]

lemma program_sem_t_alt_eq_continue:
"program_sem_t cctx net (InstructionContinue x) = program_sem_t_alt cctx net (InstructionContinue x)"
thm program_sem_t.induct[where P="\<lambda>x y z. program_sem_t x y z = program_sem_t_alt x y z"]
 apply(induction
 rule: program_sem_t.induct[where P="\<lambda>x y z. program_sem_t x y z = program_sem_t_alt x y z"] )
 apply(case_tac p; clarsimp)
   apply(simp (no_asm) add:program_sem_t_alt.simps program_sem_t.simps)
   apply(simp split:option.splits)
  apply(simp add:program_sem_t_alt.simps program_sem_t.simps)+
done

lemma program_sem_t_alt_eq:
"program_sem_t_alt cctx net pr = program_sem_t cctx net pr"
 apply(case_tac pr)
   apply(simp add: program_sem_t_alt_eq_continue)
  apply(simp add: program_sem_t.simps program_sem_t_alt.simps)+
done

(* Define the semantic of triple_cfg using program_sem_t and prove it sound *)

definition triple_cfg_sem_t :: "cfg \<Rightarrow> pred \<Rightarrow> vertex \<Rightarrow> pred \<Rightarrow> bool" where
"triple_cfg_sem_t c pre v post ==
    \<forall> co_ctx presult rest net (stopper::instruction_result \<Rightarrow> unit).
				no_assertion co_ctx \<longrightarrow>
        (cctx_program co_ctx = program_from_cfg c) \<longrightarrow>
        wf_cfg c \<longrightarrow>
        cfg_status c = None \<longrightarrow>
        cfg_blocks c (v_ind v) = Some (snd v) \<longrightarrow>
       (pre ** code (cfg_insts c) ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       ((post ** code (cfg_insts c) ** rest) (instruction_result_as_set co_ctx
            (program_sem_t_alt co_ctx net presult)))"

(* Lemmas to group code elements *)
lemma block_in_insts_:
"n \<in> set xs \<Longrightarrow>
cfg_blocks c n = Some (b, t) \<Longrightarrow>
set b \<subseteq> set (cfg_insts_aux c xs)"
apply(induction xs)
 apply(simp)
apply(case_tac "n \<in> set xs")
 apply(case_tac "cfg_blocks c a = None")
	apply(auto)
done

lemma block_in_insts:
"cfg_status c = None \<Longrightarrow>
wf_cfg c \<Longrightarrow>
cfg_blocks c n = Some (b, t) \<Longrightarrow>
set b \<subseteq> cfg_insts c"
apply(simp add: wf_cfg_def cfg_insts_def)
apply(drule_tac x = n in spec)+
apply(drule_tac x=b in spec)
apply(erule conjE)
apply(drule_tac x = t in spec)
apply(drule_tac x = "n + inst_size_list b" in spec)
apply(erule conjE, simp add: block_in_insts_)+
done

lemma decomp_set:
"P \<subseteq> Q =
(Q = (Q - P) \<union> P)"
by auto

lemma code_decomp:
" P \<subseteq> Q \<Longrightarrow>
{CodeElm (pos, i) |pos i.
         (pos, i) \<in> Q} =
({CodeElm (pos, i) |pos i.
         (pos, i) \<in> Q \<and> (pos, i) \<notin> P} \<union>
        {CodeElm (pos, i) |pos i.
         (pos, i) \<in> P})
"
by auto

lemma subset_minus:
"P \<inter> Q = {} \<Longrightarrow> P \<subseteq> R - Q \<Longrightarrow> P \<subseteq> R"
by auto

lemma code_code_sep_:
"P \<subseteq> Q \<Longrightarrow>
(code P \<and>* code (Q - P) \<and>* r) s =
(code Q \<and>* r) s"
 apply(simp)
 apply(rule iffI; rule conjI; (erule conjE)+)
		apply(simp add: code_decomp)
		apply(subgoal_tac "{CodeElm (pos, i) |pos i. (pos, i) \<in> P} \<inter> {CodeElm (pos, i) |pos i.
         (pos, i) \<in> Q \<and> (pos, i) \<notin> P} = {}")
		 apply(auto simp add: subset_minus)[1]
		apply(auto)[1]
	 apply(auto simp add: subset_minus diff_diff_union code_decomp)[1]
	apply(subgoal_tac "{CodeElm (pos, i) |pos i.
     (pos, i) \<in> Q \<and> (pos, i) \<notin> P} \<subseteq> {CodeElm (pos, i) |pos i.
     (pos, i) \<in> Q}")
	 apply(simp)
	apply(auto)[1]
 apply(rule conjI)
	apply(auto)[1]
 apply(auto simp add: subset_minus diff_diff_union code_decomp)
done

lemma code_code_sep:
"cfg_status cfg = None \<Longrightarrow>
wf_cfg cfg \<Longrightarrow>
cfg_blocks cfg n = Some (insts, ty) \<Longrightarrow>
(code (set insts) \<and>* code (cfg_insts cfg - set insts) \<and>* r) s =
(code (cfg_insts cfg) \<and>* r) s"
 apply(subgoal_tac "set insts \<subseteq> cfg_insts cfg")
	apply(simp only: code_code_sep_)
 apply(simp add: block_in_insts)
done

lemma sep_code_code_sep:
"cfg_status cfg = None \<Longrightarrow>
wf_cfg cfg \<Longrightarrow>
cfg_blocks cfg n = Some (insts, ty) \<Longrightarrow>
(p \<and>* code (set insts) \<and>* code (cfg_insts cfg - set insts) \<and>* r) s =
(p \<and>* code (cfg_insts cfg) \<and>* r) s"
 apply(rule iffI)
  apply(sep_select_asm 3)
	apply(sep_select_asm 3)
  apply(sep_select 2)
	apply(simp only: code_code_sep)
 apply(sep_select 3)
 apply(sep_select 3)
 apply(sep_select_asm 2)
 apply(simp only: code_code_sep)
done

lemma sep_sep_sep_code_code:
"cfg_status cfg = None \<Longrightarrow>
wf_cfg cfg \<Longrightarrow>
cfg_blocks cfg n = Some (insts, ty) \<Longrightarrow>
(p \<and>* q \<and>* r \<and>* code (set insts) \<and>* code (cfg_insts cfg - set insts)) s =
(p \<and>* q \<and>* r \<and>* code (cfg_insts cfg)) s"
 apply(rule iffI)
  apply(sep_select_asm 5)
	apply(sep_select_asm 5)
  apply(sep_select 4)
	apply(simp only: code_code_sep)
 apply(sep_select 5)
 apply(sep_select 5)
 apply(sep_select_asm 4)
 apply(simp only: code_code_sep)
done

lemma cfg_no_sem_t:
notes sep_fun_simps[simp del]
shows
" triple_seq pre insts post \<Longrightarrow> 
  triple_cfg_sem_t cfg pre (n, insts, No) post"
sorry

lemma cfg_next_sem_t:
notes sep_fun_simps[simp del]
shows
"\<And>cfg n i ii bi ti pre insts q post.
       cfg_edges cfg n = Some (i, None) \<Longrightarrow>
       cfg_blocks cfg i = Some (bi, ti) \<Longrightarrow>
       triple_seq pre insts (program_counter i \<and>* q) \<Longrightarrow>
       triple_cfg_sem_t cfg (program_counter i \<and>* q) (i, bi, ti) post \<Longrightarrow>
       triple_cfg_sem_t cfg pre (n, insts, Next) post"
sorry

lemma cfg_jump_sem_t:
notes sep_fun_simps[simp del]
shows
"\<And>cfg n dest bi ti pre insts p g m h rest post.
       cfg_edges cfg n = Some (dest, None) \<Longrightarrow>
       cfg_blocks cfg dest = Some (bi, ti) \<Longrightarrow>
       triple_seq pre insts
        (program_counter p \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack_height (Suc h) \<and>*
         stack h (word_of_int dest) \<and>*
         \<langle> h \<le> 1023 \<and> Gmid \<le> g \<and> 0 \<le> m \<rangle> \<and>* continuing \<and>* rest) \<Longrightarrow>
       triple_cfg cfg
        (program_counter dest \<and>*
         gas_pred (g - Gmid) \<and>*
         memory_usage m \<and>* stack_height h \<and>* continuing \<and>* rest)
        (dest, bi, ti) post \<Longrightarrow>
       triple_cfg_sem_t cfg
        (program_counter dest \<and>*
         gas_pred (g - Gmid) \<and>*
         memory_usage m \<and>* stack_height h \<and>* continuing \<and>* rest)
        (dest, bi, ti) post \<Longrightarrow>
       triple_cfg_sem_t cfg pre (n, insts, Jump) post"
sorry

lemma cfg_jumpi_sem_t:
notes sep_fun_simps[simp del]
shows
"\<And>cfg n dest j bi ti bj tj pre insts h g m cond p rest r post.
       cfg_edges cfg n = Some (dest, Some j) \<Longrightarrow>
       cfg_blocks cfg dest = Some (bi, ti) \<Longrightarrow>
       cfg_blocks cfg j = Some (bj, tj) \<Longrightarrow>
       triple_seq pre insts
        (\<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>*
         stack_height (Suc (Suc h)) \<and>*
         stack (Suc h) (word_of_int dest) \<and>*
         stack h cond \<and>*
         gas_pred g \<and>*
         continuing \<and>*
         memory_usage m \<and>* program_counter p \<and>* rest) \<Longrightarrow>
       r =
       (stack_height h \<and>*
        gas_pred (g - Ghigh) \<and>*
        continuing \<and>* memory_usage m \<and>* rest) \<Longrightarrow>
       (cond \<noteq> 0 \<Longrightarrow>
        triple_cfg cfg (r \<and>* program_counter dest) (dest, bi, ti)
         post) \<Longrightarrow>
       (cond \<noteq> 0 \<Longrightarrow>
        triple_cfg_sem_t cfg (r \<and>* program_counter dest)
         (dest, bi, ti) post) \<Longrightarrow>
       (cond = 0 \<Longrightarrow>
        triple_cfg cfg (r \<and>* program_counter j) (j, bj, tj) post) \<Longrightarrow>
       (cond = 0 \<Longrightarrow>
        triple_cfg_sem_t cfg (r \<and>* program_counter j) (j, bj, tj)
         post) \<Longrightarrow>
       triple_cfg_sem_t cfg pre (n, insts, Jumpi) post"
sorry

lemma triple_cfg_soundness_t :
notes sep_fun_simps[simp del]
shows
"triple_cfg c pre v post \<Longrightarrow> triple_cfg_sem_t c pre v post"
 apply(induction rule: triple_cfg.induct)
     apply(simp add: cfg_no_sem_t)
    apply(simp add: cfg_next_sem_t)
   apply(simp add: cfg_jump_sem_t)
  apply(simp add: cfg_jumpi_sem_t)
 apply(simp add: triple_cfg_sem_t_def)
done

end
