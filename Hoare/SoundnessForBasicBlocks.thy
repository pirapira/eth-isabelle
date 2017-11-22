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

theory "SoundnessForBasicBlocks"

imports "HoareTripleForBasicBlocks"
"../Word_Lib/Word_Lemmas"
begin

lemmas instruction_simps =
instruction_sem_simps gas_value_simps
inst_size_simps inst_numbers_simps
meter_gas_def new_memory_consumption.simps
vctx_stack_default_def check_resources_def
C_def thirdComponentOfC_def
instruction_sem_def

(* Soundness proof for instruction rules *)

lemma inst_strengthen_pre_sem:
  assumes  "triple_inst_sem n P c Q"
  and      "(\<forall> s. R s \<longrightarrow> P s)"
  shows    " triple_inst_sem n R c Q"
  using assms(1)
  apply (simp add: triple_inst_sem_def)
  apply(clarify)
  apply(drule_tac x = co_ctx in spec)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply (erule impE)
   apply (sep_drule assms(2)[rule_format])
   apply assumption
  apply simp
done

lemma inst_false_pre_sem:
  "triple_inst_sem n \<langle>False\<rangle> i q"
by(simp add: triple_inst_sem_def sep_basic_simps pure_def)

method inst_sound_set_eq uses simp =
 simp add: triple_inst_sem_def program_sem.simps as_set_simps,
 clarify,
 sep_simp simp: evm_sep; simp,
 simp split: instruction_result.splits,
 simp add: stateelm_means_simps stateelm_equiv_simps,
 simp add: vctx_next_instruction_def,
 clarsimp simp add: instruction_simps simp,
 (sep_simp simp: evm_sep)+,
 simp add: stateelm_means_simps stateelm_equiv_simps,
 erule_tac P="(_ \<and>* _)" in back_subst

method inst_sound_basic uses simp =
 inst_sound_set_eq,
 auto simp add: as_set_simps
(*
apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps)
apply(clarify)
apply(sep_simp simp: evm_sep; simp)
apply(simp split: instruction_result.splits)
apply(simp add: stateelm_means_simps stateelm_equiv_simps)
apply(simp add: vctx_next_instruction_def)
apply(clarsimp simp add: instruction_simps)
apply((sep_simp simp: evm_sep)+)
apply(simp add: stateelm_means_simps stateelm_equiv_simps)
apply(erule_tac P="(_ \<and>* _)" in back_subst)
apply(auto simp add: as_set_simps)
*)

lemma inst_stop_sem:
"triple_inst_sem net
  (\<langle> h \<le> 1024 \<and> 0 \<le> g\<rangle> \<and>* continuing \<and>* program_counter n \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
  (n, Misc STOP)
  (stack_height h \<and>* not_continuing \<and>* program_counter n \<and>* action (ContractReturn []) \<and>* gas_pred g \<and>* rest )"
apply(simp add:swap_inst_code_def triple_inst_sem_def program_sem.simps as_set_simps)
 apply(clarify)
 apply(simp split: instruction_result.splits)
   defer
  apply(sep_simp simp: continuing_sep; simp)
 apply(simp add: vctx_next_instruction_def)
 apply(split option.splits)
 apply(simp add: sep_conj_commute[where P="rest"])
 apply(clarify)
 apply(rule conjI)
  apply(clarsimp split:option.splits)
 apply(subgoal_tac "(case program_content (cctx_program co_ctx) (vctx_pc x1) of
               None \<Rightarrow> Some (Misc STOP) | Some i \<Rightarrow> Some i) =
              Some (Misc STOP)")
  apply(clarsimp)
  apply(sep_simp simp: program_counter_sep stack_height_sep pure_sep memory_usage_sep; simp)
  apply(rule conjI; rule impI; rule conjI; clarsimp;
  simp add: instruction_simps stop_def)
   apply(simp add: sep_fun_simps)
   apply(erule conjE)+
   apply(erule_tac P="(resta \<and>* rest)" in back_subst)
   apply(rule equalityI; rule subsetI; clarsimp)
  apply(simp add: memory_usage_elm_c_means stackHeightElmEquiv)
 apply(simp add: memory_usage_elm_c_means stackHeightElmEquiv)
 apply(sep_simp simp: gas_pred_sep; simp add: gasElmEquiv)
 apply(sep_simp simp: code_sep program_counter_sep)
 apply(simp add: codeElmEquiv pcElmEquiv)
 apply(simp split: option.splits)
 apply(rule allI; rule impI; simp)
done

method set_solve_arith_2_low=
  (erule_tac P="(_ \<and>* _)" in back_subst),
  (rule equalityI; rule subsetI; clarsimp simp add: as_set_simps;
   case_tac x; simp;
   clarify;
   case_tac "idx = length ta"; simp)

(*  apply(erule_tac P="(_ \<and>* _)" in back_subst)
  apply(rule equalityI; rule subsetI; clarsimp simp add: as_set_simps)
   apply(case_tac x; simp)
   apply(clarify)
   apply(case_tac "idx = length ta"; simp)
  apply(case_tac x; simp)
  apply(clarify)
  apply(case_tac "idx = length ta"; simp)*)

method set_solve =
(rule  Set.equalityI; rule subsetI; simp add: as_set_simps;
   (rename_tac elm);
   (case_tac elm; simp);
   (rename_tac pair);
   (case_tac pair; clarsimp));
(simp add: nth_append)?
(*apply(rule  Set.equalityI; rule subsetI; simp add: as_set_simps)
   apply(rename_tac elm)
   apply(case_tac elm; simp)
   apply(rename_tac pair)
   apply(case_tac pair; clarsimp)*)

(* From HoareTripleForInstructions2 *)
lemma tmp001:
"length lst = h \<Longrightarrow>
Suc (unat n) < h \<Longrightarrow>
unat n \<le> length (drop 1 lst)"
apply auto
done

lemma tmp000: "
a \<noteq> h - Suc 0 \<Longrightarrow> \<not> a < h - Suc (Suc (unat n)) \<Longrightarrow> a \<noteq> h - Suc (Suc (unat n)) \<Longrightarrow> 
a < h \<Longrightarrow> (Suc (a + unat n) - h) < unat n
"
apply auto
done

lemma tmp002:
 "a \<noteq> h - Suc 0 \<Longrightarrow> a < h
   \<Longrightarrow> Suc (h - Suc (Suc a)) = h - Suc a"
apply auto
done


lemma take_drop_nth :
  "length (vctx_stack x1) = h \<Longrightarrow>
   Suc (unat n) < h \<Longrightarrow>
   a \<noteq> h - Suc 0 \<Longrightarrow> \<not> a < h - Suc (Suc (unat n)) \<Longrightarrow> a \<noteq> h - Suc (Suc (unat n)) \<Longrightarrow>
   a < h \<Longrightarrow>
   rev (take (unat n) (drop (Suc 0) (vctx_stack x1))) ! (Suc (a + unat n) - h) = rev (vctx_stack x1) ! a"
  apply(simp add: tmp000 tmp001 tmp002 List.rev_nth min_absorb2)
done

lemma rev_lookup :
  "k < length lst \<Longrightarrow>
   rev lst ! (length lst - Suc k) = lst ! k"
apply(simp add: List.rev_nth)
done

lemma list_swap_usage :
  "n < length lst \<Longrightarrow>
   rev lst ! (length lst - Suc 0) = w \<Longrightarrow>
   rev lst ! (length lst - Suc n) = v \<Longrightarrow>
   list_swap n lst = Some ([v] @ take (n - 1) (drop 1 lst) @ [w] @ (drop (n + 1) lst))"
apply(subgoal_tac "0 < length lst")
 apply(simp add: rev_lookup list_swap_def)
apply auto
done

lemma inst_swap_sound:
notes
  if_split[split del]
shows
"triple_inst_sem net
        (\<langle> h \<le> 1023 \<and>
           Suc (unat n) \<le> h \<and> Gverylow \<le> g\<rangle> \<and>*
         stack_height (Suc h) \<and>*
         stack h w \<and>*
         stack (h - unat n - 1) v \<and>*
         program_counter k \<and>*
         gas_pred g \<and>* continuing \<and>* rest)
        (k, Swap n)
        (program_counter (k + 1) \<and>*
         gas_pred (g - Gverylow) \<and>*
         stack_height (Suc h) \<and>*
         stack h v \<and>*
         stack (h - unat n - 1) w \<and>*
         continuing \<and>* rest)"
apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps)
apply(clarify)
apply(sep_simp simp: evm_sep; simp)
apply(simp split: instruction_result.splits)
apply(simp add: stateelm_means_simps stateelm_equiv_simps)
apply(simp add: vctx_next_instruction_def set_diff_eq)
apply(clarsimp simp add: instruction_simps list_swap_usage)
apply((sep_simp simp: evm_sep; simp add: set_diff_eq)+)
apply(simp add: stateelm_means_simps stateelm_equiv_simps)
apply(rule conjI)
 apply(erule_tac P="(_ \<and>* _)" in back_subst)
 apply(rule equalityI; rule subsetI)
 		apply(clarsimp)
 apply(rename_tac elm; simp add: as_set_simps)
 apply(case_tac elm; clarsimp simp add: instruction_result_as_set_def stateelm_equiv_simps)
 		apply(rename_tac pair)
 		apply(case_tac "pair = length t - Suc (unat n)")
 		 apply(simp)
 		apply(clarsimp)
 		apply(case_tac "Suc (unat n) = length t")
 		 apply(clarsimp simp add: min_def short_rev_append)
 		 apply(simp add: rev_take rev_append_eq)
 		apply(simp add: rev_take rev_append_eq min_def)
 		apply(subgoal_tac "length t > 0"; clarsimp)
 		apply(split if_splits; clarsimp)
 		 apply(simp add: rev_nth)
 		 apply(subst (asm) Suc_diff_Suc)
 			apply(arith)
 		 apply(simp)
 		apply(simp add: rev_nth not_less nth_append split: if_splits)
 	 apply(clarsimp simp add: as_set_simps)
 	 apply(rename_tac elm, case_tac elm; simp)
 	  apply(clarsimp)
 	apply(rename_tac pair)
 		 		apply(case_tac "pair = length t - Suc (unat n)")
 		 apply(simp)
 		apply(clarsimp)
 		apply(case_tac "Suc (unat n) = length t")
 		 apply(clarsimp simp add: min_def short_rev_append)
 		 apply(simp add: rev_take rev_append_eq)
 		apply(simp add: rev_take rev_append_eq min_def)
 		apply(subgoal_tac "length t > 0"; clarsimp)
 		apply(split if_splits; clarsimp)
 		 apply(simp add: rev_nth)
 		 apply(subst (asm) Suc_diff_Suc)
 			apply(arith)
 		 apply(simp)
 		apply(simp add: rev_nth not_less nth_append split: if_splits)
apply(arith)
  done

		lemma variable_context_pc_change:
"variable_ctx_as_set (x1\<lparr>vctx_pc := vctx_pc x1 + 1\<rparr>) = insert (PcElm (vctx_pc x1 + 1)) (variable_ctx_as_set x1) - {PcElm (vctx_pc x1)}"
by (auto simp add: as_set_simps)

	lemma memory_elm_in_memory_range_elms:
	"x \<in> memory_range_elms memaddr v \<Longrightarrow> \<exists>a b. x = MemoryElm (a, b)"
	apply(induction v arbitrary: memaddr; simp)
	apply(erule disjE; simp)
	done

lemma memory_elm_in_memory_range_elms':
	"\<forall>a b. x \<noteq> MemoryElm (a,b) \<Longrightarrow> x \<notin> memory_range_elms m v"
	apply(rule notI)
	apply(drule memory_elm_in_memory_range_elms)
	apply(simp)
	done
		
		lemma memory_range_pc_update :
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
   x \<in> variable_ctx_as_set
               (x1
                \<lparr>vctx_pc := p \<rparr>) =
   (x \<in> variable_ctx_as_set x1)"
   by (auto simp: as_set_simps dest: memory_range_elms_all)

lemmas memory_range_elms_set_simps=
	memory_range_elms_in_c
	memory_range_in_minus_balance_as
	memory_range_in_union_balance
	memory_range_constant_union
	memory_range_in_caller
	memory_range_in_coinbase
	memory_range_insert_cont
	memory_range_elms_in_insert_continuing
	memory_range_elms_in_insert_contract_action
	memory_range_elms_in_insert_gas
	memory_range_elms_in_mu
	memory_range_in_origin
	memory_range_in_pc
	memory_range_in_sent_value
	not_memory_range_elms_all
	memory_range_elms_i
	memory_range_advance
	memory_range_elms_in_minus_statck_topmost
	memory_range_elms_logs_update
	memory_range_elms_update_balance
	memory_range_elms_update_memory_usage
	memory_gane_elms_in_stack_update
	memory_range_in_minus_balance
	memory_range_elms_in_x_minus_lognum
	memory_range_elms_in_minus_continuing
	memory_range_elms_in_minus_gas
	memory_range_elms_in_minus_mu
	memory_range_elms_in_minus_stack
	memory_range_elms_in_minus_stackheight
	memory_range_elms_in_minus_this
	memory_range_elms_not_account_existence
	memory_range_elms_not_code
	memory_range_elms_not_pc
	memory_range_elms_not_continuing
	memory_range_continue
	memory_range_advance_pc
	memory_range_balance
	memory_range_gas_update
	memory_range_memory_usage
	memory_range_stack
	memory_range_elms_cut_memory
	memory_elm_in_memory_range_elms
	memory_elm_in_memory_range_elms'
	memory_range_elms_all
	memory_range_pc_update

lemma inst_mload_sound :
notes
  unat_bintrunc[simp del]
shows
"triple_inst_sem net
  (\<langle> h \<le> 1023  \<and> g \<ge> Gverylow - Cmem memu + Cmem (M memu memaddr 32) \<and> memu \<ge> 0 \<and>
    length (word_rsplit v::byte list) = unat (32::w256)\<rangle> \<and>*
   stack h memaddr \<and>* stack_height (Suc h) \<and>* program_counter n \<and>*   
   memory_usage memu \<and>* memory memaddr v \<and>* gas_pred g \<and>* continuing \<and>* rest)
  (n, Memory MLOAD)
  (program_counter (n + 1) \<and>* stack_height (Suc h) \<and>* stack h v \<and>*
   memory memaddr v \<and>* memory_usage (M memu memaddr 32) \<and>*
   gas_pred (g - Gverylow + Cmem memu - Cmem (M memu memaddr 32)) \<and>*
   continuing \<and>* rest)"
  apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps instruction_sem_def)
  apply(clarify)
  apply(simp add: memory_def)
  apply(sep_simp simp: pure_sep)
  apply(sep_simp simp: evm_sep; simp)
  apply(simp add: memory_range_sep)
	apply(simp split: instruction_result.splits)
	apply(simp add: stateelm_means_simps stateelm_equiv_simps)
 	apply(simp add: memory_range_elms_set_simps)
	apply(cut_tac memory_range_elms_cut_memory[where lst="word_rsplit v"])
	apply(drule spec2[where x=memaddr and y=32]; simp)
  apply(drule mp, assumption)
  apply(simp add: vctx_next_instruction_def)
  apply(clarsimp)
  apply(simp add: instruction_simps)
  apply (unfold Let_def)
  apply (simp add: max_absorb2)
	apply((sep_simp simp: evm_sep)+)
  apply(simp add: variable_context_pc_change)
  apply(simp add: read_word_from_bytes_def unat_bintrunc byte_list_fill_right_def word_rcat_rsplit)
	apply(simp add: stateelm_means_simps stateelm_equiv_simps)
  apply(simp add: memory_range_elms_set_simps)
	apply(rule conjI)
   apply(erule_tac P="(_ \<and>* _)" in back_subst)
  apply(set_solve)
 	apply(clarsimp)
	apply(simp add: memory_range_elms_set_simps)
	apply(fastforce)
 done

	(*MSTORE*)
lemma store_list_mem_gt:
"unat (p - pos) \<ge> length lst \<Longrightarrow>
 store_byte_list_memory pos lst orig p = orig p"
apply(induction lst arbitrary: pos)
 apply(simp add: store_byte_list_memory_def)
apply(subst store_byte_list_memory_def)
apply(simp split: option.splits)
done

lemma store_list_mem_ls:
"unat (p - pos) < length lst \<Longrightarrow>
 store_byte_list_memory pos lst orig p = lst ! unat (p-pos)"
apply(induction lst arbitrary: pos)
 apply(simp add: store_byte_list_memory_def)
apply(subst store_byte_list_memory_def)
apply(simp split: option.splits)
done

lemma tmp003:
"n < 35 \<Longrightarrow> unat (x - p::w256) < n \<Longrightarrow> unat (x - p + 2) < Suc (Suc n)"
apply(subgoal_tac "unat (x-p+2)-2 < n")
 apply(auto)[1]
 using unat_add_lem
apply(insert unat_add_lem[where x="x-p" and y=2])[1]
apply(drule iffD1)
 apply(auto)
done

lemma  unat_minus_Suc:
" 0 < unat (x - pos::w256) \<Longrightarrow> unat (x - pos) = Suc (unat (x - (pos + 1)))"
apply(subgoal_tac "unat (1+ (x - (pos + 1))) = Suc (unat (x - (pos + 1)))")
 apply(auto)[1]
apply(rule unatSuc)
apply(simp add: unat_gt_0)
done

lemma store_blst_mem_append:
notes
  if_split[split del]
shows
"length lst < 32 \<Longrightarrow>
store_byte_list_memory pos (a # lst) orig =
((store_byte_list_memory (pos+1) lst orig)(pos:=a))"
apply(rule ext)
apply(induction lst arbitrary: pos a)
 apply(case_tac "unat (x - pos) < length [a]")
  apply(clarsimp simp add: store_list_mem_ls unat_eq_0)
 apply(clarsimp split: if_split)
 apply(rule conjI)
  apply(simp add: unat_gt_0)
 apply(simp add: store_list_mem_gt)
apply(case_tac "x=pos")
 apply(simp add: store_list_mem_ls)
apply(drule_tac x=x in meta_spec)
apply(drule_tac x="pos + 1" and y="a" in meta_spec2)
apply(drule meta_mp)
 apply(simp)
apply(clarsimp)
apply(case_tac "x=pos+1")
 apply(simp add: store_list_mem_ls)
apply(clarsimp)
apply(case_tac "unat (x-pos) < length (aa#a#lst)")
 apply(simp add: store_list_mem_ls)
 apply(drule sym)
 apply(simp)
 apply(subst store_list_mem_ls)
  apply(simp)
  apply(cut_tac pos=pos and x=x in unat_minus_Suc)
   apply(simp add: unat_gt_0)
  apply(simp)
 apply(insert unatSuc)[1]
 apply(drule_tac x="x - (pos + 1)" in meta_spec)
 apply(simp)
apply(simp add: store_list_mem_gt)
apply(drule sym, simp)
apply(subst store_list_mem_gt; simp)
apply(simp add: not_less_eq)
apply(cut_tac pos=pos and x=x in unat_minus_Suc)
 apply(simp add: unat_gt_0)
apply(simp)
done

lemma memory_as_set_append:
"memory_as_set
 (z(memaddr:=a)) =
insert (MemoryElm (memaddr, a))
(memory_as_set z - {MemoryElm (memaddr, z memaddr)})"
apply(simp add: memory_as_set_def)
apply(rule subset_antisym)
 apply(rule subsetI)
 apply(case_tac "x = (MemoryElm (memaddr, a))")
  apply(clarsimp)
 apply(clarsimp)
apply(rule subsetI)
apply(clarsimp)
apply(erule disjE)
 apply(simp)
apply(erule conjE)
apply(erule exE)
apply(rule_tac x=aa in exI)
apply(clarsimp)
done

lemma memory_elm_in_vctx:
"(MemoryElm (a,b)
   \<in> variable_ctx_as_set v) =
(MemoryElm (a,b)
   \<in> memory_as_set (vctx_memory v))"
by (auto simp add: as_set_simps)

lemma memory_range_elms_in_vctx:
"(memory_range_elms memaddr lst
   \<subseteq> variable_ctx_as_set v) =
(memory_range_elms memaddr lst
  \<subseteq> memory_as_set (vctx_memory v))"
by (auto simp add: as_set_simps memory_range_elms_set_simps)

lemma word_of_int_n0:
"0 < k \<Longrightarrow> k < 2^256\<Longrightarrow> (word_of_int k::w256) \<noteq> 0"
apply(subst zero_word_def)
apply(subst word_of_int_inj; simp)
done

lemma ind_memory_rg_elms:
"k > 0 \<Longrightarrow> k < 2^256 - int (length lst) \<Longrightarrow>
MemoryElm (m, b) \<notin> memory_range_elms (m + word_of_int k) lst"
apply(induction lst arbitrary:  k)
 apply(simp)
apply(rule notI)
apply(simp)
apply(simp add:word_of_int_n0)
apply(drule_tac x="k+1" in meta_spec)
apply(simp add: wi_hom_syms(5))
apply(simp add: word_succ_p1)
apply(subgoal_tac "m + word_of_int k + 1=m + (word_of_int k + 1)"; simp)
done

lemma memory_range_elms_in_store:
"length lst \<le> unat (32::w256) \<Longrightarrow>
memory_range_elms memaddr lst
   \<subseteq> memory_as_set
       (store_byte_list_memory memaddr lst mem)"
apply(induction lst arbitrary: memaddr; simp)
apply(rule context_conjI)
 apply(simp add: store_byte_list_memory_def memory_as_set_def)
apply(clarsimp)
apply(case_tac x; clarsimp simp add: stateelm_means_simps stateelm_equiv_simps memory_range_elms_set_simps)
apply(subst store_blst_mem_append, simp)
apply(simp add:  memory_as_set_append)
apply(case_tac "aa=memaddr")
 apply(simp)
 apply(cut_tac m=memaddr and k=1 and lst=lst and b=b in ind_memory_rg_elms; simp)
apply(simp)
apply(drule_tac x="memaddr + 1" in meta_spec)
apply(drule rev_subsetD; simp)
done

lemma diff_set_commute_sing:
"A - {b} - {c} = A - {c} - {b}"
by(auto)

lemma diff_memory_elms_commute_fst:
"A - {b} - memory_range_elms x y = A - memory_range_elms x y - {b}"
apply(induction y arbitrary: x; simp)
apply(rule subset_antisym; rule subsetI)
 apply(simp add: diff_set_commute_sing[where b="MemoryElm _"])+
done

lemma diff_memory_elms_commute_end:
"A - memory_range_elms x y - {b} = A - {b} - memory_range_elms x y"
apply(induction y arbitrary: x; simp)
apply(rule subset_antisym; rule subsetI)
 apply(simp add: diff_set_commute_sing[where b="MemoryElm _"])+
done

lemma memory_elms_out_of_range:
"length v \<le> unat (a - m) \<Longrightarrow>
 MemoryElm (a, b) \<notin> memory_range_elms m v"
apply(induction v arbitrary: m; simp)
apply(case_tac "a=m"; simp)
apply(drule_tac x="m+1" in meta_spec)
apply(drule meta_mp)
 apply(cut_tac pos=m in unat_minus_Suc[where x=a]; simp)
apply(simp)
done

lemma memory_elms_in_range:
"length lst < 2^256 \<Longrightarrow>
(unat (a - m) < length lst \<and>
 lst ! unat (a - m) = x ) =
 (MemoryElm (a, x) \<in> memory_range_elms m lst)"
apply(rule iffI)
apply(induction lst arbitrary: m; simp)
apply(case_tac "a=m"; simp)
apply(drule_tac x="m+1" in meta_spec)
apply(drule meta_mp)
  apply(cut_tac pos=m in unat_minus_Suc[where x=a];simp add: unat_gt_0)
 apply(cut_tac pos=m in unat_minus_Suc[where x=a];simp add: unat_gt_0)
apply(induction lst arbitrary: m; simp)
apply(case_tac "a=m"; simp)
 apply(erule disjE, simp)
 apply(cut_tac m=m and k=1 and lst=lst and b=x in ind_memory_rg_elms; simp)
apply(drule_tac x="m+1" in meta_spec)
apply(drule meta_mp)
  apply(cut_tac pos=m in unat_minus_Suc[where x=a];simp add: unat_gt_0)
 apply(cut_tac pos=m in unat_minus_Suc[where x=a];simp add: unat_gt_0)
  done
  	
  	lemma memory_elms_not_in_range:
"length lst < 2^256 \<Longrightarrow>
(MemoryElm (a, x) \<notin> memory_range_elms m lst) =
(\<not>(unat (a - m) < length lst \<and>
 lst ! unat (a - m) = x ))"
 			by(simp add: memory_elms_in_range)
 				
lemma elm_in_range_in_lst:
	"unat n < length lst \<Longrightarrow>
 MemoryElm (m+ n, lst ! unat n) \<in> memory_range_elms m lst"
	apply(induction lst arbitrary:n m; simp)
	apply(subst disj_commute)
	apply(rule disjCI)
	apply(clarsimp)
	apply(case_tac "n=0"; simp)
		apply(drule_tac x="n - 1" and y="m+1" in meta_spec2)
	apply(drule meta_mp)
	 apply(simp add: unat_minus_one )
	 apply(subst less_diff_conv2)
	  apply(subst (asm) word_neq_0_conv)
	  apply(subst (asm) word_less_nat_alt)
	  apply(arith)
	 apply(arith)
	apply(simp add: unat_minus_one)
		apply(subgoal_tac "unat n > 0"; simp)
			  apply(simp add:  word_neq_0_conv word_less_nat_alt)
	done
		
lemma in_mem_not_in_range:
	"length lst < 2^256 \<Longrightarrow>
	memory_range_elms m lst \<subseteq> memory_as_set (vctx_memory x) \<Longrightarrow>
	MemoryElm (a, b) \<in> memory_as_set (vctx_memory x) \<Longrightarrow>
	MemoryElm (a, b) \<notin> memory_range_elms m lst \<Longrightarrow>
	unat (a - m) \<ge> length lst"
	apply(simp add: memory_as_set_def)
	apply(simp add: memory_elms_not_in_range)
	apply(case_tac "length lst \<le> unat (a - m)"; simp)
	apply(simp add: not_le)
	apply(simp add: subset_eq Ball_def)
	apply(insert elm_in_range_in_lst[where n="a-m" and m=m and lst=lst], simp)
	apply(drule spec[where x="MemoryElm (a, lst ! unat (a - m))"])
	apply(simp)
	done
		
lemma vctx_memory_store_memory_set_eq:
"length (word_rsplit v::byte list) < 2^256 \<Longrightarrow>
memory_range_elms memaddr (word_rsplit old_v)
    \<subseteq> memory_as_set (vctx_memory x1) \<Longrightarrow>
    length (word_rsplit old_v::byte list) =  length (word_rsplit v::byte list) \<Longrightarrow>
    memory_range_elms memaddr (word_rsplit v)
    \<subseteq> memory_as_set (store_word_memory memaddr v (vctx_memory x1)) \<Longrightarrow>
    contexts_as_set
     (x1\<lparr>vctx_memory := store_word_memory memaddr v (vctx_memory x1)\<rparr>)
     co_ctx -
    memory_range_elms memaddr (word_rsplit v) =
    contexts_as_set x1 co_ctx -
    memory_range_elms memaddr (word_rsplit old_v)"
apply(simp add: contexts_as_set_def)
apply(rule subset_antisym; rule subsetI)
	 apply(case_tac "\<exists>a b. x = MemoryElm (a,b)")
	  apply(clarsimp simp add: memory_elm_not_constant memory_range_elms_set_simps)
	  apply(simp add: memory_elms_not_in_range)
	  apply(rule conjI)
	  		apply(thin_tac " _ \<subseteq> _", thin_tac "_=_", thin_tac "_\<subseteq>_")
		 apply(simp add: stateelm_means_simps stateelm_equiv_simps)
		 apply(simp add: store_word_memory_def store_byte_list_memory_def)
	apply(split option.splits; clarsimp)
		apply(clarsimp)
		apply(simp add: stateelm_means_simps stateelm_equiv_simps)
 apply(simp add: store_word_memory_def store_byte_list_memory_def)
 apply(rename_tac elm, case_tac elm; simp add: stateelm_means_simps memory_range_elms_set_simps stateelm_equiv_simps)
 apply(simp add: as_set_simps)
 	 apply(simp add: as_set_simps)
 	  
 	apply(case_tac "\<exists>a b. x = MemoryElm (a,b)")
 	 prefer 2
 	  apply(rename_tac elm, case_tac elm; simp add: stateelm_means_simps memory_range_elms_set_simps stateelm_equiv_simps)
 apply(simp add: as_set_simps)
 apply(simp add: as_set_simps)

	  apply(clarsimp simp add: memory_elm_not_constant memory_range_elms_set_simps)
	apply(simp add: memory_elm_in_vctx)
	apply(insert in_mem_not_in_range[where m=memaddr])
		apply(drule_tac x="word_rsplit old_v::byte list" and y="x1"in meta_spec2)
	apply(drule_tac x=a and y=b in meta_spec2)
		apply(clarsimp)
	apply(subst memory_elms_not_in_range, simp)
	  		apply(thin_tac " _ \<subseteq> _", thin_tac "_=_", thin_tac "_\<subseteq>_")
		 apply(simp add: memory_as_set_def)
		 apply(simp add: store_word_memory_def store_byte_list_memory_def)
done

lemma memory_in_mem_as_set:
"x \<in> memory_as_set m \<Longrightarrow> \<exists>a b. x= MemoryElm (a,b)"
by(auto simp add: as_set_simps)


lemma inst_mstore_sound :
notes
  unat_bintrunc[simp del]
shows
"triple_inst_sem net
  (\<langle> h \<le> 1022 \<and> g \<ge> Gverylow - Cmem memu + Cmem (M memu memaddr 32) \<and> memu \<ge> 0 \<and>
    length (word_rsplit old_v::byte list) = unat (32::w256) \<and>
    length (word_rsplit v::byte list) = unat (32::w256) \<and> memaddr \<le> -32\<rangle> \<and>*
   stack (h+1) memaddr \<and>* stack h v \<and>* stack_height (h+2) \<and>*
   program_counter n \<and>* memory_usage memu \<and>*
   memory memaddr old_v \<and>* gas_pred g \<and>* continuing \<and>* rest)
  (n, Memory MSTORE)
  (program_counter (n + 1) \<and>* stack_height h \<and>* memory memaddr v \<and>* 
   gas_pred (g - Gverylow + Cmem memu - Cmem (M memu memaddr 32)) \<and>*
   memory_usage (M memu memaddr 32) \<and>* continuing \<and>* rest)"
apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps instruction_sem_def)
apply(clarify)
apply(simp add: memory_def)
apply(sep_simp simp: pure_sep)
	apply(sep_simp simp: evm_sep; simp, (erule conjE)?)+
	apply(simp split: instruction_result.splits add: memory_range_sep)
	apply(simp add: stateelm_means_simps stateelm_equiv_simps)
apply(simp add: vctx_next_instruction_def)
apply(clarsimp simp add: rev_nth)
apply(simp add: instruction_simps Let_def max_absorb2)
apply(subst conj_commute, rule context_conjI)
	apply(simp add: memory_range_elms_set_simps)
	apply(simp add: store_word_memory_def memory_range_elms_in_vctx)
  apply(simp only: memory_range_elms_in_store)
apply(erule_tac P="(_ \<and>* _)" in back_subst)
apply(simp add: diff_set_commute_sing[where c="ContinuingElm True"])
	apply(simp add: diff_memory_elms_commute_fst  memory_range_elms_in_vctx)
	apply(simp add: memory_range_elms_set_simps)
	apply(rule subst[OF vctx_memory_store_memory_set_eq[where old_v=old_v and v=v]]; simp?)
		apply(simp add:  memory_range_elms_in_vctx)
		apply(simp add: store_word_memory_def memory_range_elms_in_store)
		 apply(subgoal_tac "unat (32::w256) = 32"; simp add: unat_def)
		apply(simp add: memory_range_elms_in_vctx)
		apply(simp add: memory_range_elms_in_vctx)
		 apply(simp add: diff_memory_elms_commute_end)
apply(rule arg_cong[where f="\<lambda>u. u - memory_range_elms _ _"])
apply(rule subset_antisym; rule subsetI)
apply(simp add: memory_range_elms_set_simps)
	 apply(case_tac "\<exists>a b. x= MemoryElm (a,b)"; clarsimp)
	  	apply(simp add: stateelm_means_simps stateelm_equiv_simps)
	 apply(case_tac x; clarsimp simp add: stateelm_means_simps stateelm_equiv_simps)
	 apply(case_tac "a=length ta"; clarsimp)
	 apply(case_tac "a<length ta"; clarsimp)
	 apply(erule notE, simp add: short_rev_append)
	apply(clarsimp)
	apply(case_tac x; clarsimp simp add: stateelm_means_simps stateelm_equiv_simps)
	apply(simp add: short_rev_append)
	done

lemma inst_return_sem :
notes
  if_split[split del]
shows
  "triple_inst_sem net
    (\<langle> h \<le> 1022 \<and> m \<ge> 0 \<and> length lst = unat v \<and> (Cmem (M m u v) - Cmem m) \<le> g \<rangle> \<and>*
     continuing \<and>* memory_usage m \<and>* memory_range u lst \<and>*
     program_counter n \<and>* stack_height (Suc (Suc h)) \<and>* gas_pred g \<and>*
     stack (Suc h) u \<and>* stack h v \<and>* rest)
    (n, Misc RETURN)
    (stack_height (Suc (Suc h)) \<and>* not_continuing \<and>* memory_usage (M m u v) \<and>*
     action (ContractReturn lst) \<and>* gas_pred (g - (Cmem (M m u v) - Cmem m)) \<and>*
     stack (Suc h) u \<and>* stack h v \<and>* memory_range u lst \<and>*
     program_counter n \<and>* rest)"
 apply(simp add: triple_inst_sem_def)
 apply(simp add: program_sem.simps  as_set_simps instruction_sem_def)
 apply(clarify)
 apply(case_tac presult; clarsimp)
   defer
   apply(simp add: as_set_simps)
   apply(sep_simp simp: continuing_sep; clarsimp)
 apply(sep_simp simp: pure_sep)
 			apply(sep_simp simp: evm_sep, simp?, (erule conjE)?)+
 				 apply(simp add: instruction_simps vctx_returned_bytes_def)
 			apply(simp add: stateelm_means_simps stateelm_equiv_simps)
 				apply(simp add: memory_range_sep memory_range_elms_set_simps)
 apply(clarify)
 apply(clarsimp)
 			apply(simp add: instruction_simps Let_def max_absorb2)
 				apply(simp add: stateelm_means_simps stateelm_equiv_simps)
 				apply(simp add: vctx_returned_bytes_def memory_range_elms_cut_memory)
 apply(rule conjI)
 			 apply(erule_tac P="(_ \<and>* _)" in back_subst)
 			  
 			 apply(auto simp add: as_set_simps )[1]
 			apply(thin_tac "(_ \<and>* _) _")
  		apply(subst (asm) subset_eq)
  		apply(simp add: Ball_def)
  		apply(clarsimp simp add: memory_range_elms_set_simps)
  			apply(drule_tac x=x in spec, simp)
  		apply(drule memory_elm_in_memory_range_elms)
  			apply(clarsimp)
  		apply(simp add: stateelm_means_simps stateelm_equiv_simps)
  done

  	lemma inst_dup_sound:
"triple_inst_sem net
  (\<langle> h \<le> 1023 \<and> unat n < h \<and> Gverylow \<le> g\<rangle> \<and>*
   stack_height h \<and>* stack (h - unat n - 1) w \<and>*
   program_counter k \<and>* gas_pred g \<and>* continuing \<and>* rest)
  (k, Dup n)
  (program_counter (k + 1) \<and>* gas_pred (g - Gverylow) \<and>*
   stack_height (Suc h) \<and>* stack (h - unat n - 1) w \<and>*
   stack h w \<and>* continuing \<and>* rest)"
apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps)
apply(clarify)
apply(sep_simp simp: evm_sep; simp)
apply(simp split: instruction_result.splits)
apply(simp add: stateelm_means_simps stateelm_equiv_simps)
apply(simp add: vctx_next_instruction_def)
apply(clarsimp simp add: instruction_simps Let_def max_absorb2)
apply((sep_simp simp: evm_sep)+)
apply(simp add: stateelm_means_simps stateelm_equiv_simps)
			apply(simp add: rev_lookup)
			apply(subst conj_commute)
			apply(rule context_conjI)
			 apply(rule conjI)
			  apply(arith)
			 apply(rule conjI)
			  apply(simp add: short_rev_append rev_nth)
			  apply(arith)
			apply(erule_tac P="(_ \<and>* _)" in back_subst)
apply(set_solve)
      done


lemma inst_suicide_sem:
 "triple_inst_sem net
  (\<langle> h \<le> 1024 \<and> Csuicide (\<not> existence) net \<le> g \<and> at_least_eip150 net\<rangle> \<and>*
   continuing \<and>* account_existence addr existence \<and>*
   program_counter n \<and>* stack_height (Suc h) \<and>* gas_pred g \<and>* stack h (ucast addr) \<and>* rest)
  (n, Misc SUICIDE)
  (stack_height (Suc h) \<and>* stack h (ucast addr) \<and>*
   not_continuing \<and>*  account_existence addr existence \<and>*
   program_counter n \<and>* action (ContractSuicide addr) \<and>* gas_pred (g - Csuicide (\<not> existence) net) \<and>* rest)"
  apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps)
  apply(clarify)
  apply(sep_simp simp: evm_sep; simp)
  apply(simp split: instruction_result.splits)
  apply(simp add: stateelm_means_simps stateelm_equiv_simps)
  apply(simp add: vctx_next_instruction_def)
  apply(clarsimp simp add: instruction_simps)
  apply(simp add:  vctx_recipient_def vctx_next_instruction_default_def vctx_next_instruction_def)
  apply(subgoal_tac "ucast (ucast addr::w256) = addr")
   apply(simp)
   apply((sep_simp simp: evm_sep)+)
   apply(simp add: stateelm_means_simps stateelm_equiv_simps)
   apply(erule_tac P="(_ \<and>* _)" in back_subst)
   apply(set_solve)
  apply(subst ucast_ucast_mask)
  apply(simp add: mask_def)
 done

lemma triple_inst_soundness:
notes
  if_split[split del]
shows
  "triple_inst net p i q \<Longrightarrow> triple_inst_sem net p i q"
  apply(induction rule:triple_inst.induct)
              apply(erule triple_inst_arith.cases; clarsimp)
                       apply(inst_sound_set_eq, set_solve)
                      apply(split if_split, rule conjI, rule impI)
                      apply(inst_sound_set_eq, set_solve)+
                     apply(split if_split, rule conjI, rule impI)
                      apply(inst_sound_set_eq, set_solve)
                     apply(inst_sound_set_eq, set_solve)
                    apply(inst_sound_set_eq, set_solve)
                   apply(inst_sound_set_eq, set_solve)
                  apply(inst_sound_set_eq, set_solve)
                 apply(inst_sound_set_eq, set_solve)
                apply(inst_sound_set_eq, set_solve)
               apply(split if_split, rule conjI, rule impI)
                apply(inst_sound_set_eq, set_solve)
               apply(inst_sound_set_eq, set_solve)
              apply(split if_split, rule conjI, rule impI)
               apply(inst_sound_set_eq, set_solve)
              apply(inst_sound_set_eq, set_solve)
             apply(inst_sound_set_eq simp: iszero_stack_def, set_solve)
            apply(erule triple_inst_bits.cases; clarsimp)
                apply(inst_sound_set_eq, set_solve)
               apply(inst_sound_set_eq, set_solve)
              apply(inst_sound_set_eq, set_solve)
             apply(inst_sound_set_eq, set_solve)
            apply(inst_sound_set_eq, set_solve)
           apply(erule triple_inst_info.cases; clarsimp)
              apply(inst_sound_set_eq, set_solve)
             apply(inst_sound_set_eq simp: datasize_def, set_solve)
            apply(inst_sound_set_eq, set_solve)
           apply(erule triple_inst_memory.cases; clarsimp)
  					  apply(rule inst_mload_sound[simplified])
  				 apply(rule inst_mstore_sound[simplified])
        apply(erule triple_inst_storage.cases; clarsimp)
         apply(inst_sound_set_eq, set_solve)
          apply(inst_sound_set_eq, set_solve)
  					apply(erule triple_inst_misc.cases; clarsimp)
  					 apply(rule inst_stop_sem)
  				  apply(rule inst_return_sem)
           apply(rule inst_suicide_sem)
    apply(erule triple_inst_pc.cases; clarsimp)
     apply(inst_sound_set_eq, set_solve)
    apply(inst_sound_set_eq, set_solve)
   apply(erule triple_inst_stack.cases; clarsimp)
    apply(inst_sound_set_eq simp: constant_mark_def, set_solve)
    		apply(inst_sound_set_eq, set_solve)
    apply(inst_sound_set_eq simp: cut_data_def, set_solve)
    	apply(rule inst_swap_sound)
  	 apply(rule inst_dup_sound)
  	apply(inst_sound_set_eq, set_solve)
 apply(simp add: inst_strengthen_pre_sem)
apply(simp add: inst_false_pre_sem)
done

(* Soundness proof for triple_seq rules *)

lemma inst_seq_eq:
"triple_inst net P i Q \<Longrightarrow> triple_seq_sem net P [i] Q"
 apply(drule triple_inst_soundness)
 apply(simp add: triple_inst_sem_def triple_seq_sem_def)
done

lemma seq_compose_soundness:
"triple_seq_sem net P xs R \<Longrightarrow> triple_seq_sem net R ys Q \<Longrightarrow> triple_seq_sem net P (xs@ys) Q "
 apply(simp (no_asm) add: triple_seq_sem_def)
 apply clarsimp
 apply(subst (asm) triple_seq_sem_def[where pre=P])
 apply clarsimp
 apply(rename_tac co_ctx presult rest stopper)
 apply(drule_tac x = "co_ctx" in spec)
 apply(drule_tac x = "presult" in spec)
 apply(drule_tac x = "code ((set ys) - (set xs)) ** rest" in spec)
 apply(simp add: code_more sep_conj_commute sep_conj_left_commute)
 apply(drule_tac x = stopper in spec)
 apply(clarsimp simp add: triple_seq_sem_def)
 apply(drule_tac x = "co_ctx" in spec)
 apply(drule_tac x = "program_sem stopper co_ctx (length xs) net presult" in spec)
 apply(drule_tac x = "code ((set xs) - (set ys)) ** rest" in spec)
 apply(simp add: code_more sep_conj_commute sep_conj_left_commute code_union_comm)
 apply(drule_tac x = stopper in spec)
 apply(simp add: execution_continue)
done

lemma triple_seq_empty:
"(\<And>s. pre s \<longrightarrow> post s) \<Longrightarrow> triple_seq_sem net pre [] post"
 apply (simp add: triple_seq_sem_def program_sem.simps imp_sepL)
 apply(clarify)
 apply(drule allI)
 apply(simp add: imp_sepL)
done

lemma seq_strengthen_pre_sem:
  assumes  "triple_seq_sem net P c Q"
  and      "(\<forall> s. R s \<longrightarrow> P s)"
  shows    " triple_seq_sem net R c Q"
  using assms(1)
  apply (simp add: triple_seq_sem_def)
  apply(clarify)
  apply(drule_tac x = co_ctx in spec)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
   apply(erule impE)
   apply(sep_drule assms(2)[rule_format])
   apply assumption
  apply simp
done

lemma triple_seq_soundness:
"triple_seq net P xs Q \<Longrightarrow> triple_seq_sem net P xs Q"
 apply(induction rule: triple_seq.induct)
    apply(drule inst_seq_eq)
    apply(rename_tac pre x q xs post)
    apply(subgoal_tac "x#xs = [x]@xs")
     apply(simp only: seq_compose_soundness)
    apply(simp)
   apply(simp add: triple_seq_empty)
  apply(simp add: seq_strengthen_pre_sem)
 apply(simp add: triple_seq_sem_def pure_sep)
done

(* How to compose program_sem and program_sem_t_alt *)

lemma program_sem_t_exec_continue_1:
" program_sem_t co_ctx net
   (program_sem stopper co_ctx (Suc 0) net presult) =
  program_sem_t co_ctx net presult"
 apply(case_tac presult)
   apply(simp add: program_sem.simps next_state_def)
   apply(insert program_sem_t_no_gas_not_continuing)[1]
   apply(drule_tac x=x1 and y=co_ctx in meta_spec2)
   apply(drule_tac x=net in meta_spec)
   apply(simp split: option.splits)
   apply (rule conjI)
    apply (simp add: program_sem_t.simps)
   apply clarsimp
   apply (simp add: program_sem_t.simps)
   apply(clarsimp)
   apply(simp add: check_resources_def)
   apply(case_tac "inst_stack_numbers x2"; clarsimp)
   apply(case_tac "instruction_sem x1 co_ctx x2 net")
     apply(drule_tac x=x1a in spec; simp)
    apply (simp)+
  apply (simp add: program_sem.simps next_state_def)
done

lemma program_sem_t_exec_continue:
"program_sem_t co_ctx net (program_sem stopper co_ctx k net presult) =
       program_sem_t co_ctx net presult"
 apply(induction k arbitrary: presult)
  apply(simp add: program_sem.simps next_state_def)
 apply(drule_tac x="program_sem stopper co_ctx 1 net presult" in meta_spec)
 apply(simp add:program_sem_t_exec_continue_1 execution_continue)
done

(* Define the semantic of triple_blocks using program_sem_t and prove it sound *)

definition triple_blocks_sem_t :: "network \<Rightarrow> basic_blocks \<Rightarrow> pred \<Rightarrow> vertex \<Rightarrow> pred \<Rightarrow> bool" where
"triple_blocks_sem_t net c pre v post ==
    \<forall> co_ctx presult rest (stopper::instruction_result \<Rightarrow> unit).
        wf_blocks c \<longrightarrow>
        block_lookup c (v_ind v) = Some (snd v) \<longrightarrow>
       (pre ** code (blocks_insts c) ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       ((post ** code (blocks_insts c) ** rest) (instruction_result_as_set co_ctx
            (program_sem_t co_ctx net presult))) "

(* Lemmas to group code elements *)
lemma block_in_insts_:
"(n, b, t) \<in> set c \<Longrightarrow>
    set b \<subseteq> set (rebuild_with_add c)"
apply(induction c)
 apply(simp)
apply(simp)
apply(erule disjE)
 apply(clarsimp)
 apply(case_tac t; simp)
apply(case_tac a)
apply(case_tac ca; simp)
apply(auto)
done

lemma block_in_insts:
"block_lookup c n = Some (b, t) \<Longrightarrow>
set b \<subseteq> blocks_insts c"
apply(simp add: blocks_insts_def)
apply(drule map_of_SomeD)
apply(simp add: block_in_insts_)
done

lemma block_in_insts_wf:
"wf_blocks c \<Longrightarrow>
block_lookup c n = Some (b, t) \<Longrightarrow>
set b \<subseteq> blocks_insts c"
by(simp add: block_in_insts wf_blocks_def)

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
"Q \<inter> P = {} \<Longrightarrow> P \<subseteq> R - Q \<Longrightarrow> P \<subseteq> R"
by auto

lemma code_code_sep_:
"P \<subseteq> Q \<Longrightarrow>
(code P \<and>* code (Q - P) \<and>* r) s =
(code Q \<and>* r) s"
 apply(simp add: code_sep)
 apply(rule iffI; rule conjI; (erule conjE)+)
		apply(simp add: code_decomp)
		apply(subgoal_tac "{CodeElm (pos, i) |pos i. (pos, i) \<in> P} \<inter> {CodeElm (pos, i) |pos i.
         (pos, i) \<in> Q \<and> (pos, i) \<notin> P} = {}")
		 apply(simp add: subset_minus)[1]
		apply(auto)[1]
	 apply(auto simp add: subset_minus set_diff_eq  code_decomp Un_commute)[1]
	apply(subgoal_tac "{CodeElm (pos, i) |pos i.
     (pos, i) \<in> Q \<and> (pos, i) \<notin> P} \<subseteq> {CodeElm (pos, i) |pos i.
     (pos, i) \<in> Q}")
	 apply(auto)[1]
	apply(auto)[1]
 apply(auto simp add: subset_minus set_diff_eq code_decomp Un_commute)
done

lemma code_code_sep:
"block_lookup blocks = map_of (all_blocks blocks) \<Longrightarrow>
block_lookup blocks n = Some (insts, ty) \<Longrightarrow>
(code (set insts) \<and>* code (blocks_insts blocks - set insts) \<and>* r) s =
(code (blocks_insts blocks) \<and>* r) s"
 apply(subgoal_tac "set insts \<subseteq> blocks_insts blocks")
	apply(simp only: code_code_sep_)
 apply(simp add: block_in_insts)
done


lemma code_code_sep_wf:
"wf_blocks blocks \<Longrightarrow>
block_lookup blocks n = Some (insts, ty) \<Longrightarrow>
(code (set insts) \<and>* code (blocks_insts blocks - set insts) \<and>* r) s =
(code (blocks_insts blocks) \<and>* r) s"
by(simp add: wf_blocks_def code_code_sep)


lemma sep_code_code_sep:
"block_lookup blocks = map_of (all_blocks blocks) \<Longrightarrow>
block_lookup blocks n = Some (insts, ty) \<Longrightarrow>
(p \<and>* code (set insts) \<and>* code (blocks_insts blocks - set insts) \<and>* r) s =
(p \<and>* code (blocks_insts blocks) \<and>* r) s"
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

lemma sep_code_code_sep_wf:
"wf_blocks blocks \<Longrightarrow>
block_lookup blocks n = Some (insts, ty) \<Longrightarrow>
(p \<and>* code (set insts) \<and>* code (blocks_insts blocks - set insts) \<and>* r) s =
(p \<and>* code (blocks_insts blocks) \<and>* r) s"
by(simp add: wf_blocks_def sep_code_code_sep)

lemma sep_sep_sep_code_code:
"block_lookup blocks = map_of (all_blocks blocks) \<Longrightarrow>
block_lookup blocks n = Some (insts, ty) \<Longrightarrow>
(p \<and>* q \<and>* r \<and>* code (set insts) \<and>* code (blocks_insts blocks - set insts)) s =
(p \<and>* q \<and>* r \<and>* code (blocks_insts blocks)) s"
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

(*NEXT case *)

lemma blocks_next_sem_t:
" wf_blocks blocks \<Longrightarrow>
 block_lookup blocks n = Some (insts, Next) \<Longrightarrow>
 block_lookup blocks (n + inst_size_list insts) = Some (bi, ti) \<Longrightarrow>
 triple_seq net pre insts	(program_counter (n + inst_size_list insts) \<and>* q) \<Longrightarrow>
 triple_sem_t net
	(program_counter (n + inst_size_list insts) \<and>* q)
	(blocks_insts blocks) post \<Longrightarrow>
 triple_sem_t net pre (blocks_insts blocks) post"
 apply(drule triple_seq_soundness)
 apply(simp only: triple_seq_sem_def triple_sem_t_def)
 apply(rule allI)+
 apply(clarify)
 apply(rename_tac co_ctx presult rest stopper)
 apply(drule_tac x = "co_ctx" in spec)+
 apply(drule_tac x = "(program_sem stopper co_ctx (length insts) net presult)" in spec)
 apply(drule_tac x = "rest" in spec)
 apply(drule_tac x = presult in spec)
 apply(drule_tac x = "code (blocks_insts blocks - set insts) \<and>* rest" in spec)
 apply(simp add: sep_code_code_sep_wf)
 apply(drule_tac x = "stopper" in spec)
 apply(sep_select_asm 4, sep_select_asm 4)
 apply(simp add: code_code_sep_wf)
 apply(sep_select_asm 3, sep_select_asm 3, simp)
 apply (erule_tac P="(post \<and>* code (blocks_insts blocks) \<and>* rest)" in back_subst)
 apply(subst program_sem_t_exec_continue )
 apply(simp)
done

(* Definition of uniq_stateelm to say that a set have a most one element for some state elements *)

definition
 uniq_stateelm :: "state_element set \<Rightarrow> bool"
where
 "uniq_stateelm s ==
(\<forall>v. PcElm v \<in> s \<longrightarrow> (\<forall>x. PcElm x \<in> s \<longrightarrow> x = v)) \<and>
(\<forall>v. GasElm v \<in> s \<longrightarrow> (\<forall>x. GasElm x \<in> s \<longrightarrow> x = v)) \<and>
(\<forall>v. StackHeightElm v \<in> s \<longrightarrow> (\<forall>v'. StackHeightElm v' \<in> s \<longrightarrow> v' = v)) \<and>
(\<forall>h v. StackElm (h, v) \<in> s \<longrightarrow> (\<forall>v'. StackElm (h, v') \<in> s \<longrightarrow> v' = v)) \<and>
(\<forall>v. StackHeightElm v \<in> s \<longrightarrow> (\<forall>h u. h \<ge> v \<longrightarrow> StackElm (h,u) \<notin> s)) \<and>
(\<forall>h v. MemoryElm (h, v) \<in> s \<longrightarrow> (\<forall>v'. MemoryElm (h, v') \<in> s \<longrightarrow> v' = v)) \<and>
(\<forall>h v. StorageElm (h, v) \<in> s \<longrightarrow> (\<forall>v'. StorageElm (h, v') \<in> s \<longrightarrow> v' = v)) \<and>
(\<forall>v. MemoryUsageElm v \<in> s \<longrightarrow> (\<forall>x. MemoryUsageElm x \<in> s \<longrightarrow> x = v))"

lemma uniq_gaselm:
"s = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>v. GasElm v \<in> s \<longrightarrow> (\<forall>x. GasElm x \<in> s \<longrightarrow> x = v))"
by(simp add:instruction_result_as_set_def gasElmEquiv split:instruction_result.splits)

lemma uniq_gaselm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = s + y \<Longrightarrow>
(\<forall>v. GasElm v \<in> s \<longrightarrow> (\<forall>x. GasElm x \<in> s \<longrightarrow> x = v))"
by (drule sym, drule uniq_gaselm, simp add: plus_set_def)

lemma uniq_pcelm:
"s = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>v. PcElm v \<in> s \<longrightarrow> (\<forall>x. PcElm x \<in> s \<longrightarrow> x = v))"
by(simp add:instruction_result_as_set_def pcElmEquiv split:instruction_result.splits)

lemma uniq_pcelm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = s + y \<Longrightarrow>
(\<forall>v. PcElm v \<in> s \<longrightarrow> (\<forall>x. PcElm x \<in> s \<longrightarrow> x = v))"
by (drule sym, drule uniq_pcelm, simp add: plus_set_def)

lemma uniq_stackheightelm:
"x = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>v. StackHeightElm v \<in> x \<longrightarrow> (\<forall>v'. StackHeightElm v' \<in> x \<longrightarrow> v' = v))"
by (simp add:instruction_result_as_set_def stackHeightElmEquiv split:instruction_result.splits)

lemma uniq_stackheightelm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = x + y \<Longrightarrow>
(\<forall>v. StackHeightElm v \<in> x \<longrightarrow> (\<forall>v'. StackHeightElm v' \<in> x \<longrightarrow> v' = v))"
by (drule sym, drule uniq_stackheightelm, simp add: plus_set_def)

lemma uniq_stackelm:
"x = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>h v. StackElm (h, v) \<in> x \<longrightarrow> (\<forall>v'. StackElm (h, v') \<in> x \<longrightarrow> v' = v))"
by (simp add:instruction_result_as_set_def stackElmEquiv split:instruction_result.splits)

lemma uniq_stackelm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = x + y \<Longrightarrow>
(\<forall>h v. StackElm (h, v) \<in> x \<longrightarrow> (\<forall>v'. StackElm (h, v') \<in> x \<longrightarrow> v' = v))"
by (drule sym, drule uniq_stackelm, simp add: plus_set_def)

lemma stack_max_elm:
"s = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>v. StackHeightElm v \<in> s \<longrightarrow> (\<forall>h u. h \<ge> v \<longrightarrow> StackElm (h,u) \<notin> s))"
by(simp add:instruction_result_as_set_def stackHeightElmEquiv stackElmEquiv split:instruction_result.splits)

lemma stack_max_elm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = s + y \<Longrightarrow>
(\<forall>v. StackHeightElm v \<in> s \<longrightarrow> (\<forall>h u. h \<ge> v \<longrightarrow> StackElm (h,u) \<notin> s))"
	by (drule sym, drule stack_max_elm, simp add: plus_set_def)
		
lemma uniq_memuelm:
"x = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>v. MemoryUsageElm v \<in> x \<longrightarrow> (\<forall>v'. MemoryUsageElm v' \<in> x \<longrightarrow> v' = v))"
by (simp add:instruction_result_as_set_def memory_usage_elm_c_means split:instruction_result.splits)

lemma uniq_memuelm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = x + y \<Longrightarrow>
(\<forall>v. MemoryUsageElm v \<in> x \<longrightarrow> (\<forall>v'. MemoryUsageElm v' \<in> x \<longrightarrow> v' = v))"
by (drule sym, drule uniq_memuelm, simp add: plus_set_def)
		
lemma uniq_memelm:
"x = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>h v. MemoryElm (h, v) \<in> x \<longrightarrow> (\<forall>v'. MemoryElm (h, v') \<in> x \<longrightarrow> v' = v))"
by (simp add:instruction_result_as_set_def memory_elm_means split:instruction_result.splits)

lemma uniq_memelm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = x + y \<Longrightarrow>
(\<forall>h v. MemoryElm (h, v) \<in> x \<longrightarrow> (\<forall>v'. MemoryElm (h, v') \<in> x \<longrightarrow> v' = v))"
by (drule sym, drule uniq_memelm, simp add: plus_set_def)

lemma uniq_storageelm:
"x = instruction_result_as_set co_ctx presult \<Longrightarrow>
(\<forall>h v. StorageElm (h, v) \<in> x \<longrightarrow> (\<forall>v'. StorageElm (h, v') \<in> x \<longrightarrow> v' = v))"
  by(simp add: as_set_simps split:instruction_result.splits)

lemma uniq_storageelm_plus[rule_format]:
"instruction_result_as_set co_ctx presult = x + y \<Longrightarrow>
(\<forall>h v. StorageElm (h, v) \<in> x \<longrightarrow> (\<forall>v'. StorageElm (h, v') \<in> x \<longrightarrow> v' = v))"
by (drule sym, drule uniq_storageelm, simp add: plus_set_def)

lemmas uniq_stateelm_simps=
uniq_stateelm_def
uniq_gaselm_plus uniq_pcelm_plus uniq_stackheightelm_plus
stack_max_elm_plus uniq_stackelm_plus uniq_memuelm_plus
uniq_memelm_plus uniq_storageelm_plus

lemma inst_res_as_set_uniq_stateelm:
"(pre \<and>* code (blocks_insts blocks) \<and>* resta)
        (instruction_result_as_set co_ctx
          presult) \<Longrightarrow>
       \<exists>s. pre s \<and> uniq_stateelm s"
apply(clarsimp simp add: sep_conj_def)
apply(rule_tac x=x in exI)
apply(simp add: uniq_stateelm_simps)
done

lemma uniq_stateelm_subset:
"Q = P + R \<Longrightarrow> uniq_stateelm Q \<Longrightarrow> uniq_stateelm P"
by(simp add: uniq_stateelm_simps plus_set_def)

lemma uniq_stateelm_inst_res:
"uniq_stateelm (instruction_result_as_set co_ctx presult)"
apply(case_tac presult)
apply(simp add: as_set_simps uniq_stateelm_simps)+
done

(*Lemmas for Jump and Jumpi *)
lemmas uint_word_reverse = word_of_int_inverse[OF refl]

lemma sep_conj_imp:
"(P \<and>* R) s \<Longrightarrow> \<forall>t. P t \<longrightarrow> Q t \<Longrightarrow> (Q \<and>* R) s"
apply(simp add: sep_conj_def)
apply(fastforce)
done

method find_q_pc_after_inst =
(rule exI; rule conjI),
rule ext,
rule iffI,
sep_simp simp: program_counter_sep,
assumption

(*apply(rule exI; rule conjI)
 apply(rule ext)
 apply(rule iffI)
  apply(sep_simp simp: program_counter_sep)
 apply(assumption)*)

lemma only_one_pc:
"uniq_stateelm s \<Longrightarrow>
PcElm n \<in> s \<Longrightarrow>
PcElm (n+1) \<in> s \<Longrightarrow>
False"
apply(simp add: uniq_stateelm_def)
apply(drule conjunct1)
apply(drule spec[where x=n], erule impE, assumption)
apply(drule spec[where x="n+1"], erule impE, assumption)
apply simp
done

lemma only_one_gas:
"uniq_stateelm s \<Longrightarrow>
i > 0 \<Longrightarrow>
GasElm g \<in> s \<Longrightarrow>
GasElm (g-i) \<in> s \<Longrightarrow>
False"
apply(simp add: uniq_stateelm_def)
apply(drule conjunct2, drule conjunct1)
apply(drule spec[where x=g], erule impE, assumption)
apply(drule spec[where x="g-i"], erule impE, assumption)
apply simp
	done
		
		lemma only_one_stack_elm:
"uniq_stateelm s \<Longrightarrow>
StackElm (h,v) \<in> s \<Longrightarrow>
StackElm (h,u) \<in> s \<Longrightarrow>
u = v"
apply(simp add: uniq_stateelm_def)
			done
				
method uniq_state_elm_quasi=
 (simp add: uniq_stateelm_def),
 (rule conjI, fastforce),
 (rule conjI, fastforce),
 (rule conjI, fastforce),
 (rule conjI; clarsimp),
  (rule conjI; clarsimp),
 (rule conjI; clarsimp)

(*apply (simp add: uniq_stateelm_def)
           apply(rule conjI, fastforce)
           apply(rule conjI, fastforce)
           apply(rule conjI, fastforce)
           apply(rule conjI; clarsimp)
            apply(rule conjI; clarsimp)
           apply(rule conjI; clarsimp)*)

method easy_case_pc_after_inst=
(clarsimp simp add: gas_value_simps evm_sep),
(rule conjI),
(erule_tac P=rest in back_subst),
(auto simp add: uniq_stateelm_def)[1],
(auto simp add: uniq_stateelm_def)[1]

(*        apply(clarsimp simp add: gas_value_simps sep_fun_simps)
        apply(rule conjI)
         apply(erule_tac P=rest in back_subst)
         apply(auto simp add: uniq_stateelm_def)[1]
        apply (auto simp add: uniq_stateelm_def)[1]
*)


method after_arith_if =
(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+,
(clarsimp simp add: gas_value_simps),
(rule conjI),
(erule_tac P="_ \<and>* _" in back_subst),
(rule  Set.equalityI),
(simp add: Set.subset_iff, clarify),
(rule conjI),
(rule notI; drule only_one_pc; simp),
(rule conjI, rule notI,simp add: uniq_stateelm_def),
(rule conjI, rule notI),
(split if_splits; simp)
  (*          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          				 apply(erule_tac P="_ \<and>* _" in back_subst)
    apply(rule  Set.equalityI)
             prefer 2
            apply(auto)[1]
           apply(simp add: Set.subset_iff, clarify)
           apply(rule conjI)
            apply(rule notI; drule only_one_pc; simp)
            			 apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
            		 apply(rule conjI, rule notI)
            		  apply(split if_splits; simp)*)

method after_byte =
(clarsimp simp add: gas_value_simps evm_sep),
(rule conjI),
(erule_tac P=rest in back_subst),
(auto simp add: uniq_stateelm_def)[1],
(uniq_state_elm_quasi),
(case_tac "ha=Suc h"; simp)
  (*       apply(clarsimp simp add: gas_value_simps evm_sep)
       apply(rule conjI)
        apply(erule_tac P=rest in back_subst)
        apply(auto simp add: uniq_stateelm_def)[1]
       apply (uniq_state_elm_quasi)
       			 apply(case_tac "ha=Suc h"; simp)*)

lemma memaddr_no_overflow:
 "unat (memaddr::w256) + v \<le> unat (- 1::w256) \<Longrightarrow> 0 < v  \<Longrightarrow> memaddr \<le> memaddr + 1"    
  by unat_arith
    
lemma memory_range_elms_le:
"MemoryElm (h, v) \<in> memory_range_elms memaddr xs \<Longrightarrow> unat memaddr + length xs - 1 \<le> unat (-1::w256) \<Longrightarrow>  
memaddr \<le> h"
  apply(induct xs arbitrary:v h memaddr, simp)
  apply clarsimp
  apply(erule disjE, clarsimp)
  apply(case_tac "xs = []", clarsimp)
  apply (drule meta_spec)+
  apply(drule meta_mp, assumption)
  apply simp
  apply (drule meta_mp)
  apply(subst unat_plus_simple[THEN iffD1])
  apply (erule memaddr_no_overflow, simp)
  apply simp+
  apply (drule memaddr_no_overflow, simp)    
  apply simp
done    

lemma memory_range_elms_uniq_stateelm:
"unat memaddr + length xs - 1 \<le> unat (-1::w256) \<Longrightarrow>  
 MemoryElm (h, v) \<in> memory_range_elms memaddr xs  \<longrightarrow> 
    (\<forall>v'. MemoryElm (h, v') \<in> memory_range_elms memaddr xs \<longrightarrow> v' = v)"
  apply (induct xs arbitrary: memaddr)
  apply clarsimp
  apply clarsimp
  apply(case_tac "xs = []")
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply(drule memory_range_elms_le)
  apply(subst unat_plus_simple[THEN iffD1])   
  apply (erule memaddr_no_overflow, simp)
  apply simp+
  apply (drule memaddr_no_overflow, simp)    
  apply simp
  apply(rule conjI, clarsimp)
 apply(drule memory_range_elms_le)
  apply(subst unat_plus_simple[THEN iffD1])   
  apply (erule memaddr_no_overflow, simp)
  apply simp+
  apply (drule memaddr_no_overflow, simp)    
  apply simp
  apply clarsimp
  apply(drule_tac x="memaddr + 1" in meta_spec, simp)
    apply (drule meta_mp)
  apply(subst unat_plus_simple[THEN iffD1])   
  apply (erule memaddr_no_overflow, simp)
  apply simp+
  done
    
lemma memory_range_elms_same_addr:
 "MemoryElm (a, v) \<in> memory_range_elms memaddr xs \<Longrightarrow> length xs \<le> length zs \<Longrightarrow>
       \<exists>v'. MemoryElm (a, v') \<in> memory_range_elms memaddr zs"
  apply (induct xs arbitrary:memaddr zs ; clarsimp)
  apply (erule disjE; clarsimp)
  apply(case_tac zs, simp)
  apply fastforce
  apply(case_tac zs, simp)
  apply fastforce
  done
    
lemma pc_after_inst:
notes
  if_split[split del]
shows
"triple_inst net pre x post \<Longrightarrow> x = (n, i) \<Longrightarrow> reg_inst i \<Longrightarrow>
\<exists>s. pre s \<and> uniq_stateelm s \<Longrightarrow>
\<exists>q. post = (program_counter (n + inst_size i) ** q) \<and>
    (\<exists>s0. (program_counter (n + inst_size i) ** q) s0 \<and> uniq_stateelm s0)"

  apply(induct rule: triple_inst.induct; clarsimp)
 					 apply(erule triple_inst_arith.cases; clarsimp)
 		(*MUL*)
           apply(find_q_pc_after_inst)
           apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, v * w)} \<union>
             {GasElm (g-Glow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
           apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
           apply(clarsimp simp add: gas_value_simps)
           apply(rule conjI)
            apply(erule_tac P="_ \<and>* _" in back_subst)
            apply(auto simp add: uniq_stateelm_def)[1]
           apply (uniq_state_elm_quasi)
  apply(case_tac "ha=Suc h"; simp)
  	(*DIV*)
          apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_2_1_low DIV v w)} \<union>
             {GasElm (g-Glow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          					 apply(erule_tac P="_ \<and>* _" in back_subst)
          					 apply(auto simp add: uniq_stateelm_def)[1]
          					apply (uniq_state_elm_quasi)
  apply(case_tac "ha=Suc h"; simp)
  	(*MOD*)
              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_2_1_low MOD v w)} \<union>
             {GasElm (g-Glow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          					 apply(erule_tac P="_ \<and>* _" in back_subst)
          					apply(auto simp add: uniq_stateelm_def)[1]
    apply (uniq_state_elm_quasi)
  apply(case_tac "ha=Suc h"; simp)
  	(*ADD*)
  	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, v + w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          				 apply(erule_tac P="_ \<and>* _" in back_subst)
    apply(rule  Set.equalityI)
             prefer 2
            apply(auto)[1]
           apply(simp add: Set.subset_iff, clarify)
           apply(rule conjI)
            apply(rule notI; drule only_one_pc; simp)
            			 apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
            			 apply(rule conjI, rule notI)
    							 apply(drule_tac h=h and v=w and u="v+w" in only_one_stack_elm; simp)
           apply(rule notI; drule only_one_gas; simp)
          apply (uniq_state_elm_quasi)
          				apply(case_tac "ha=Suc h"; simp)
    (*SUB*)
      	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, v - w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          				 apply(erule_tac P="_ \<and>* _" in back_subst)
    apply(rule  Set.equalityI)
             prefer 2
            apply(auto)[1]
           apply(simp add: Set.subset_iff, clarify)
           apply(rule conjI)
            apply(rule notI; drule only_one_pc; simp)
            			 apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
            			 apply(rule conjI, rule notI)
    							 apply(drule_tac h=h and v=w and u="v-w" in only_one_stack_elm; simp)
           apply(rule notI; drule only_one_gas; simp)
          apply (uniq_state_elm_quasi)
          apply(case_tac "ha=Suc h"; simp)
    (*inst_GT*)
      	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_2_1_verylow inst_GT v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
      apply(after_arith_if)
    							 apply(drule_tac h=h and v=w and u="1" in only_one_stack_elm; simp)
    							apply(drule_tac h=h and v=w and u="0" in only_one_stack_elm; simp)
    							apply(rule notI; drule only_one_gas; simp)
    apply(auto)[1]
          apply (uniq_state_elm_quasi)
          			apply(case_tac "ha=Suc h"; simp)
    (*inst_EQ*)
          	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_2_1_verylow inst_EQ v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
      apply(after_arith_if)
    							 apply(drule_tac h=h and v=w and u="1" in only_one_stack_elm; simp)
    							apply(drule_tac h=h and v=w and u="0" in only_one_stack_elm; simp)
    						 apply(rule notI; drule only_one_gas; simp)
    apply(auto)[1]
          apply (uniq_state_elm_quasi)
          		 apply(case_tac "ha=Suc h"; simp)
    (*inst_LT*)
          	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_2_1_verylow inst_LT v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
              apply(after_arith_if)
    							 apply(drule_tac h=h and v=w and u="1" in only_one_stack_elm; simp)
    							apply(drule_tac h=h and v=w and u="0" in only_one_stack_elm; simp)
    						apply(rule notI; drule only_one_gas; simp)
    		apply(auto)[1]
          apply (uniq_state_elm_quasi)
          		apply(case_tac "ha=Suc h"; simp)
    (*ADDMOD*)
          	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc (Suc h)))} -
             {StackElm (Suc (Suc h), u)} - {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_3_1 ADDMOD u v w)} \<union>
             {GasElm (g-Gmid)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
apply(after_arith_if)
    							 apply(drule_tac h=h and v=w and u="word_of_int
          ((uint u + uint v) mod uint w)" in only_one_stack_elm; simp)
  apply(rule notI; drule only_one_gas; simp)
  	apply(auto)[1]
          apply (uniq_state_elm_quasi)
          	 apply(case_tac "ha=Suc (Suc h)"; simp)
    apply(case_tac "ha=Suc h"; simp)
  	(*MULMOD*)
  	          	              apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc (Suc h)))} -
             {StackElm (Suc (Suc h), u)} - {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, arith_3_1 MULMOD u v w)} \<union>
             {GasElm (g-Gmid)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)} " in exI)
apply(after_arith_if)
    							 apply(drule_tac h=h and v=w and u="word_of_int
          ((uint u * uint v) mod uint w)" in only_one_stack_elm; simp)
  apply(rule notI; drule only_one_gas; simp)
  	apply(auto)[1]
          apply (uniq_state_elm_quasi)
          	 apply(case_tac "ha=Suc (Suc h)"; simp)
          	apply(case_tac "ha=Suc h"; simp)
    (*ISZERO*)
    	        apply(find_q_pc_after_inst)
          apply(rule_tac x="(s - {PcElm n} -
             {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, iszero_stack w)} \<union>
             {GasElm (g-Gverylow)} \<union> {PcElm (n+1)} " in exI)
           apply(easy_case_pc_after_inst)
    (**BITS**)
    			apply(erule triple_inst_bits.cases; clarsimp)
    (*NOT*)
        apply(find_q_pc_after_inst)
        apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackElm (h, w)}) \<union> 
           {PcElm (n + 1)} \<union>
           {StackElm (h, NOT w)} \<union> {GasElm (g - Gverylow)} " in exI)
           		apply(easy_case_pc_after_inst)
    (*AND*)
       apply(find_q_pc_after_inst)
       apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, bits_2_1_verylow inst_AND v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)}" in exI)
      apply(after_byte)
    (*OR*)
       apply(find_q_pc_after_inst)
       apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, bits_2_1_verylow inst_OR v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)}" in exI)
      apply(after_byte)
    (*XOR*)
           apply(find_q_pc_after_inst)
       apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, bits_2_1_verylow inst_XOR v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)}" in exI)
      apply(after_byte)
    (*BYTE*)
           apply(find_q_pc_after_inst)
       apply(rule_tac x="(s - {PcElm n} - {StackHeightElm (Suc (Suc h))} -
             {StackElm (Suc h, v)} - {StackElm (h, w)} - {GasElm g}) \<union> {StackElm (h, get_byte v w)} \<union>
             {GasElm (g-Gverylow)} \<union> {StackHeightElm (Suc h)} \<union> {PcElm (n+1)}" in exI)
      apply(after_byte)
    (**INFO**)
    		  apply(erule triple_inst_info.cases; clarsimp)
    (*CALLVALUE*)
            apply(find_q_pc_after_inst)
            apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackHeightElm h}) \<union>
          {StackHeightElm (Suc h)} \<union> {GasElm (g - Gbase)} \<union> {StackElm (h, w)} \<union>
          {PcElm (n + 1)}" in exI)
            apply(easy_case_pc_after_inst)
    (*CALLDATASIZE*)
           apply(find_q_pc_after_inst)
           apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackHeightElm h}) \<union>
        {StackHeightElm (Suc h)} \<union> {GasElm (g - Gbase)} \<union> {StackElm (h, word256FromNat (length data))} \<union>
          {PcElm (n + 1)}" in exI)
           apply(easy_case_pc_after_inst)
    (*CALLDATASIZE*)
           apply(find_q_pc_after_inst)
           apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackHeightElm h}) \<union>
        {StackHeightElm (Suc h)} \<union> {GasElm (g - Gbase)} \<union> {StackElm (h, ucast c)} \<union>
          {PcElm (n + 1)}" in exI)
           apply(easy_case_pc_after_inst)
    (**Memory**)
    		apply(erule triple_inst_memory.cases; clarsimp)
    (*MLOAD*)
    		 apply(find_q_pc_after_inst)
         apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackElm (h,memaddr)} - {MemoryUsageElm memu}) \<union>
          {GasElm (g - Gverylow + Cmem memu - Cmem (M memu memaddr 32))} \<union>
					{StackElm (h, v)} \<union> {MemoryUsageElm (M memu memaddr 32)} \<union>
          {PcElm (n + 1)}" in exI)
          apply(sep_simp simp: program_counter_sep memory_usage_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          apply(erule_tac P="_ \<and>* _" in back_subst)
      		 apply(rule  Set.equalityI)
           apply(simp add: Set.subset_iff, clarify)
          apply(rule conjI)
            apply(rule notI; drule only_one_pc; simp)
            			 apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
            		 apply(rule conjI, rule notI; simp add: uniq_stateelm_def)
           apply(auto simp add: uniq_stateelm_def)[1]
          apply(auto simp add: uniq_stateelm_def)[1]
         apply(auto simp add: uniq_stateelm_def)[1]
        (*MSTORE*)
        apply(find_q_pc_after_inst)
        apply(simp add: memory_def)
    		apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackElm (Suc h,memaddr)} - {StackElm (h,v)} -
					{MemoryUsageElm memu} - {StackHeightElm (Suc (Suc h))} -
					(memory_range_elms memaddr (word_rsplit old_v))) \<union>
          {GasElm (g - Gverylow + Cmem memu - Cmem (M memu memaddr 32))} \<union>
					{MemoryUsageElm (M memu memaddr 32)} \<union> {StackHeightElm h} \<union>
          {PcElm (n + 1)} \<union> (memory_range_elms memaddr (word_rsplit v))" in exI)
                apply(sep_simp simp: program_counter_sep memory_usage_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps memory_range_sep[where len_word=32, simplified])
    			apply(simp add: memory_range_elms_set_simps)
    		apply(rule conjI)
    		 apply(subst subset_iff)
    		 apply(rule allI, rule impI)
    		 apply(simp)
    		apply(rule conjI)
    		 apply(erule_tac P="_ \<and>* _" in back_subst)
         apply(rule  Set.equalityI, subst subset_iff)
          apply(clarsimp)
          apply(rule conjI)
           apply(rule notI; drule only_one_pc; simp)
          apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
          apply(rule conjI, rule notI, simp add: uniq_stateelm_def)
          apply(rule conjI, rule notI, simp add: uniq_stateelm_def)
          apply(rule notI)
          apply(case_tac t; simp add: memory_range_elms_set_simps)
          apply(clarsimp)
    			apply(subst (asm) memory_elms_not_in_range, simp)
    			apply(subst (asm) de_Morgan_conj)
    			apply(case_tac "unat (a - memaddr) < 32"; simp)
    			 prefer 2
    			 apply(subst (asm) not_less)
    			 apply(insert memory_elms_out_of_range)[1]
    			 apply(drule_tac x="word_rsplit v" and y=a in meta_spec2)
    			 apply(drule_tac x=memaddr and y=b in meta_spec2)
    			 apply(simp)
    			apply(subst (asm) subset_iff)
    			apply(drule_tac x="MemoryElm (a, word_rsplit old_v ! unat (a - memaddr))" in spec)
    			apply(drule mp)
    			 apply(insert elm_in_range_in_lst)[1]
    			 apply(drule_tac x="a - memaddr" and y="word_rsplit old_v" in meta_spec2)
    			 apply(drule_tac x=memaddr in meta_spec)
    			 apply(simp)
  apply(simp add: uniq_stateelm_simps)    
  apply clarsimp
  apply(simp add: uniq_stateelm_simps memory_range_elms_set_simps)        
  apply (rule conjI[rotated])+
    prefer 2
  apply clarsimp
  apply (rule conjI) apply clarsimp
    
  apply (drule_tac zs="word_rsplit old_v" in  memory_range_elms_same_addr, simp)
  apply clarify
  apply (drule (1) subsetD)
  apply (drule_tac x=ha and y=v'a in spec2, fastforce)
  apply clarsimp
  apply (rule conjI, clarsimp)

  apply (drule_tac zs="word_rsplit old_v" in  memory_range_elms_same_addr, simp)
  apply clarify
  apply (drule (1) subsetD)
  apply (drule_tac x=ha and y=v'a in spec2, fastforce)
  apply clarsimp
  apply (erule (1) memory_range_elms_uniq_stateelm[rule_format,rotated])
  apply simp
               apply (subst (asm) word_le_nat_alt)
               apply(thin_tac "\<forall>v. _v")+
  apply(thin_tac "(_ \<and>*_) _")
  apply (drule add_le_mono[where i="31" and j="31" and l="unat _", OF le_refl]) 
               apply(erule le_trans)
               apply(subgoal_tac "unat (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0::w256) = unat (-32::w256)"; simp)
               apply(subgoal_tac "unat (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF::w256) = unat (-1::w256)")
                apply(simp)
               apply(subst unat_arith_simps(3)[symmetric], simp)
              apply(rule allI, rule conjI; clarsimp)
             apply(rule allI, rule conjI; clarsimp)
             apply(case_tac "ha = Suc h"; clarsimp)
             apply(case_tac "ha = h"; clarsimp)
            apply(rule allI, rule allI, clarsimp)
           apply(rule allI, rule conjI; clarsimp)
          apply(rule allI, rule conjI; clarsimp)
         apply(rule allI, rule conjI; clarsimp)
    (**Storage**)
      (*SLOAD*)
        apply(erule triple_inst_storage.cases; clarsimp)
         apply(find_q_pc_after_inst)
         apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackElm (h,idx)}) \<union> {GasElm (g - Gsload neta)} \<union>
          {PcElm (n + 1)} \<union> {StackElm (h,w)}" in exI)
         apply(easy_case_pc_after_inst)
        (*SSTORE*)
        apply(find_q_pc_after_inst)
        apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackElm (h,new)} - {StackElm (Suc h, idx)} -
        {StackHeightElm (Suc (Suc h))} - {StorageElm (idx, old)}) \<union> {StorageElm (idx, new)} \<union>
        {GasElm (g - Csstore old new)} \<union> {StackHeightElm h} \<union> {PcElm (n + 1)}" in exI)
            apply(after_byte)
             apply(case_tac "ha=h"; clarsimp)
            apply(rule conjI; clarsimp)
    (**Pc**)
  	    apply(erule triple_inst_pc.cases; clarsimp)
      apply(find_q_pc_after_inst)
      apply(rule_tac x="(s - {GasElm g} - {PcElm n}) \<union> {GasElm (g - Gjumpdest)} \<union>
          {PcElm (n + 1)}" in exI)
      apply(easy_case_pc_after_inst)
     apply(find_q_pc_after_inst)
     apply(rule_tac x="(s - {GasElm g} - {PcElm n} - {StackHeightElm h}) \<union>
          {StackHeightElm (Suc h)} \<union> {GasElm (g - Gbase)} \<union> {StackElm (h, word_of_int n)} \<union>
          {PcElm (n + 1)}" in exI)
     apply(easy_case_pc_after_inst)
    apply(erule triple_inst_stack.cases; clarsimp)
     apply(clarsimp simp add: inst_size_simps pure_sep)
     apply(find_q_pc_after_inst)
     apply(rule_tac x="(s - {GasElm g} - {PcElm n} -
          {StackHeightElm h}) \<union> {GasElm (g - Gverylow)} \<union> {StackElm (h, word_rcat lst)} \<union>
          { StackHeightElm (Suc h)} \<union> {PcElm (n + (1 + int (length lst)))}" in exI)
         apply(easy_case_pc_after_inst)
        apply(find_q_pc_after_inst)
    apply(rule_tac x="(s - {GasElm g} - {PcElm n} -
          {StackHeightElm (Suc h)} - {StackElm (h, w)}) \<union> {GasElm (g - Gbase)} \<union>
          { StackHeightElm h} \<union> {PcElm (n + 1)}" in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
          apply(rule conjI)
          					 apply(erule_tac P="_ \<and>* _" in back_subst)
         apply(auto simp add: uniq_stateelm_def)[1]
    apply(simp add: uniq_stateelm_def)
        apply(rule conjI, fastforce)+
    apply(rule allI, rule conjI; clarsimp)
    apply(case_tac "ha=h"; clarsimp)
        apply(find_q_pc_after_inst)
     apply(rule_tac x="(s - {GasElm g} - {PcElm n} -
          {StackElm (h, u)}) \<union> {GasElm (g - Gverylow)} \<union>
          {StackElm (h,read_word_from_bytes (unat u)
                lst)} \<union> {PcElm (n + 1)}" in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
       apply(rule conjI)
          					 apply(erule_tac P="_ \<and>* _" in back_subst)
       apply(auto simp add: uniq_stateelm_def)[1]
       apply(simp add: uniq_stateelm_def)
       apply(rule conjI, fastforce)+
       apply(fastforce)
    (*Swap*)
    	apply(find_q_pc_after_inst)
apply(rule_tac x="(s - {PcElm n} - {GasElm g} -
             {StackElm (h, w)} - {StackElm (h - (Suc (unat na)), v)}) \<union> 
             {StackElm (h, v)} \<union> {StackElm (h - (Suc (unat na)), w)} \<union>
             {GasElm (g-Gverylow)} \<union> {PcElm (n+1)}" in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
   apply(rule conjI)
   		 apply(erule_tac P="_ \<and>* _" in back_subst)
   		 apply(rule  Set.equalityI)
           apply(simp add: Set.subset_iff, clarify)
        apply(rule conjI)
            apply(rule notI; drule only_one_pc; simp)
            			 apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
            		 apply(rule conjI, rule notI; simp add: uniq_stateelm_def)
            		  apply(auto simp add: uniq_stateelm_def)[1]
       apply(auto simp add: uniq_stateelm_def)[1]
   apply (simp add: uniq_stateelm_def)
   apply(rule conjI, fastforce)
   apply(rule conjI, fastforce)
   apply(rule conjI)
    apply(clarsimp)
    apply(rule conjI, fastforce)
    apply(rule conjI; clarsimp)
    apply(rule conjI; clarsimp)
    	apply(fastforce)
    (*Dup*)
      	apply(find_q_pc_after_inst)
apply(rule_tac x="(s - {PcElm n} - {GasElm g} -
             {StackHeightElm h}) \<union> 
             {StackElm (h, w)} \<union> {StackHeightElm (Suc h)} \<union>
             {GasElm (g-Gverylow)} \<union> {PcElm (n+1)}" in exI)
          apply(sep_simp simp: program_counter_sep gas_pred_sep stack_sep stack_height_sep pure_sep, (erule conjE)?)+
          apply(clarsimp simp add: gas_value_simps)
   apply(rule conjI)
   		 apply(erule_tac P="_ \<and>* _" in back_subst)
   		 apply(rule  Set.equalityI)
           apply(simp add: Set.subset_iff, clarify)
        apply(rule conjI)
            apply(rule notI; drule only_one_pc; simp)
            			 apply(rule conjI, rule notI,simp add: uniq_stateelm_def)
            		 apply(rule conjI, rule notI; simp add: uniq_stateelm_def)
            		  apply(auto simp add: uniq_stateelm_def)[1]
       apply(auto simp add: uniq_stateelm_def)[1]
   apply (simp add: uniq_stateelm_def)
   apply(rule conjI, fastforce)+
   	 apply(fastforce)
   	  apply(drule meta_mp)
  apply(rule_tac x=s in exI; rule conjI; simp)
  apply(assumption)
  apply(simp add: pure_def)
  done

lemma triple_seq_empty_case[OF _ refl] :
"triple_seq net q xs r \<Longrightarrow> xs = [] \<Longrightarrow>
 \<exists>q'. (\<forall>s. q s \<longrightarrow> q' s) \<and> (\<forall>s. q' s \<longrightarrow> r s)"
  apply(induct rule: triple_seq.induct, simp_all)
apply(rule_tac x=post in exI, simp)
  apply force
apply(rule_tac x=post in exI, simp)
apply(simp add: pure_def)
done

lemma triple_seq_empty_case' :
"triple_seq net q [] r \<Longrightarrow>
 (\<forall>s. q s \<longrightarrow> r s)"
by(drule triple_seq_empty_case, fastforce)

lemma pc_after_seq:
" triple_seq net pre insts post' \<Longrightarrow>
\<exists>s. pre s \<and> uniq_stateelm s \<Longrightarrow>
\<forall>s. post' s = (program_counter m \<and>* post) s \<Longrightarrow>
fst (hd insts) = n \<Longrightarrow>
insts \<noteq> [] \<Longrightarrow>
seq_block insts \<Longrightarrow>
reg_block insts \<Longrightarrow>
 m = n + inst_size_list insts"
  apply(induction arbitrary:n post rule:triple_seq.induct)
    apply(clarsimp)
    apply(case_tac xs; clarsimp)
     apply(drule triple_seq_empty_case'; clarsimp)
     apply(simp add: reg_block_def seq_block.simps)
     apply(drule_tac n=a and i=b and pre=pre and post=q in pc_after_inst; clarsimp)
      apply(fastforce)
     apply(thin_tac "uniq_stateelm s")
		 apply(thin_tac "\<forall>s. _ s = _ s")
     apply(simp add: program_counter_sep uniq_stateelm_def)
    apply(drule_tac x="a + inst_size b" and y=posta in meta_spec2)
    apply(clarsimp)
    apply(simp add:reg_block_def)
    apply(erule conjE)+
    apply(drule_tac n=a and i=b in pc_after_inst)
       apply(simp add: seq_block.simps)+
     apply(fastforce)
    apply(drule meta_mp; clarsimp)
    apply(simp add: seq_block.simps; clarsimp)
   apply(clarsimp)
  apply(drule_tac x=n and y=post in meta_spec2)
  apply(drule meta_mp)
  apply(clarsimp)
   apply(rule_tac x=s in exI)
   apply(fastforce)
  apply(simp)
 apply (fastforce simp: pure_def)
done

lemma jump_i_ends_block:
"seq_block (ys@xs) \<Longrightarrow>
 (t=Jump \<and> i=JUMP) \<or> (t=Jumpi \<and> i=JUMPI) \<Longrightarrow>
 (n, insts, t) \<in> set (aux_basic_block xs ys) \<Longrightarrow>
 (n + inst_size_list insts, Pc i) \<in> set xs"
 apply(induction xs arbitrary: ys)
  apply(case_tac ys; simp add: aux_basic_block.simps)
 apply(clarsimp simp add: aux_basic_block.simps Let_def)
 apply(case_tac "reg_inst b \<and> b \<noteq> Pc JUMPDEST")
  apply(drule_tac x="ys @ [(a, b)]" in meta_spec)
  apply(simp split: reg_inst_splits)
 apply(case_tac "b=Pc JUMPDEST")
  apply(case_tac ys)
	 apply(simp; drule_tac x="[(a, b)]" in meta_spec; simp)
  apply(simp; drule_tac x="[(a, b)]" in meta_spec; simp add: seq_block_tl'[where xs="_#_"])
  apply(erule disjE; simp)
 apply(drule_tac x="[]" in meta_spec)
 apply(drule meta_mp)
  apply(subgoal_tac "seq_block ((a, b) # xs)")
	 apply(simp add: seq_block_tl)
  apply(simp add: seq_block_tl')
 apply(simp split: reg_inst_splits; erule disjE; simp)
  apply(erule disjE; simp)
  apply(case_tac ys; simp add: block_pt_def seq_block_sumC)
 apply(erule disjE; simp)
 apply(case_tac ys; simp add: block_pt_def seq_block_sumC)
done

lemma jump_i_in_blocks_insts:
"wf_blocks blocks \<Longrightarrow>
blocks = build_blocks bytecode \<Longrightarrow>
 (t=Jump \<and> i=JUMP) \<or> (t=Jumpi \<and> i=JUMPI) \<Longrightarrow>
block_lookup blocks n = Some (xs, t) \<Longrightarrow>
(n+inst_size_list xs, Pc i) \<in> blocks_insts blocks"
apply(simp add: blocks_insts_def)
apply(simp add: rev_rebuild_with_add)
apply(simp add: build_blocks_def Let_def)
apply(simp add: build_basic_blocks_def)
apply(rule jump_i_ends_block[where ys="[]" and i=i and t=t])
  apply(simp add: seq_block_add_address add_address_def)
 apply(simp)
apply(rule map_of_SomeD, assumption)
done


(* JUMP case *)
lemma extract_info_jump:
"block_lookup blocks dest = Some (bi, ti) \<Longrightarrow>
 wf_blocks blocks \<Longrightarrow>
 block_lookup blocks n = Some (insts, Jump) \<Longrightarrow>
uint (word_of_int dest::w256) = dest"
apply(subst (asm) wf_blocks_def)
apply(simp add: uint_word_reverse)
done

lemma program_content_some_fst:
"wf_blocks blocks \<Longrightarrow>
 block_lookup blocks dest = Some ((dest, i) # bbi, ti) \<Longrightarrow>
 i \<noteq> Misc STOP \<Longrightarrow>
 {CodeElm (pos, i) |pos i. (pos, i) \<in> blocks_insts blocks}
       \<subseteq> instruction_result_as_set co_ctx
           (InstructionContinue x1) \<Longrightarrow>
 program_content (cctx_program co_ctx) dest = Some i"
apply(drule block_in_insts_wf, assumption)
apply(clarsimp)
 apply(subgoal_tac "CodeElm (dest,i) \<in> instruction_result_as_set co_ctx (InstructionContinue x1)")
  apply(simp add: code_elm_means)
 apply(fastforce)
done

lemma jump_sem:
"block_lookup blocks dest = Some (bi, ti) \<Longrightarrow>
 bi = (dest, Pc JUMPDEST) # bbi \<Longrightarrow>
 wf_blocks blocks \<Longrightarrow>
 blocks = build_blocks bytecode \<Longrightarrow>
 block_lookup blocks n = Some (insts, Jump) \<Longrightarrow>
       (code (blocks_insts blocks) \<and>*
        (continuing \<and>*
         gas_pred g \<and>*
         program_counter (n + inst_size_list insts) \<and>*
         stack_height (Suc h) \<and>*
         stack h (word_of_int dest::w256) \<and>*
         memory_usage m \<and>*
         \<langle> h \<le> 1023 \<and> Gmid \<le> g \<and> 0 \<le> m \<rangle> \<and>*
         restb) \<and>*
        rest)
        (instruction_result_as_set co_ctx presult) \<Longrightarrow>
       (code (blocks_insts blocks) \<and>*
        (continuing \<and>*
         program_counter dest \<and>*
         stack_height h \<and>*
         gas_pred (g - Gmid) \<and>*
         memory_usage m \<and>* restb) \<and>*
        rest)
        (instruction_result_as_set co_ctx
          (program_sem stopper co_ctx (Suc 0) net
            presult))"
apply (sep_simp_asm simp: continuing_sep memory_usage_sep pure_sep gas_pred_sep stack_sep stack_height_sep program_counter_sep )
apply(clarsimp)
apply(insert extract_info_jump[where blocks=blocks and n=n and dest=dest and bi=bi and ti=ti and insts=insts]; clarsimp)
apply(case_tac presult)
 apply(simp add: stateelm_means_simps)
 apply(simp add: program_sem.simps instruction_simps next_state_def)
 apply(insert jump_i_in_blocks_insts[where blocks=blocks and t=Jump and i=JUMP and n=n and xs=insts and bytecode=bytecode], simp)
 apply(insert code_elm_means[where xy="(n+ inst_size_list insts,Pc JUMP)" and c=co_ctx])
 apply(drule_tac x=x1 in meta_spec)
 apply(drule iffD1)
  apply (sep_simp_asm simp: code_sep)
  apply(auto)[1]
 apply(simp add: instruction_simps Let_def rev_nth)
 apply(case_tac "vctx_stack x1"; clarsimp)
 apply(simp add: instruction_simps Let_def rev_nth)
 apply (sep_simp simp: continuing_sep memory_usage_sep pure_sep gas_pred_sep stack_sep stack_height_sep program_counter_sep)+
 apply(simp add: stateelm_means_simps)
 apply(insert program_content_some_fst[where blocks=blocks and dest=dest and co_ctx=co_ctx])[1]
 apply(drule meta_spec)+
 apply(drule meta_mp, simp)+
  apply (sep_simp_asm simp: code_sep)
  apply(auto)[1]
 apply(simp)
 apply(clarsimp simp add: instruction_simps stateelm_means_simps)
 apply(erule_tac P="_ \<and>* _" in back_subst)
  apply(rule equalityI, rule subsetI; clarsimp simp add: as_set_simps)
   apply(erule disjE, clarsimp)+
    apply(case_tac "idx < length list"; simp add: short_rev_append)
   apply(erule disjE, clarsimp)+
   apply(clarsimp)
  apply(erule disjE, clarsimp)+
   apply(case_tac "idx < length list"; simp add: short_rev_append)
  apply(clarsimp)
  apply(erule disjE, clarsimp)+
  apply(clarsimp)
apply(simp add: as_set_simps)
done

lemma blocks_jump_sem_t:
"block_lookup blocks dest = Some (bi, ti) \<Longrightarrow>
 bi = (dest, Pc JUMPDEST) # bbi \<Longrightarrow>
 triple_seq net pre insts
	(program_counter (n + inst_size_list insts) \<and>*
	 gas_pred g \<and>*
	 memory_usage m \<and>*
	 stack_height (Suc h) \<and>*
	 stack h (word_of_int dest) \<and>*
	 \<langle> h \<le> 1023 \<and> Gmid \<le> g \<and> 0 \<le> m \<rangle> \<and>* continuing \<and>* rest) \<Longrightarrow>
	triple_sem_t net
	 (program_counter dest \<and>*
		gas_pred (g - Gmid) \<and>*
		memory_usage m \<and>* stack_height h \<and>* continuing \<and>* rest)
	 (blocks_insts blocks) post \<Longrightarrow>
 wf_blocks blocks \<Longrightarrow>
 build_blocks bytecode = blocks \<Longrightarrow>
 block_lookup blocks (v_ind (n, insts, Jump)) = Some (snd (n, insts, Jump)) \<Longrightarrow>
 triple_sem_t net pre (blocks_insts blocks) post"
 apply(simp only: triple_sem_t_def; clarify)
 apply(drule_tac x=co_ctx and y="(program_sem stopper co_ctx (Suc (length insts)) net presult)" in spec2)
 apply(drule_tac x=resta and y=stopper in spec2)
 apply(case_tac "insts")
  apply(cut_tac q=pre and r="(program_counter (n + inst_size_list insts) \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack_height (Suc h) \<and>*
         stack h (word_of_int dest) \<and>*
         \<langle> h \<le> 1023 \<and> Gmid \<le> g \<and> 0 \<le> m \<rangle> \<and>* continuing \<and>* rest)" and net=net
        in triple_seq_empty_case')
   apply(clarsimp)
  apply(drule mp)
   apply(clarsimp)
   apply(drule_tac P=pre in sep_conj_imp, assumption)
   apply(drule_tac bi="(dest, Pc JUMPDEST) # bbi" and ti=ti and g=g and h=h and presult=presult and
         m=m and restb=rest and rest=resta and bytecode=bytecode and co_ctx=co_ctx
         in jump_sem; simp add: sep_lc)
   apply(simp add: sep_lc)
  apply(simp add: program_sem_t_exec_continue)
 apply(cut_tac m="n + inst_size_list insts" and n=n
			 and post=" (gas_pred g \<and>* memory_usage m \<and>* stack_height (Suc h) \<and>*
         stack h (word_of_int dest) \<and>* \<langle> h \<le> 1023 \<and> Gmid \<le> g \<and> 0 \<le> m \<rangle> \<and>* continuing \<and>* rest)"
			 in pc_after_seq)
        apply(assumption)
			 apply(simp add: inst_res_as_set_uniq_stateelm)
		  apply(simp add: wf_blocks_def)
     apply(simp add: wf_blocks_def)
     apply(drule_tac x=n and y=insts in spec2; drule conjunct1)
	   apply(drule_tac x=Jump in spec; simp)
    apply(fastforce)
   apply(simp add: wf_blocks_def)
  apply(simp add: wf_blocks_def)
	apply(simp add: reg_vertex_def)
	apply(drule_tac x=n and y=insts in spec2, drule conjunct1, drule_tac x=Jump in spec, simp)
 apply(thin_tac "_ = _ # _")
 apply(drule triple_seq_soundness)
 apply(simp only: triple_seq_sem_def)
 apply(rename_tac co_ctx presult resta stopper a list)
 apply(drule_tac x = "co_ctx" in spec)
 apply(drule_tac x = "presult" and y = "code (blocks_insts blocks - set insts) \<and>* resta" in spec2)
 apply(erule impE)
  apply(simp)
	apply(erule impE)
	 apply(cut_tac p=pre and n=n and insts="insts" and ty=Jump and r=resta and s="instruction_result_as_set co_ctx presult"
        in sep_code_code_sep_wf[where blocks=blocks]; simp)
	apply(drule_tac x = "stopper" in spec)
	apply(insert code_code_sep_wf[where blocks=blocks and n=n and insts="insts" and ty=Jump]; simp)
	apply(thin_tac "\<And>r s. _ r s = _ r s")
   apply(cut_tac co_ctx=co_ctx and stopper=stopper and insts=insts and net=net and
    presult="(program_sem stopper co_ctx (length insts) net presult)" and h=h
    and g=g and m=m and rest=resta and restb=rest and co_ctx=co_ctx
   in jump_sem; simp add: sep_lc)
  apply(sep_select_asm 8, sep_select_asm 8)
  apply(insert code_code_sep[where insts=insts and blocks=blocks and n=n and ty=Jump])[1]
	apply(simp, sep_select 6, simp)
 apply(simp add: execution_continue)
 apply(sep_cancel)+
apply(simp add: program_sem_t_exec_continue) 
done

(* JUMPI case *)

lemma diff_set_commute:
"A - {b} - {c} = A - {c} - {b}"
by(auto)

lemma diff_set_commute_code:
"A - {CodeElm (pos, i) |pos i.
        (pos, i) \<in> blocks_insts blocks} - {c} = A - {c} - {CodeElm (pos, i) |pos i.
        (pos, i) \<in> blocks_insts blocks}"
by(auto)

lemma extract_info_jumpi:
"      block_lookup blocks dest = Some (bi, ti) \<Longrightarrow>
       block_lookup blocks j = Some (bj, tj) \<Longrightarrow>
       wf_blocks blocks \<Longrightarrow>
       block_lookup blocks n = Some (insts, Jumpi) \<Longrightarrow>
dest = uint (word_of_int dest::256 word)"
 apply(simp add: wf_blocks_def)
 apply(drule spec2[where x=dest and y=bi])
 apply(drule conjunct1)+
 apply(drule spec[where x=ti])
 apply(simp add: uint_word_reverse)
done

lemma set_change_stack:
"instruction_result_as_set co_ctx
        (InstructionContinue
          (x1\<lparr>vctx_stack := ta, vctx_pc := k,
                vctx_gas := g\<rparr>)) -
       {StackHeightElm (length ta)} =
instruction_result_as_set co_ctx
        (InstructionContinue
          (x1\<lparr>vctx_stack := cond # ta, vctx_pc := k,
                vctx_gas := g\<rparr>)) -
       {StackElm (length ta, cond)} -
       {StackHeightElm (Suc (length ta))}"
apply(simp add: as_set_simps)
apply(rule equalityI; rule subsetI; clarsimp)
 apply(erule disjE, clarsimp)+
  apply(simp add: short_rev_append)
 apply(erule disjE, clarsimp)+
 apply(clarsimp)
apply(erule disjE, clarsimp)+
 apply(case_tac "idx = length ta"; simp add: short_rev_append)
apply(erule disjE, clarsimp)+
apply(clarsimp)
done

lemma set_change_stack_2:
"vctx_stack x1 = word_of_int dest # cond # ta \<Longrightarrow>
instruction_result_as_set co_ctx
        (InstructionContinue
          (x1\<lparr>vctx_stack := cond # ta,
                vctx_pc := p,
                vctx_gas := g\<rparr>)) -
       {StackHeightElm (Suc (length ta))}=
instruction_result_as_set co_ctx
        (InstructionContinue
          (x1\<lparr>vctx_pc := p,
                vctx_gas := g\<rparr>)) -
       {StackElm (Suc (length ta), word_of_int dest)} -
       {StackHeightElm (Suc (Suc (length ta)))}"
apply(simp add: as_set_simps)
apply(rule equalityI; rule subsetI; clarsimp)
 apply(erule disjE, clarsimp)+
  apply(case_tac "idx = length ta"; simp add: short_rev_append)
 apply(erule disjE, clarsimp)+
 apply(clarsimp)
apply(erule disjE, clarsimp)+
 apply(case_tac "idx < Suc (length ta)"; simp add: short_rev_append)
 apply(case_tac "idx = length ta"; simp add: short_rev_append)
apply(erule disjE, clarsimp)+
apply(clarsimp)
done

lemma jumpi_sem_zero:
"      block_lookup blocks i = Some (bi, ti) \<Longrightarrow>
       block_lookup blocks j = Some (bj, tj) \<Longrightarrow>
			 j = n + 1 + inst_size_list insts \<Longrightarrow>
       blocks = build_blocks bytecode \<Longrightarrow>
       wf_blocks blocks \<Longrightarrow>
       block_lookup blocks n = Some (insts, Jumpi) \<Longrightarrow>
       (code (blocks_insts blocks) \<and>*
        (continuing \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack h 0 \<and>*
         stack_height (Suc (Suc h)) \<and>*
         program_counter (n + inst_size_list insts) \<and>*
         stack (Suc h) (word_of_int i) \<and>*
         \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>* restb) \<and>*
        rest)
        (instruction_result_as_set co_ctx presult) \<Longrightarrow>
       (code (blocks_insts blocks) \<and>*
        ((continuing \<and>*
          stack_height h \<and>*
          gas_pred (g - Ghigh) \<and>*
          memory_usage m \<and>* restb) \<and>*
         program_counter j) \<and>*
        rest)
        (instruction_result_as_set co_ctx
          (program_sem stopper co_ctx (Suc 0) net
            presult))"
 apply (sep_simp_asm simp: stack_sep stack_height_sep memory_usage_sep pure_sep gas_pred_sep program_counter_sep )
 apply(clarsimp)
 apply(insert extract_info_jumpi[where blocks=blocks and n=n and dest=i and j=j and bi=bi and ti=ti and insts=insts and bj=bj and tj=tj])
 apply(clarsimp)
 apply(simp add: program_sem.simps instruction_sem_simps next_state_def)
 apply(split instruction_result.splits)
 apply(rule conjI;clarsimp)
	apply(simp add: stateelm_means_simps)
	apply(insert jump_i_in_blocks_insts[where blocks=blocks and t=Jumpi and i=JUMPI and n=n and xs=insts and bytecode=bytecode], simp)[1]
  apply(insert code_elm_means[where xy="(n+ inst_size_list insts,Pc JUMPI)" and c=co_ctx])[1]
  apply(drule_tac x=x1 in meta_spec)
  apply(drule iffD1)
	 apply(sep_simp simp: code_sep)
   apply(auto)[1]
 apply(simp add: instruction_simps Let_def rev_nth)
 apply(case_tac "vctx_stack x1"; clarsimp)
 apply(simp add: instruction_simps Let_def rev_nth)
 apply (sep_simp simp: continuing_sep memory_usage_sep pure_sep gas_pred_sep stack_sep stack_height_sep program_counter_sep)+
 apply(simp add: stateelm_means_simps)
 apply(erule_tac P="_ \<and>* _" in back_subst)
  apply(rule equalityI, rule subsetI; clarsimp simp add: as_set_simps)
   apply(erule disjE, clarsimp)+
    apply(case_tac "idx < length t"; simp add: short_rev_append)
   apply(erule disjE, clarsimp)+
   apply(clarsimp)
  apply(erule disjE, clarsimp)+
   apply(case_tac "idx < length t"; simp add: short_rev_append)
  apply(clarsimp)
  apply(erule disjE, clarsimp)+
  apply(clarsimp)
apply(sep_simp simp:continuing_sep)
apply(simp add: as_set_simps)
done

lemma jumpi_sem_non_zero:
"      block_lookup blocks dest = Some (bi, ti) \<Longrightarrow>
       block_lookup blocks j = Some (bj, tj) \<Longrightarrow>
			 bi = (dest, Pc JUMPDEST) # bbi \<Longrightarrow>
       blocks = build_blocks bytecode \<Longrightarrow>
       wf_blocks blocks \<Longrightarrow>
       block_lookup blocks n = Some (insts, Jumpi) \<Longrightarrow>
       (code (blocks_insts blocks) \<and>*
        (continuing \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack h cond \<and>*
         stack_height (Suc (Suc h)) \<and>*
         program_counter (n + inst_size_list insts) \<and>*
         stack (Suc h) (word_of_int dest) \<and>*
         \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>* restb) \<and>*
        rest)
        (instruction_result_as_set co_ctx presult) \<Longrightarrow>
       cond \<noteq> 0 \<Longrightarrow>
       (code (blocks_insts blocks) \<and>*
        ((continuing \<and>*
          memory_usage m \<and>*
          stack_height h \<and>* gas_pred (g - Ghigh) \<and>* restb) \<and>*
         program_counter dest) \<and>*
        rest)
        (instruction_result_as_set co_ctx
          (program_sem stopper co_ctx (Suc 0) net presult))"
 apply (sep_simp_asm simp: memory_usage_sep pure_sep gas_pred_sep stack_sep stack_height_sep program_counter_sep )
 apply(clarsimp)
 apply(insert extract_info_jumpi[where blocks=blocks and n=n and dest=dest and j=j and bi=bi and ti=ti and insts=insts and bj=bj and tj=tj])
 apply(clarsimp)
 apply(simp add: program_sem.simps instruction_sem_simps next_state_def)
 apply(split instruction_result.splits)
 apply(rule conjI;clarsimp)
	apply(simp add: stateelm_means_simps)
	apply(insert jump_i_in_blocks_insts[where blocks=blocks and t=Jumpi and i=JUMPI and n=n and xs=insts and bytecode=bytecode], simp)
  apply(insert code_elm_means[where xy="(n+ inst_size_list insts,Pc JUMPI)" and c=co_ctx])
  apply(drule_tac x=x1 in meta_spec)
  apply(drule iffD1)
	 apply(sep_simp simp: code_sep)
   apply(auto)[1]
 apply(simp add: instruction_simps Let_def rev_nth)
 apply(case_tac "vctx_stack x1"; clarsimp)
 apply(simp add: instruction_simps Let_def rev_nth)
 apply (sep_simp simp: continuing_sep memory_usage_sep pure_sep gas_pred_sep stack_sep stack_height_sep program_counter_sep)+
 apply(simp add: stateelm_means_simps)
 apply(insert program_content_some_fst[where blocks=blocks and dest=dest and co_ctx=co_ctx])[1]
 apply(drule meta_spec)+
 apply(drule meta_mp, simp)+
  apply (sep_simp_asm simp: code_sep)
  apply(auto)[1]
 apply(simp)
 apply(clarsimp simp add: instruction_simps stateelm_means_simps)
 apply(erule_tac P="_ \<and>* _" in back_subst)
  apply(rule equalityI, rule subsetI; clarsimp simp add: as_set_simps)
   apply(erule disjE, clarsimp)+
    apply(case_tac "idx < length t"; simp add: short_rev_append)
   apply(erule disjE, clarsimp)+
   apply(clarsimp)
  apply(erule disjE, clarsimp)+
   apply(case_tac "idx < length t"; simp add: short_rev_append)
  apply(clarsimp)
  apply(erule disjE, clarsimp)+
  apply(clarsimp)
apply(sep_simp simp: continuing_sep)
apply(simp add: as_set_simps)
done

lemma blocks_jumpi_sem_t:
"block_lookup blocks dest = Some ((dest, Pc JUMPDEST) # bbi, ti) \<Longrightarrow>
 bi = (dest, Pc JUMPDEST) # bbi \<Longrightarrow>
 block_lookup blocks (n + 1 + inst_size_list insts) = Some (bj, tj) \<Longrightarrow>
 triple_seq net pre insts
	(continuing \<and>* gas_pred g \<and>* memory_usage m \<and>*
	 stack h cond \<and>* stack_height (Suc (Suc h)) \<and>*
	 program_counter (n + inst_size_list insts) \<and>*
	 stack (Suc h) (word_of_int dest) \<and>*
	 \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>* rest) \<Longrightarrow>
 r = (continuing \<and>* memory_usage m \<and>*
			stack_height h \<and>* gas_pred (g - Ghigh) \<and>* rest) \<Longrightarrow>
 (cond \<noteq> 0 \<Longrightarrow>
	triple_sem_t net
	 ((continuing \<and>* memory_usage m \<and>*
		 stack_height h \<and>* gas_pred (g - Ghigh) \<and>* rest) \<and>*
		program_counter dest)
	 (blocks_insts blocks) post) \<Longrightarrow>
 (cond = 0 \<Longrightarrow>
	triple_sem_t net
	 ((continuing \<and>* memory_usage m \<and>*
		 stack_height h \<and>* gas_pred (g - Ghigh) \<and>* rest) \<and>*
		program_counter (n + 1 + inst_size_list insts))
	 (blocks_insts blocks) post) \<Longrightarrow>
 wf_blocks blocks \<Longrightarrow>
 build_blocks bytecode = blocks \<Longrightarrow>
 block_lookup blocks n = Some (insts, Jumpi) \<Longrightarrow>
 triple_sem_t net pre (blocks_insts blocks) post"
 apply(simp only: triple_sem_t_def; clarify)
 apply(case_tac "insts")
  apply(case_tac "cond = 0"; clarify)
   apply(thin_tac "0 \<noteq> 0 \<Longrightarrow> _")+
   apply(simp)
   apply(drule_tac x=co_ctx in spec; drule_tac x="(program_sem (\<lambda>x. ()) co_ctx (Suc 0) net presult)" in spec)
   apply(drule_tac x=resta in spec)
   apply(drule mp)
    apply(cut_tac q=pre and r="(continuing \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack h 0 \<and>*
         stack_height (Suc (Suc h)) \<and>*
         program_counter n \<and>*
         stack (Suc h) (word_of_int dest) \<and>*
         \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>*
         rest)" and net=net
        in triple_seq_empty_case')
     apply(clarsimp)
    apply(drule_tac P=pre in sep_conj_imp, assumption)
    apply(drule_tac bi="(dest, Pc JUMPDEST) # bbi" and ti=ti and g=g and h=h and presult=presult and
         m=m and restb=rest and rest=resta and bytecode=bytecode and co_ctx=co_ctx
         in jumpi_sem_zero; simp add: sep_lc)
    apply(simp add: sep_lc)
   apply(simp add: program_sem_t_exec_continue)
  apply(clarsimp)
  apply(drule_tac x=co_ctx in spec; drule_tac x="(program_sem (\<lambda>x. ()) co_ctx (Suc 0) net presult)" in spec)
  apply(drule_tac x=resta in spec)
  apply(drule mp)
   apply(cut_tac q=pre and r="(continuing \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack h cond \<and>*
         stack_height (Suc (Suc h)) \<and>*
         program_counter n \<and>*
         stack (Suc h) (word_of_int dest) \<and>*
         \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>*
         rest)" and net=net
        in triple_seq_empty_case')
    apply(clarsimp)
   apply(drule_tac P=pre in sep_conj_imp, assumption)
   apply(drule_tac bi="(dest, Pc JUMPDEST) # bbi" and ti=ti and g=g and h=h and presult=presult and
         m=m and restb=rest and rest=resta
         in jumpi_sem_non_zero; simp add: sep_lc)
   apply(simp add: sep_lc)
  apply(simp add: program_sem_t_exec_continue)
 apply(cut_tac m="n + inst_size_list insts" and n=n
			 and post=" (continuing \<and>*
         gas_pred g \<and>*
         memory_usage m \<and>*
         stack h cond \<and>*
         stack_height (Suc (Suc h)) \<and>*
         stack (Suc h) (word_of_int dest) \<and>*
         \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>*
         rest)"
			 in pc_after_seq)
        apply(assumption)
			 apply(simp add: inst_res_as_set_uniq_stateelm)
			apply(clarsimp, rule iffI; (sep_cancel)+)
		  apply(clarsimp simp add: wf_blocks_def)
			apply(drule_tac x=n and y=insts in spec2, simp)
		 apply(clarsimp)
   apply(simp add: wf_blocks_def)
  apply(simp add: wf_blocks_def)
	apply(simp add: reg_vertex_def)
	apply(drule_tac x=n and y=insts in spec2, drule conjunct1, drule_tac x=Jumpi in spec; simp)
 apply(thin_tac "_ = _ # _")
 apply(drule triple_seq_soundness)
 apply(simp only: triple_seq_sem_def; clarify)
 apply(rename_tac co_ctx presult resta stopper a b list)
 apply(drule_tac x = "co_ctx" and y=presult in spec2)
 apply(drule_tac x = "code (blocks_insts blocks - set insts) \<and>* resta" in spec)
 apply(drule_tac x = "stopper" in spec)
 apply(clarsimp)
 apply(erule impE)
  apply(cut_tac iffD2[OF sep_code_code_sep_wf[where insts=insts]]; simp)
 apply(insert iffD1[OF code_code_sep_wf[where insts=insts and blocks=blocks and n=n and ty=Jumpi]])
 apply(sep_select_asm 11, sep_select_asm 11)
 apply(drule_tac x="(continuing \<and>* gas_pred g \<and>* memory_usage m \<and>* stack h cond \<and>*
         stack_height (Suc (Suc h)) \<and>* stack (Suc h) (word_of_int dest) \<and>*
         program_counter (n + (inst_size b + inst_size_list list)) \<and>*
         \<langle> h \<le> 1022 \<and> Ghigh \<le> g \<and> 0 \<le> m \<rangle> \<and>* rest) \<and>* resta" in meta_spec)
 apply(drule_tac x="instruction_result_as_set co_ctx
          (program_sem stopper co_ctx
            (Suc (length list)) net presult)" in meta_spec)
 apply(clarsimp simp add: sep_lc)
 apply(thin_tac "(continuing \<and>* _) (_)")
 apply(case_tac "cond=0"; clarsimp)
  apply(drule_tac x = "co_ctx" in spec)
  apply(drule_tac x = "(program_sem stopper co_ctx (Suc (length insts)) net presult)" in spec)
  apply(drule_tac x = "resta" in spec)
  apply (erule impE)
	 apply(cut_tac presult="(program_sem stopper co_ctx (length insts) net presult)" and
		blocks=blocks and j="n + 1 + inst_size_list insts" and bi="(dest, Pc JUMPDEST) # bbi" and ti=ti
		and bj=bj and tj=tj and h=h and g=g and net=net and
	  i=dest and restb=rest and co_ctx=co_ctx and rest=resta and stopper=stopper and m=m
  in jumpi_sem_zero; simp add: sep_lc)
		apply(simp add: sep_lc)
	 apply(simp add: execution_continue)
   apply(simp add: program_sem_t_exec_continue)
  apply(sep_simp simp:program_counter_sep)
 apply(drule_tac x = "co_ctx" in spec)
 apply(drule_tac x = "(program_sem stopper co_ctx (Suc (length insts)) net presult)" in spec)
 apply(drule_tac x = "resta" in spec)
 apply (erule impE)
	apply(cut_tac co_ctx=co_ctx and stopper=stopper and insts=insts and
		g=g and restb=rest and n=n and bi="(dest, Pc JUMPDEST) # bbi" and ti=ti and tj=tj and g=g and
		dest=dest and net=net and m=m and blocks=blocks and bytecode=bytecode and rest=resta and
    presult="(program_sem stopper co_ctx (length insts) net presult)" and h=h
  in jumpi_sem_non_zero; simp add: sep_conj_commute sep_conj_left_commute)
   apply(sep_simp simp: program_counter_sep; simp)
	apply(simp add: execution_continue)
 apply (erule_tac P="post \<and>* code (blocks_insts (build_blocks bytecode)) \<and>* resta" in back_subst)
 apply(subst program_sem_t_exec_continue; simp)
done

(* NO case *)
lemma program_sem_to_environment:
"program_sem st c k n (InstructionToEnvironment x y z) = InstructionToEnvironment x y z"
 by(induction k; simp add: program_sem.simps next_state_def)

lemma pc_before_inst:
"triple_inst net pre x post \<Longrightarrow>
x = (n, i) \<Longrightarrow>
pre s \<and> uniq_stateelm s \<Longrightarrow>
PcElm n \<in> s"
 apply(induct rule: triple_inst.induct; clarsimp)
            apply(erule triple_inst_arith.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
           apply(erule triple_inst_bits.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
          apply(erule triple_inst_info.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
         apply(erule triple_inst_memory.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
        apply(erule triple_inst_storage.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
       apply(erule triple_inst_misc.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
      apply(erule triple_inst_pc.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
     apply(erule triple_inst_stack.cases; clarsimp; sep_simp simp: pure_sep sep_fun_simps; simp)
    apply(sep_simp simp: pure_sep sep_fun_simps; simp)+
 apply(simp add: pure_def)
done

lemma pc_before_seq:
"triple_seq net pre insts post \<Longrightarrow>
fst (hd insts) = n \<Longrightarrow>
insts \<noteq> [] \<Longrightarrow>
pre s \<and> uniq_stateelm s \<Longrightarrow>
PcElm n \<in> s"
 apply(induction rule:triple_seq.induct; clarsimp)
   apply(simp add: pc_before_inst)
 apply(simp add: pure_def)
done

lemma execution_stop:
"\<forall>v. program_sem stopper co_ctx k net presult \<noteq>
		InstructionContinue v \<Longrightarrow>
program_sem_t co_ctx net presult = program_sem stopper co_ctx k net presult"
 apply(case_tac "program_sem stopper co_ctx k net presult")
   apply(fastforce)
  apply(insert program_sem_t_exec_continue[where stopper=stopper and co_ctx=co_ctx and k=k and net=net and presult=presult])
  apply(drule sym[where t="program_sem_t co_ctx net presult"])
  apply(clarsimp simp add: program_sem_t.simps)
 apply(insert program_sem_t_exec_continue[where stopper=stopper and co_ctx=co_ctx and k=k and net=net and presult=presult])
done

lemma pc_advance_continue:
"reg_inst i \<Longrightarrow>
        program_content (cctx_program co_ctx)
         (vctx_pc x) = Some i \<Longrightarrow>
       vctx_next_instruction x co_ctx = Some x2 \<Longrightarrow>
       check_resources x co_ctx (vctx_stack x) x2 net \<Longrightarrow>
       instruction_sem x co_ctx x2 net =
       InstructionContinue x1 \<Longrightarrow>
       vctx_pc x + int (length (inst_code i)) = vctx_pc x1"
apply(case_tac x2; simp add: instruction_simps)
						apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
					 apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
					apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps Let_def split:list.splits if_splits; clarsimp)
				 apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
				apply(split option.splits; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
			 apply(rename_tac y; case_tac y; clarsimp)
						 apply(simp add: instruction_simps split:list.splits; clarsimp)+
			apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
		 apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
		apply(rename_tac y; case_tac y; clarsimp; simp add: instruction_simps split:list.splits; clarsimp)
	 apply(simp add: instruction_simps split:list.splits option.splits; clarsimp)
	apply(rename_tac y; case_tac y; simp add: instruction_simps split:list.splits; clarsimp)
done

lemma stop_after_no_continue:
"insts = (vctx_pc x,i)#xs \<Longrightarrow>
last_no insts \<Longrightarrow>
seq_block insts \<Longrightarrow>
reg_vertex (m, insts, Terminal) \<Longrightarrow>
\<forall>a b. (a,b)\<in> (set insts) \<longrightarrow>
   (program_content (cctx_program co_ctx) a = Some b \<or>
   program_content (cctx_program co_ctx) a = None \<and> b = Misc STOP) \<Longrightarrow>
\<forall>v. program_sem stopper co_ctx (length insts) net (InstructionContinue x) \<noteq>
		InstructionContinue v"
 apply(induction insts arbitrary: i x xs)
  apply(simp)
 apply(clarsimp)
 apply(case_tac xs)
	apply(simp)
	apply(thin_tac "(\<And>i x xs. False \<Longrightarrow> _ x i xs \<Longrightarrow> _ x i xs \<Longrightarrow> _ x i xs \<Longrightarrow> \<forall>v. _ x i xs v)")
  apply(simp add: last_no_def)
	apply(case_tac i; simp)
   apply(simp add: program_sem.simps instruction_simps next_state_def split: if_splits)
  apply(erule disjE)
   apply(case_tac x13; simp add: program_sem.simps instruction_simps stop_def next_state_def split: if_splits option.splits list.splits)
  apply(simp add: program_sem.simps instruction_simps stop_def next_state_def split: if_splits option.splits list.splits)
 apply(drule subst[OF program_sem.simps(2), where P="\<lambda>u. u = _"])
 apply(simp add: instruction_simps next_state_def)
 apply(drule_tac x="vctx_pc x" and y=i in spec2, simp, drule conjunct1)
 apply(simp split: option.splits; clarsimp)
	apply(simp add: program_sem_to_environment split: if_splits)
	apply(simp add: instruction_sem_def stop_def subtract_gas.simps)
	apply(simp add: program_sem_to_environment)
 apply(simp add: program_sem_to_environment split: if_splits)
 apply(drule_tac x="b" in meta_spec; simp)
 apply(case_tac "(instruction_sem x co_ctx i net)")
	 apply(simp)
	 apply(drule_tac x=x1 and y=list in meta_spec2)
	 apply(subgoal_tac "vctx_pc x + int (length (inst_code i)) = vctx_pc x1")
    apply(simp add: seq_block.simps inst_size_def; clarsimp)
		apply(simp add: last_no_def reg_block_def reg_vertex_def; fastforce)
	 apply(insert pc_advance_continue[where co_ctx=co_ctx])
   apply(drule_tac x=i and y=x in meta_spec2;
          drule_tac x=i and y=net in meta_spec2; drule_tac x=x1 in meta_spec)
   apply(simp add: reg_block_def reg_vertex_def instruction_simps)
 apply(simp add: program_sem_to_environment)
done

lemma blocks_no_sem_t:
" triple_seq net pre insts post \<Longrightarrow>
	 wf_blocks blocks \<Longrightarrow>
	 block_lookup blocks (v_ind (n, insts, Terminal)) =
	 Some (snd (n, insts, Terminal)) \<Longrightarrow>
	 triple_sem_t net pre (blocks_insts blocks) post"
 apply(simp add: triple_sem_t_def; clarsimp)
 apply(insert pc_before_seq[where n=n and pre=pre and insts=insts and post=post and net=net]; simp)
 apply(drule triple_seq_soundness)
 apply(simp add: triple_seq_sem_def)
 apply(rename_tac co_ctx presult rest)
 apply(drule_tac x = co_ctx in spec)
 apply(drule_tac x = presult and y = "code (blocks_insts blocks - set insts) \<and>* rest" in spec2)
 apply(drule mp)
 apply(simp add: sep_code_code_sep_wf)
 apply(drule_tac x="\<lambda>x. ()" in spec)
 apply(subgoal_tac "wf_blocks blocks")
  prefer 2 apply(assumption)
 apply(subst (asm) wf_blocks_def)
 apply(clarsimp)
 apply(drule spec2[where x=n and y=insts])
 apply(erule conjE)
 apply(drule spec[where x=Terminal])
 apply(drule mp, assumption)
 apply(drule conjunct2, drule conjunct2, drule conjunct2, drule conjunct1, simp, erule conjE)
 apply(simp add: sep_code_code_sep_wf)
 apply(subst execution_stop[where k="length insts" and stopper="\<lambda>x. ()"])
  apply(case_tac presult)
    apply(case_tac insts)
     apply(clarsimp)
    apply(subgoal_tac "a = (vctx_pc x1, snd a)")
     apply(cut_tac x=x1 and i="snd a" and xs=list and m=n and co_ctx=co_ctx and net=net
      in stop_after_no_continue[where insts=insts and stopper="\<lambda>x. ()"]; simp)
       apply(simp add: wf_blocks_def)
			apply(simp add: wf_blocks_def)
     apply(drule_tac r=rest and s="instruction_result_as_set co_ctx (InstructionContinue x1)"
        in sep_code_code_sep_wf[where p=pre]; simp)
     apply(sep_simp simp: code_sep[where rest="pre \<and>* _" and pairs="set _"])
     apply(simp add: instruction_result_as_set_def)
     apply(clarsimp simp add: code_elms code_elm_c)
		 apply(rule conjI)
		  apply(simp add:  code_element_means)
		 apply(clarsimp)
     apply(subgoal_tac "CodeElm (aa, ba) \<in> insert (ContinuingElm True) (contexts_as_set x1 co_ctx)")
      apply(clarsimp simp add: stateelm_means_simps)
     apply(subgoal_tac "CodeElm (aa, ba) \<in> {CodeElm (pos, i) |pos i. (pos, i) \<in> set list}")
      apply(rule_tac A="{CodeElm (pos, i) |pos i. (pos, i) \<in> set list}" in set_rev_mp; simp)
		 apply(clarsimp)
    apply(simp add: sep_conj_def[where P=pre])
    apply(clarsimp)
    apply(drule_tac x=x in meta_spec)
    apply(drule meta_mp)
     apply(simp)
     apply(rule_tac Q="instruction_result_as_set co_ctx (InstructionContinue x1)"
           and R=y in uniq_stateelm_subset)
      apply(simp)
     apply(rule uniq_stateelm_inst_res)
    apply(subgoal_tac "PcElm n \<in> instruction_result_as_set co_ctx (InstructionContinue x1)")
     apply(thin_tac "instruction_result_as_set _ _ = _")
     apply(drule subst[OF instruction_result_as_set_def, where P="\<lambda>u. PcElm n \<in> u"], simp)
		 apply(simp add: wf_blocks_def)
		 apply(drule_tac x=n and y="(n, b) # list" in spec2, simp)
		apply(simp add: pcElmEquiv)
   apply(simp add: plus_set_def)
  apply(simp add: program_sem_to_environment)
 apply(simp)
done

lemma triple_soundness_aux:
"triple_blocks net blocks pre v post \<Longrightarrow>
 wf_blocks blocks \<Longrightarrow>
 build_blocks bytecode = blocks \<Longrightarrow>
 block_lookup blocks (v_ind v) = Some (snd v) \<Longrightarrow>
 triple_sem_t net pre (blocks_insts blocks) post"
 apply(induction rule: triple_blocks.induct)
		 apply(simp add: blocks_no_sem_t)
		apply(simp add: blocks_next_sem_t)
	 apply(simp add: blocks_jump_sem_t sep_lc)
  apply(simp add: blocks_jumpi_sem_t sep_lc)
  apply(simp add: triple_sem_t_def pure_sep)
  apply (clarsimp simp add: triple_sem_t_def sep_lc pure_sep)
  apply (drule spec)
  apply (drule spec)
  apply (drule_tac x=rest in spec)
  apply (drule mp)
   apply (sep_cancel)+
   apply simp+
 done

lemma blocks_insts_eq_add_address:
"set (add_address bytecode) = blocks_insts (build_blocks bytecode)"
apply(simp add: blocks_insts_def)
apply(subst arg_cong[where f=set and y="rebuild_with_add (build_blocks bytecode)"])
 apply(subst rev_rebuild_with_add)
 apply(rule refl)+
done

lemma aux_bb_not_Nil:
"aux_basic_block (x#xs) ys \<noteq> []"
apply(induction xs arbitrary: ys x; clarsimp)
 apply(simp add: aux_basic_block.simps Let_def)
 apply(case_tac "reg_inst b \<and> b \<noteq> Pc JUMPDEST")
    apply(simp split: reg_inst_splits; case_tac "(ys @ [(a,b)])"; simp add: aux_basic_block.simps)
   apply(split reg_inst_splits if_splits; simp add: aux_basic_block.simps)
  apply(case_tac x9; simp split:if_splits add: aux_basic_block.simps)
apply(drule subst[OF aux_basic_block.simps(3), where P="\<lambda>u. u = []"])
apply(simp add: Let_def split: list.splits reg_inst_splits)
apply(simp split: if_splits)
done

theorem triple_soundness:
"bytecode \<noteq> [] \<Longrightarrow>
fst (last (add_address bytecode)) < 2 ^ 256 \<Longrightarrow>
triple net pre (build_blocks bytecode) post \<Longrightarrow>
triple_sem_t net pre (set (add_address bytecode)) post"
 apply(simp add: triple_def blocks_insts_eq_add_address)
 apply(subst triple_soundness_aux)
		 apply(simp)
		apply(simp add: wf_build_blocks)
	 apply(simp)
  apply(simp add: build_blocks_def Let_def)
  apply(case_tac "build_basic_blocks bytecode")
   apply(simp add: build_basic_blocks_def add_address_def)
   apply(induction bytecode; simp add: aux_bb_not_Nil)
  apply(clarsimp)
 apply(simp)
done

end
