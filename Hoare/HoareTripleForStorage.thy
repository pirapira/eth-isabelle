theory "HoareTripleForStorage" 

imports "HoareTripleForInstructions"
 "../attic/Apply_Trace_Cmd"
begin

lemma storage_inst_advance [simp] :
"program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Storage m) \<Longrightarrow>
 k = vctx_pc x1 \<Longrightarrow>
 vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
by (simp add: vctx_next_instruction_def 
 vctx_advance_pc_def inst_size_def inst_code.simps)


lemma update_storage_preserves_pc [simp] :
"vctx_pc
  (vctx_update_storage idx new x1) =
 vctx_pc x1"
by (simp add: vctx_update_storage_def)

lemma update_storage_updates [simp] :
"vctx_storage (vctx_update_storage idx new x1) idx = new"
by (simp add: vctx_update_storage_def)

lemma update_storage_preserves_gas [simp] :
  "vctx_gas (vctx_update_storage idx new x1) = vctx_gas x1"
by (simp add: vctx_update_storage_def)

lemma some_list_gotcha :
  "       rev ta ! fst x2 = snd x2 \<longrightarrow> \<not> fst x2 < length ta \<Longrightarrow>
       x2 \<noteq> (Suc (length ta), idx) \<Longrightarrow>
       x2 \<noteq> (length ta, new) \<Longrightarrow>
       (fst x2 < length ta \<and> rev ta ! fst x2 = snd x2 \<or>
        length ta \<le> fst x2 \<and> [new, idx] ! (fst x2 - length ta) = snd x2) \<and>
       fst x2 < Suc (Suc (length ta)) \<Longrightarrow>
       elm = StackElm x2 \<Longrightarrow> False"
apply(case_tac x2; auto)
 apply(case_tac "a - length ta"; simp)
 apply(rename_tac smaller)
 apply(case_tac smaller; simp)
apply(case_tac "a - length ta"; simp)
apply(rename_tac smaller)
apply(case_tac smaller; simp)
done

lemma sstore_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1024\<rangle>
           ** stack_height (h + 2)
           ** stack (h + 1) idx
           ** stack h new
           ** program_counter k ** storage idx old
           ** gas_pred g ** continuing)
          {(k, Storage SSTORE)}
          (stack_height h
           ** program_counter (k + 1) ** storage idx new **
           gas_pred (g - Csstore old new) ** continuing)"
  apply (clarsimp simp: triple_def simp_for_triples sep_crunch)
apply(rule_tac x = 1 in exI)
  apply(case_tac presult ; (solves \<open>clarsimp simp:Hoare_legacy_simps HoareTripleForInstructions_legacy_simps\<close>)?)
(*  apply (rule disjCI) *)
apply_trace (clarsimp simp add: simp_for_triples sep_crunch
       instruction_result_as_set_def  sstore_def
       vctx_update_storage_def Hoare_legacy_simps HoareTripleForInstructions_legacy_simps)
apply (erule_tac P=rest in back_subst)
apply(rule Set.equalityI; clarify)
apply(rename_tac elm)
apply(simp add: vctx_update_storage_def) 
apply(case_tac elm; simp add: Hoare_legacy_simps HoareTripleForInstructions_legacy_simps)
using some_list_gotcha apply blast
apply(split if_splits; simp add: Hoare_legacy_simps HoareTripleForInstructions_legacy_simps)
apply(rename_tac elm)
apply (simp add: set_diff_eq) 
apply(case_tac elm; simp add: Hoare_legacy_simps HoareTripleForInstructions_legacy_simps)
 apply auto[1]
  apply_trace(split if_splits; simp add: Hoare_legacy_simps HoareTripleForInstructions_legacy_simps)
  find_theorems  "ContinuingElm ?b \<notin> contexts_as_set ?x32.0 ?co_ctx"
done

(*
lemma sstore_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1024\<rangle>
           ** stack_height (h + 2)
           ** stack (h + 1) idx
           ** stack h new
           ** program_counter k ** storage idx old
           ** gas_pred g ** continuing)
          {(k, Storage SSTORE)}
          (stack_height h
           ** program_counter (k + 1) ** storage idx new **
           gas_pred (g - Csstore old new) ** continuing)"
apply(auto simp add: triple_def)
apply (subgoal_tac "((gas_pred g \<and>*
         program_counter k \<and>*
         stack h new \<and>*
         storage idx old \<and>*
         stack (Suc h) idx \<and>* stack_height (Suc (Suc h)) \<and>* \<langle> h \<le> 1024 \<rangle> \<and>* continuing) \<and>*
        rest) = (gas_pred g \<and>*
         program_counter k \<and>*
         stack h new \<and>*
         storage idx old \<and>*
         stack (Suc h) idx \<and>* stack_height (Suc (Suc h)) \<and>* \<langle> h \<le> 1024 \<rangle> \<and>* continuing \<and>*
        rest)")
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add:
   instruction_result_as_set_def sstore_def)
apply (subgoal_tac "((stack_height (length ta) \<and>*
         storage idx new \<and>*
         program_counter (vctx_pc x1 + 1) \<and>*
         gas_pred
          (vctx_gas x1 - Csstore (vctx_storage x1 idx) new) \<and>*
         continuing) \<and>*
        rest) = (stack_height (length ta) \<and>*
         storage idx new \<and>*
         program_counter (vctx_pc x1 + 1) \<and>*
         gas_pred
          (vctx_gas x1 - Csstore (vctx_storage x1 idx) new) \<and>*
         continuing \<and>*
        rest)")
apply (auto simp add:
   instruction_result_as_set_def sstore_def vctx_update_storage_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI; clarify)
 apply(rename_tac elm)
 apply(simp add: vctx_update_storage_def)
 apply(case_tac elm; simp)
 using some_list_gotcha apply blast
 apply(split if_splits; simp)
apply(rename_tac elm)
apply(case_tac elm; simp)
 apply auto[1]
defer
  apply (metis (no_types, hide_lams) sep.mult.left_commute sep.mult_commute)
  apply (metis (no_types, hide_lams) sep.mult.left_commute sep.mult_commute)

apply (simp add:vctx_advance_pc_def)

using foo apply force
done
*)

lemma sload_gas_triple :
  notes simp_for_triples[simp] sep_crunch[simp]
 shows
  "triple net {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle>
           ** block_number_pred bn ** stack_height (h + 1)
           ** stack h idx
           ** program_counter k ** storage idx w ** gas_pred g ** continuing)
          {(k, Storage SLOAD)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h w
           ** program_counter (k + 1) ** storage idx w ** gas_pred (g - Gsload net) ** continuing )"
apply(clarsimp simp add: triple_def )
apply(rule_tac x = 1 in exI)
apply(case_tac presult ; (solves \<open>clarsimp\<close>)?)
apply(clarsimp simp add: instruction_result_as_set_def)
apply(erule_tac P=rest in back_subst)
apply(rule  Set.equalityI; clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; simp)
 apply(rename_tac pair)
 apply(case_tac pair; fastforce)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; simp)
apply(rename_tac pair)
apply(case_tac pair; fastforce)
done

end