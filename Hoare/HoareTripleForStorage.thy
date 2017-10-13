theory "HoareTripleForStorage" 

imports "HoareTripleForInstructions"
begin

lemma storage_inst_advance [simp] :
"program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Storage m) \<Longrightarrow>
 k = vctx_pc x1 \<Longrightarrow>
 vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
by (simp add: vctx_next_instruction_def 
 vctx_advance_pc_def inst_size_def inst_code.simps)


lemma update_storage_preserves_pc [simp] :
"vctx_pc (vctx_update_storage idx new x1) = vctx_pc x1"
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
    
lemma next_state_noop[simp]:
  "next_state stopper c net (InstructionToEnvironment x y z) = (InstructionToEnvironment x y z)" 
  by (simp add: next_state_def)+

lemmas hoare_simps = stateelm_means_simps stateelm_equiv_simps 
       next_state_def rev_nth_simps instruction_sem_simps gas_value_simps
      inst_numbers_simps instruction_failure_result_def 
      advance_pc_simps
      
method hoare_sep uses sep simp dest split =
 ((sep_simp simp: sep)+,
  clarsimp simp: simp dest:dest split:split)

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
  apply (clarsimp simp: triple_def)
  apply(rule_tac x = 1 in exI)
  apply (clarsimp simp add: program_sem.simps)
  apply(case_tac presult ; (solves \<open>(hoare_sep sep: evm_sep simp:   stateelm_means_simps dest: stateelm_dest)\<close>) ?)
  apply (hoare_sep sep: evm_sep 
                   simp: instruction_result_as_set_def  sstore_def
                         vctx_update_storage_def hoare_simps
                  split:if_splits) 
  apply (erule_tac P=rest in back_subst)
  apply(rule Set.equalityI; clarify)
  apply(rename_tac elm)
  apply(simp add: vctx_update_storage_def) 
  apply (case_tac elm; simp add: hoare_simps split:if_splits) 
  using some_list_gotcha gasprice_advance_pc apply blast
  apply(rename_tac elm)
  apply (simp add: set_diff_eq) 
  apply (case_tac elm; simp add: hoare_simps  split:if_splits) 
  apply auto
done


lemma sload_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle>
           ** block_number_pred bn ** stack_height (h + 1)
           ** stack h idx
           ** program_counter k ** storage idx w ** gas_pred g **  account_existence c existence ** continuing)
          {(k, Storage SLOAD)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h w
           ** program_counter (k + 1) ** storage idx w ** gas_pred (g - Gsload net) **  account_existence c existence ** continuing )"
apply(clarsimp simp add: triple_def)
  apply(rule_tac x = 1 in exI)
  apply(clarsimp simp add: program_sem.simps)
  apply(case_tac presult;  (solves \<open>(hoare_sep sep: evm_sep simp:  set_diff_eq stateelm_means_simps dest: stateelm_dest)\<close>)?)
  apply clarsimp
  apply(hoare_sep sep: evm_sep 
                   simp: instruction_result_as_set_def  sstore_def
                         vctx_update_storage_def hoare_simps set_diff_eq
                  split:if_split_asm)
  apply(erule_tac P=rest in back_subst)
  apply(rule  Set.equalityI; clarify)
  apply(simp)
  apply(rename_tac elm)
  apply(case_tac elm; simp add: hoare_simps split:if_splits)
  apply(rename_tac pair)
  apply(case_tac pair; fastforce)
  apply(simp)
  apply(rename_tac elm)
  apply(case_tac elm; simp add: hoare_simps split:if_splits)
  apply(rename_tac pair)
  apply(case_tac pair; fastforce)
done

end