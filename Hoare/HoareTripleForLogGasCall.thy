theory HoareTripleForLogGasCall

imports Main "HoareTripleForInstructions"

begin

context
  includes hoare_bundle hoare_inst_bundle
           sep_crunch_bundle simp_for_triples_bundle

begin

lemma account_existence_not_stack_top [simp] :
  "\<forall> len. AccountExistenceElm x29 \<notin> stack_topmost_elms len ss"
 by (induction ss; auto)

lemma logged_sep [simp]:
  "(logged n l ** a) s =
   (LogElm (n, l) \<in> s \<and> a (s - {LogElm (n, l)}))"
  by (solve_sep_iff simp: logged_def)
    
lemma memory_range_elms_conjD:
  "memory_range_elms logged_start data \<subseteq> {x. x \<noteq> v \<and> P x} \<Longrightarrow> v \<notin> range MemoryElm  \<Longrightarrow>
   memory_range_elms logged_start data \<subseteq> {x. P x}"
  by auto

lemma memory_range_elms_disjD:
  "memory_range_elms logged_start data \<subseteq> {x. x = v \<or> P x} \<Longrightarrow> v \<notin> range MemoryElm  \<Longrightarrow>
   memory_range_elms logged_start data \<subseteq> {x. P x}"
  by (induct data arbitrary:logged_start; clarsimp)

lemma move_neq_first:
   "{x. P x \<and> x \<noteq> v} = {x. x \<noteq> v \<and> P x}"
   "{x. P x \<and> x \<noteq> v \<and> Q x} = {x. x \<noteq> v \<and> P x \<and> Q x}"
  by blast+


lemma log0_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1022 \<and> length data = unat logged_size \<rangle> **
           memory_range logged_start data **
           this_account this **
           log_number n **
           gas_pred g **
           stack_topmost h [logged_size, logged_start] **
           program_counter k ** 
           memory_usage m **
           continuing)
          {(k, Log LOG0)}
          (memory_range logged_start data **
           this_account this **
           log_number (Suc n) **
           logged n \<lparr> log_addr = this, log_topics = [], log_data = data \<rparr>  **
           stack_topmost h [] **
           gas_any **
           program_counter (k + 1) ** 
           memory_usage (M m logged_start logged_size) **
           continuing)
  "
apply (simp add: triple_def)
apply clarify
  apply (rule_tac x = 1 in exI)
  apply (case_tac presult)
    defer
    apply (simp)
   apply (simp  add:  memory_range_sep )
apply(rename_tac continued)
apply(simp add: log_inst_numbers.simps sep_memory_range
      sep_memory_range_sep log_def memory_range_sep
        instruction_result_as_set_def insert_minus_set
vctx_stack_default_def set_diff_expand set_diff_eq )
  apply clarify
  apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def
              elim: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)
  apply (drule (1) set_mp)
  apply (rename_tac elm, case_tac elm; simp)
  apply (erule_tac P=rest in  back_subst)
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
   apply(rename_tac st)
   apply(case_tac st; clarsimp)
   apply(erule disjE; clarsimp)
  apply auto[1]
 apply(simp add: gasprice_advance_pc)
apply auto
apply(rename_tac elm; case_tac elm; simp)
apply auto
done

lemma imp_to_disjD: "P \<longrightarrow> Q \<Longrightarrow> \<not>P \<or> Q"
by blast

lemma log1_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1021 \<and> length data = unat logged_size \<rangle> **
           memory_range logged_start data **
           this_account this **
           log_number n **
           gas_pred g **
           stack_topmost h [topic0, logged_size, logged_start] **
           program_counter k ** 
           memory_usage m **
           continuing)
          {(k, Log LOG1)}
          (memory_range logged_start data **
           this_account this **
           log_number (Suc n) **
           logged n \<lparr> log_addr = this, log_topics = [topic0], log_data = data \<rparr>  **
           stack_topmost h [] **
           gas_any **
           program_counter (k + 1) ** 
           memory_usage (M m logged_start logged_size) **
           continuing)
  "
apply (simp add: triple_def)
apply clarify
apply (rule_tac x = 1 in exI)
apply (case_tac presult)
  defer
  apply(simp)
 apply(simp add:  memory_range_sep )
apply(simp add: log_inst_numbers.simps 
      log_def memory_range_sep
      instruction_result_as_set_def insert_minus_set
      vctx_stack_default_def set_diff_expand set_diff_eq )
apply clarify
apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def
            elim: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)
apply (drule (1) set_mp)
apply (rename_tac elm, case_tac elm; simp)
apply (erule_tac P=rest in  back_subst)
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; clarsimp)
 apply (drule imp_to_disjD, erule disjE; clarsimp)
 apply (simp add: gasprice_advance_pc)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; clarsimp)
done


lemma log2_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1020 \<and> length data = unat logged_size \<rangle> **
           memory_range logged_start data **
           this_account this **
           log_number n **
           gas_pred g **
           stack_topmost h [topic1, topic0, logged_size, logged_start] **
           program_counter k ** 
           memory_usage m **
           continuing)
          {(k, Log LOG2)}
          (memory_range logged_start data **
           this_account this **
           log_number (Suc n) **
           logged n \<lparr> log_addr = this, log_topics = [topic0, topic1], log_data = data \<rparr>  **
           stack_topmost h [] **
           gas_any **
           program_counter (k + 1) ** 
           memory_usage (M m logged_start logged_size) **
           continuing)
  "
apply (simp add: triple_def)
apply clarify
  apply (rule_tac x = 1 in exI)
  apply(case_tac presult; (solves \<open>simp add:memory_range_sep \<close>)?)
  apply( simp add: sep_memory_range sep_memory_range_sep memory_range_sep
        log_inst_numbers.simps log_def 
        instruction_result_as_set_def vctx_stack_default_def )
  apply clarify
    (* There should be a way to speedup the lines above with set_diff_eq *)
  apply (clarsimp simp only: set_diff_expand stateelm_means_simps stateelm_equiv_simps set_diff_eq)
 apply (rule conjI)
    apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def set_diff_eq
            elim!: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)[1]   
 apply (rule conjI)
  apply (clarsimp simp: set_diff_eq)
 apply (rule conjI)
  apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def set_diff_eq
              elim: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)[1]   
apply (erule_tac P=rest in back_subst)
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length tc"; simp)
apply clarify
apply simp
   apply(rename_tac elm; case_tac elm; simp)
       apply (case_tac "ad = Suc (length tc)" ; clarsimp)
   apply (case_tac "ad = (length tc)" ; clarsimp)
  apply (case_tac "ad = Suc (Suc (Suc (length tc)))" ; clarsimp)
apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def set_diff_eq
            elim: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)[1]
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
done


lemma log3_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1019 \<and> length data = unat logged_size \<rangle> **
           memory_range logged_start data **
           this_account this **
           log_number n **
           gas_pred g **
           stack_topmost h [topic2, topic1, topic0, logged_size, logged_start] **
           program_counter k ** 
           memory_usage m **
           continuing)
          {(k, Log LOG3)}
          (memory_range logged_start data **
           this_account this **
           log_number (Suc n) **
           logged n \<lparr> log_addr = this, log_topics = [topic0, topic1, topic2], log_data = data \<rparr>  **
           stack_topmost h [] **
           gas_any **
           program_counter (k + 1) ** 
           memory_usage (M m logged_start logged_size) **
           continuing)
  "
apply (simp add: triple_def)
apply clarify
apply (rule_tac x = 1 in exI)
  apply(case_tac presult; simp add:memory_range_sep)
  apply (erule conjE)+
  apply (simp only: set_diff_expand set_diff_eq)
 apply (simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def vctx_stack_default_def
        memory_range_sep set_diff_expand insert_minus_set)
  apply clarify
  apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def
              elim!: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)
apply (erule_tac P=rest in back_subst)
apply(rule Set.equalityI)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "fst x2 < length td"; clarsimp)
apply clarify
apply (simp add: set_diff_expand set_diff_eq)
apply clarsimp
apply(rename_tac elm; case_tac elm; clarsimp)
done

lemma log4_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1018 \<and> length data = unat logged_size \<rangle> **
           memory_range logged_start data **
           this_account this **
           log_number n **
           gas_pred g **
           stack_topmost h [topic3, topic2, topic1, topic0, logged_size, logged_start] **
           program_counter k ** 
           memory_usage m **
           continuing)
          {(k, Log LOG4)}
          (memory_range logged_start data **
           this_account this **
           log_number (Suc n) **
           logged n \<lparr> log_addr = this, log_topics = [topic0, topic1, topic2, topic3],
                      log_data = data \<rparr>  **
           stack_topmost h [] **
           gas_any **
           program_counter (k + 1) ** 
           memory_usage (M m logged_start logged_size) **
           continuing)
  "
apply (simp add: triple_def)
apply clarify
  apply (rule_tac x = 1 in exI)
  apply (case_tac presult; simp add: memory_range_sep)
apply(clarsimp simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def vctx_stack_default_def set_diff_eq set_diff_expand
memory_range_sep insert_minus_set)
      apply (auto simp: move_neq_first create_log_entry_def vctx_returned_bytes_def 
              elim!: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)
 apply (auto simp add: as_set_simps)[1]
   defer
    apply (auto split: if_split_asm simp: log_inst_numbers.simps)[1]
apply (erule_tac P=rest in back_subst)
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length te"; simp)
apply clarify
   apply (simp add: set_diff_expand set_diff_eq)
   apply (case_tac "a = Suc (Suc (Suc (Suc (Suc (length te)))))"; clarsimp)
   apply (auto simp: set_diff_eq)
  apply(rename_tac elm; case_tac elm; simp)
  apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
  done
    
lemma call_gas_triple:
  notes meter_gas_def [simp del]
  shows
  "triple net {OutOfGas}
          (\<langle> h \<le> 1017 \<and> fund \<ge> v \<and> length input = unat in_size \<and> at_least_eip150 net \<rangle> ** 
           program_counter k ** memory_range in_begin input **
           stack_topmost h [out_size, out_begin, in_size, in_begin, v, r, g] **
           gas_pred own_gas **
           memory_usage u **
           this_account this **
           balance this fund **
           account_existence (Word.ucast r) existence **
           continuing)
          {(k, Misc CALL)}
          (memory_range in_begin input **
           stack_topmost h [] **
           this_account this **
           balance this (fund - v) **
           program_counter (k + 1) ** 
           gas_any **
           memory_usage (M (M u in_begin in_size) out_begin out_size) **
           account_existence (Word.ucast r) existence **
           not_continuing **
           action (ContractCall
             \<lparr> callarg_gas = (word_of_int (Ccallgas g r v
                     (\<not> existence) own_gas net
                     (calc_memu_extra u g r v in_begin in_size out_begin out_size)))
             , callarg_code = ucast r
             , callarg_recipient = ucast r
             , callarg_value = v
             , callarg_data = input
             , callarg_output_begin = out_begin
             , callarg_output_size = out_size \<rparr>))"
  apply(simp only: triple_triple_alt)

  apply(auto simp add: triple_alt_def set_diff_expand set_diff_eq memory_range_sep[rule_format])
apply(rule_tac x = 1 in exI)
  apply(case_tac presult; simp)
apply(clarify)
apply(simp add: call_def)
apply(simp add: instruction_result_as_set_def vctx_recipient_def)
apply(simp add: sep_memory_range_sep sep_memory_range memory_range_sep failed_for_reasons_def)
    apply(simp add: vctx_stack_default_def)
        apply (rule conjI, (auto simp: move_neq_first 
                        elim!: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)[1])+

apply(erule_tac P=rest in back_subst)
apply(rule Set.equalityI)
 apply(clarify)
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
  apply(case_tac "length tf \<le> fst x2"; clarsimp)
 apply(clarsimp)
 apply(subgoal_tac "a = cctx_this co_ctx")
  apply(simp)
 apply(case_tac "a = cctx_this co_ctx")
  apply(simp)
 apply(simp)
apply(clarsimp)
    apply(rename_tac elm; case_tac elm; clarsimp)
    apply (case_tac "vctx_balance x1 a = update_balance (cctx_this co_ctx) (\<lambda>orig. orig - v) (vctx_balance x1) a"; clarsimp)
   apply (auto simp: move_neq_first elim!: set_mp dest!: memory_range_elms_conjD memory_range_elms_disjD)
done

end


context
  includes hoare_bundle hoare_inst_bundle
           sep_crunch_bundle simp_for_triples_bundle    
  notes gas_def [simp]
begin

lemma gas_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1023 \<rangle> ** stack_height h ** program_counter k ** gas_pred g ** continuing)
          {(k, Info GAS)}
          (stack_height (h + 1) ** stack h (word_of_int (g - 2))
           ** program_counter (k + 1) ** gas_pred (g - 2) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; simp add:set_diff_expand set_diff_eq memory_range_sep[rule_format])
apply(clarsimp simp add: Word.wi_hom_syms(2))
apply(erule_tac P=rest in back_subst)
apply (clarsimp simp: instruction_result_as_set_def)
apply(rule  Set.equalityI; clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; clarsimp)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; auto simp add: Word.wi_hom_syms(2))
done
end


end
