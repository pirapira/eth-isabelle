theory HoareTripleForLogGasCall

imports Main "HoareTripleForInstructions"

begin

context
  includes sep_crunch simp_for_triples

begin

lemma log0_gas_triple :
  "triple {OutOfGas}
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
apply(case_tac presult; simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def
vctx_stack_default_def)
apply clarify
apply auto
apply (rule leibniz)
apply blast
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length ta"; simp)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
done


lemma log1_gas_triple :
  "triple {OutOfGas}
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
apply(case_tac presult; simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def
vctx_stack_default_def)
apply clarify
apply auto
apply (simp add: create_log_entry_def vctx_returned_bytes_def)
apply (rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "rev tb ! fst x2 = snd x2"; simp)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
apply (simp add: create_log_entry_def vctx_returned_bytes_def)
done


lemma log2_gas_triple :
  "triple {OutOfGas}
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
apply(case_tac presult; simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def)
apply clarify
apply(rule_tac x = " vctx_gas x1 - meter_gas (Log LOG2) x1 co_ctx" in exI)
apply (simp add: create_log_entry_def vctx_returned_bytes_def)
apply (rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length tc"; simp)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
done


lemma log3_gas_triple :
  "triple {OutOfGas}
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
apply(case_tac presult; simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def)
apply clarify
apply(rule_tac x = " vctx_gas x1 - meter_gas (Log LOG3) x1 co_ctx" in exI)
apply (simp add: create_log_entry_def vctx_returned_bytes_def)
apply (rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length td"; simp)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
done

lemma log4_gas_triple :
  "triple {OutOfGas}
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
apply(case_tac presult; simp add: log_inst_numbers.simps sep_memory_range sep_memory_range_sep log_def
        instruction_result_as_set_def)
apply clarify
apply(rule_tac x = " vctx_gas x1 - meter_gas (Log LOG4) x1 co_ctx" in exI)
apply (simp add: create_log_entry_def vctx_returned_bytes_def)
apply (rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply clarify
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length te"; simp)
apply clarify
apply simp
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "length (vctx_logs x1) \<le> fst x5"; auto)
done

end

context
  includes sep_crunch simp_for_triples
begin

(* not correct anymore, gas for called is calculated
 differently
lemma call_gas_triple:
  "triple {OutOfGas}
          (\<langle> h \<le> 1017 \<and> fund \<ge> v \<and> length input = unat in_size \<rangle> ** 
           program_counter k ** memory_range in_begin input **
           stack_topmost h [out_size, out_begin, in_size, in_begin, v, r, g] **
           gas_pred own_gas **
           memory_usage u **
           this_account this **
           balance this fund **
           continuing)
          {(k, Misc CALL)}
          (memory_range in_begin input **
           stack_topmost h [] **
           this_account this **
           balance this (fund - v) **
           program_counter (k + 1) ** 
           gas_any **
           memory_usage (M (M u in_begin in_size) out_begin out_size) **
           not_continuing **
           action (ContractCall \<lparr> callarg_gas = g
                                , callarg_code = ucast r
                                , callarg_recipient = ucast r
                                , callarg_value = v
                                , callarg_data = input
                                , callarg_output_begin = out_begin
                                , callarg_output_size = out_size \<rparr>))"
apply(simp only: triple_triple_alt)
apply(auto simp add: triple_alt_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; simp)
apply(clarify)
apply(simp add: call_def)
apply(rule_tac x = "vctx_gas x1 - meter_gas (Misc CALL) x1 co_ctx" in exI)
apply(simp add: instruction_result_as_set_def)
apply(simp add: sep_memory_range_sep sep_memory_range failed_for_reasons_def )
apply(simp add: vctx_stack_default_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarify)
 apply simp
 apply(rename_tac elm; case_tac elm; simp)
  apply(case_tac "length tf \<le> fst x2"; simp)
 apply(clarsimp)
 apply(subgoal_tac "a = cctx_this co_ctx")
  apply(simp)
 apply(case_tac "a = cctx_this co_ctx")
  apply(simp)
 apply(simp)
apply(clarsimp)
apply(rename_tac elm; case_tac elm; simp)
apply(auto)
done
*)

end


context
  includes sep_crunch simp_for_triples
  notes stack_height_sep [simp]
  notes stack_sep [simp]
  notes program_counter_sep [simp]
  notes gas_def [simp]
begin

lemma gas_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<rangle> ** stack_height h ** program_counter k ** gas_pred g ** continuing)
          {(k, Info GAS)}
          (stack_height (h + 1) ** stack h (word_of_int (g - 2))
           ** program_counter (k + 1) ** gas_pred (g - 2) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
 apply(simp add: Word.wi_hom_syms(2))
apply(rule leibniz)
 apply blast
apply(rule  Set.equalityI; clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; simp)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; auto simp add: Word.wi_hom_syms(2))
done
end


end
