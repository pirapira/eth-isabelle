theory "HoareTripleForStorage" 

imports "HoareTripleForInstructions"

begin

context
 includes simp_for_triples
begin

lemma storage_inst_advance [simp] :
"program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Storage m) \<Longrightarrow>
 k = vctx_pc x1 \<Longrightarrow>
 vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps)
done


lemma update_storage_preserves_pc [simp] :
"vctx_pc
  (vctx_update_storage idx new x1) =
 vctx_pc x1"
apply(simp add: vctx_update_storage_def)
done

lemma update_storage_updates [simp] :
"vctx_storage (vctx_update_storage idx new x1) idx = new"
apply(simp add: vctx_update_storage_def)
done

lemma update_storage_preserves_gas [simp] :
  "vctx_gas (vctx_update_storage idx new x1) = vctx_gas x1"
apply(simp add: vctx_update_storage_def)
done

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

context
 includes sep_crunch
 notes Gsset_def [simp]
begin

lemma foo :
      "vctx_stack x1 = idx # new # ta \<Longrightarrow>
       x \<in> contexts_as_set x1 co_ctx \<longrightarrow>
       x = CodeElm (vctx_pc x1, Storage SSTORE) \<or>
       x = PcElm (vctx_pc x1) \<or>
       x = StackElm (length ta, new) \<or>
       x = StackElm (Suc (length ta), idx) \<or>
       x = StackHeightElm (Suc (Suc (length ta))) \<or>
       x = StorageElm (idx, vctx_storage x1 idx) \<Longrightarrow>
       x \<noteq> StorageElm (idx, new) \<Longrightarrow>
       x \<noteq> GasElm (vctx_gas x1 - Csstore (vctx_storage x1 idx) new) \<Longrightarrow>
       x \<noteq> PcElm (vctx_pc x1 + 1) \<Longrightarrow>
       x \<noteq> ContinuingElm True \<Longrightarrow>
       x \<noteq> StackHeightElm (length ta) \<Longrightarrow>
       (x = PcElm (vctx_pc x1 + inst_size (Storage SSTORE)) \<or>
        x \<in> contexts_as_set
              (x1\<lparr>vctx_storage :=
                    \<lambda>x. if x = idx then new else vctx_storage x1 x,
                    vctx_stack := ta,
                    vctx_touched_storage_index :=
                      idx # vctx_touched_storage_index x1,
                    vctx_refund :=
                      vctx_refund x1 + check_refund (vctx_storage x1 idx) new\<rparr>)
              co_ctx \<and>
        x \<noteq> PcElm (vctx_pc x1)) \<and>
       x \<noteq> GasElm (vctx_gas x1) \<Longrightarrow>
       x = CodeElm (vctx_pc x1, Storage SSTORE)"
apply (auto simp add:inst_size_def inst_code.simps)
apply (auto simp add:contexts_as_set_def variable_ctx_as_set_def constant_ctx_as_set_def
      stack_as_set_def memory_as_set_def
      balance_as_set_def storage_as_set_def log_as_set_def program_as_set_def data_sent_as_set_def
      ext_program_as_set_def account_existence_def vctx_advance_pc_def)
  by presburger


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


lemma sload_gas_triple :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle>
           ** block_number_pred bn ** stack_height (h + 1)
           ** stack h idx
           ** program_counter k ** storage idx w ** gas_pred g ** continuing)
          {(k, Storage SLOAD)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h w
           ** program_counter (k + 1) ** storage idx w ** gas_pred (g - Gsload net) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(rule  Set.equalityI; clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; simp)
 apply(rename_tac pair)
 apply(case_tac pair; auto)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; simp)
apply(rename_tac pair)
apply(case_tac pair; auto)
done

end

end

end
