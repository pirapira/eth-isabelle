theory HoareTripleForInstructions2

imports Main "./HoareTripleForInstructions"

begin

lemma add_gas_triple : 
   "triple {OutOfGas} 
      (\<langle> h \<le> 1023\<rangle> **
       stack_height (h + 2) **
       stack (h + 1) v **
       stack h w **
       program_counter k **
       gas_pred g **
       continuing
      )

      {(k, Arith ADD)}

      (stack_height (h + 1) **
       stack h (v + w) **
       program_counter (k + 1) **
       gas_pred (g - Gverylow) **
       continuing
      )"
apply(simp add: triple_def)
apply(clarify)
apply(rule_tac x = "1" in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
done



lemma add_instance : "triple {} (\<langle> (h + 1) \<le> 1023 \<and> g \<ge> Gverylow \<rangle> **
                            stack_height ((h + 1) + 2) **
                            stack ((h + 1) + 1) x **
                            stack (h + 1) v **
                            program_counter k **
                            gas_pred g **
                            continuing
                           )
                           ({(k, Arith ADD)})
                           (stack_height ((h + 1) + 1) **
                            stack (h + 1) (x + v) **
                            program_counter (k + 1) **
                            gas_pred (g - Gverylow) **
                            continuing
                            )"
apply(rule add_triple)
done

lemma add_extended : "triple {} ((\<langle> (h + 1) \<le> 1023 \<and> g \<ge> Gverylow \<rangle> **
                            stack_height ((h + 1) + 2) **
                            stack ((h + 1) + 1) x **
                            stack (h + 1) v **
                            program_counter k **
                            gas_pred g **
                            continuing)
                            ** stack h w
                           )
                           ({(k, Arith ADD)})
                           ((stack_height ((h + 1) + 1) **
                            stack (h + 1) (x + v) **
                            program_counter (k + 1) **
                            gas_pred (g - Gverylow) **
                            continuing)
                            ** stack h w
                            )"
apply(rule frame)
apply(rule add_instance)
done


lemma addadd_triple :
  "triple {} (\<langle> h \<le> 1022 \<and> g \<ge> 2 * Gverylow \<rangle> **
              stack_height (Suc (Suc (Suc h))) **
              stack (h + 2) x **
              stack (h + 1) v **
              stack h w **
              program_counter k **
              gas_pred g **
              continuing
             )
             ({(k, Arith ADD)} \<union> {(k + 1, Arith ADD)})
             (stack_height (h + 1) **
              stack h (x + v + w) **
              program_counter (2 + k) **
              gas_pred (g - 2 * Gverylow) **
              continuing
             )"
(* here the pure condition should be moved out *)
apply(auto)
apply(rule_tac cL = "{(k, Arith ADD)}" and cR = "{(k + 1, Arith ADD)}" in composition)
  apply(simp)
  apply(rule_tac r = "stack h w" in frame_backward)
   apply(rule_tac h = "h + 1" and g = g and v = x and w = v and k = k in add_triple)
  apply(simp)
  apply(rule pred_equiv_R_pure)
   apply (simp add: Gverylow_def)
  using pred_equiv_sep_comm pred_equiv_R_assoc apply blast
 defer
 apply(rule postW)
 apply(rule_tac h = h and v = "x + v" and w = w and k = "k + 1" and g = "g - Gverylow" in add_triple)
 apply(auto)
apply(rule pred_equiv_L_pure)
 apply(simp)
using pred_equiv_sep_comm pred_equiv_R_assoc by blast


lemma pop1 [simp] :
"
vctx_stack x1 = v # t \<Longrightarrow>
(insert (GasElm (vctx_gas x1 - Gbase))
              (insert (ContinuingElm True)
                (insert (StackHeightElm (length t))
                  (insert (PcElm (vctx_pc x1 + 1)) (contexts_as_set x1 co_ctx) - {PcElm (vctx_pc x1)} -
                   insert (StackHeightElm (Suc (length t))) {StackElm (idx, (rev t @ [v]) ! idx) |idx. idx < Suc (length t)} \<union>
                   {StackElm (idx, rev t ! idx) |idx. idx < length t}) -
                 {GasElm (vctx_gas x1)})) -
             {StackHeightElm (length t)} -
             {PcElm (vctx_pc x1 + 1)} -
             {GasElm (vctx_gas x1 - Gbase)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Stack POP)}) =
 (insert (ContinuingElm True) (contexts_as_set x1 co_ctx) - {StackHeightElm (Suc (length t))} -
             {StackElm (length t, v)} -
             {PcElm (vctx_pc x1)} -
             {GasElm (vctx_gas x1)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Stack POP)})
"
apply(auto)
done

lemma pop_triple : "triple {} (\<langle> h \<le> 1024 \<and> g \<ge> Gbase \<rangle> **
                            stack_height (h + 1) **
                            stack h v **
                            program_counter k **
                            gas_pred g **
                            continuing
                           )
                           {(k, Stack POP)}
                           (stack_height h **
                            program_counter (k + 1) **
                            gas_pred (g - Gbase) **
                            continuing
                            )"
apply(simp add: triple_def)
apply(clarify)
apply(rule_tac x = "1" in exI)
apply(case_tac presult; simp)
apply(auto simp add:
      stack_inst_numbers.simps
      pop_def
      instruction_result_as_set_def
      )
apply(auto simp add: stack_as_set_def)
done

declare misc_inst_numbers.simps [simp]
Gzero_def [simp]

lemma stop_gas_triple:
  "triple {OutOfGas}
          (\<langle> h \<le> 1024 \<rangle> ** stack_height h ** program_counter k ** continuing)
          {(k, Misc STOP)}
          (stack_height h ** program_counter k ** not_continuing ** action (ContractReturn []))"
apply(simp add: triple_def)
apply(clarify)
apply(rule_tac x = "1" in exI)
apply(clarify)
apply(case_tac presult; auto simp add: stop_def not_continuing_def action_def
      instruction_result_as_set_def stack_as_set_def ext_program_as_set_def)
   apply(split if_splits; auto)
  apply(rule leibniz)
   apply blast
  apply(auto)
 apply(split if_splits; auto)
apply(rule leibniz)
 apply blast
apply(auto)
done


lemma caller0 [simp] :
" program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Info CALLER) \<Longrightarrow>
  (insert (GasElm (vctx_gas x1 - Gbase))
              (insert (ContinuingElm True)
                (contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx - stack_as_set (vctx_stack x1) \<union>
                 stack_as_set (ucast (vctx_caller x1) # vctx_stack x1) -
                 {GasElm (vctx_gas x1)})) -
             {StackHeightElm (Suc (length (vctx_stack x1)))} -
             {StackElm (length (vctx_stack x1), ucast (vctx_caller x1))} -
             {PcElm (vctx_pc x1 + 1)} -
             {CallerElm (vctx_caller x1)} -
             {GasElm (vctx_gas x1 - Gbase)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Info CALLER)}) =
 (insert (ContinuingElm True) (contexts_as_set x1 co_ctx) - {StackHeightElm (length (vctx_stack x1))} -
             {PcElm (vctx_pc x1)} -
             {CallerElm (vctx_caller x1)} -
             {GasElm (vctx_gas x1)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Info CALLER)})
"
apply(auto)
    apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
  apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
 apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
done

lemma caller_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<rangle> ** stack_height h ** program_counter k ** caller c ** gas_pred g ** continuing)
          {(k, Info CALLER)}
          (stack_height (h + 1) ** stack h (ucast c)
           ** program_counter (k + 1) ** caller c ** gas_pred (g - Gbase) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: stack_0_1_op_def instruction_result_as_set_def)
done


end