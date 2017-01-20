theory HoareTripleForInstructions2

imports Main "./HoareTripleForInstructions"

begin

lemma invalid_jump [simp] :
      "program_content (cctx_program co_ctx) (uint d) = Some i \<Longrightarrow>
       i \<noteq> Pc JUMPDEST \<Longrightarrow>
       g = vctx_gas v \<Longrightarrow>
       vctx_stack v = d # t \<Longrightarrow>
       jump v co_ctx = instruction_failure_result v [InvalidJumpDestination]"
apply(simp add: jump_def)
apply(case_tac i; simp)
apply(rename_tac j; case_tac j; simp)
done

lemma invalid_jump2 [simp] :
      "program_content (cctx_program co_ctx) (uint d) = None \<Longrightarrow>
       g = vctx_gas v \<Longrightarrow>
       vctx_stack v = d # t \<Longrightarrow>
       jump v co_ctx = instruction_failure_result v [InvalidJumpDestination]"
apply(simp add: jump_def)
done


lemma not_continuing_sep [simp] :
  "(not_continuing ** rest) s =
   (ContinuingElm False \<in> s \<and> rest (s - {ContinuingElm False}))"
apply(auto simp add: sep_def not_continuing_def)
done

lemma action_sep [simp] :
  "(action a ** rest) s =
   (ContractActionElm a \<in> s \<and> rest (s - {ContractActionElm a}))"
apply(auto simp add: action_def sep_def)
done

lemma invalid_jumpi_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<and> cond \<noteq> 0 \<and> i \<noteq> Pc JUMPDEST \<rangle> **
                       stack_height (h + 2) **
                       stack (h + 1) d **
                       stack h cond **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Pc JUMPI), ((uint d), i)}
                      (stack_height (h + 1) **
                       stack h d **
                       program_counter k **
                       gas_pred (g - Ghigh) **
                       not_continuing **
                       action (ContractFail [InvalidJumpDestination])
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
 apply(rule leibniz)
  apply blast
 apply(auto)
  apply(simp add: stack_as_set_def)
  apply(clarify)
  apply(case_tac "idx = Suc (length ta)"; auto)
 apply(simp add: stack_as_set_def)
 apply(clarify)
 apply(case_tac "idx = Suc (length ta)"; auto)
apply(rule leibniz)
 apply blast
apply(auto)
 apply(simp add: stack_as_set_def)
 apply(clarify)
 apply(case_tac "idx = Suc (length ta)"; simp)
apply(simp add: stack_as_set_def)
apply(clarify)
apply(case_tac "idx = Suc (length ta)"; simp)
done


lemma invalid_jump_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1023 \<and> i \<noteq> Pc JUMPDEST\<rangle> **
                       stack_height (h + 1) **
                       stack h d **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Pc JUMP), ((uint d), i)}
                      (stack_height (h + 1) **
                       stack h d **
                       program_counter k **
                       gas_pred (g - Gmid) **
                       not_continuing **
                       action (ContractFail [InvalidJumpDestination])
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
 apply(rule leibniz)
  apply blast
 apply(auto)
apply(rule leibniz)
 apply blast
apply auto
done

lemma jumpdest_advance [simp] :
  "k = vctx_pc x1 \<Longrightarrow>
   program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Pc JUMPDEST) \<Longrightarrow>
   vctx_pc x1 + 1 = vctx_pc (vctx_advance_pc co_ctx x1)"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps)
done

lemma jumpdest_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1024 \<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Pc JUMPDEST)}
                      (stack_height h **
                       program_counter (k + 1) **
                       gas_pred (g - Gjumpdest) **
                       continuing
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; simp)
  apply(rule leibniz)
   apply blast
  apply(rule Set.equalityI) (* why is the following so complicated? *)
   apply(simp add: Set.subset_eq)
   apply(clarify)
   apply(rename_tac elm)
   apply(case_tac elm; simp add: instruction_result_as_set_def)
  apply(simp add: Set.subset_eq)
  apply(simp add: instruction_result_as_set_def)
  apply(clarify)
  apply(rename_tac elm)
  apply(case_tac elm; clarify?; simp?)
 apply(simp add: instruction_result_as_set_def)
apply(simp add: instruction_result_as_set_def)
done

lemma pop_gas_triple : "triple {OutOfGas} (\<langle> h \<le> 1024 \<rangle> **
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
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; simp)
  apply(case_tac "vctx_stack x1"; simp)
  apply(rule leibniz)
   apply blast
  apply(auto simp add: instruction_result_as_set_def)
 apply(auto simp add: stack_as_set_def)
done

lemma balance_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000\<rangle>
           ** block_number_pred bn ** stack_height (h + 1) ** stack h a
           ** program_counter k ** balance (ucast a) b ** gas_pred g ** continuing)
          {(k, Info BALANCE)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h b
           ** program_counter (k + 1) ** balance (ucast a) b ** gas_pred (g - 400) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(simp)
apply(case_tac presult)
  apply(simp)
  apply(case_tac "vctx_stack x1"; simp)
 apply(simp add: instruction_result_as_set_def)
apply(simp add: instruction_result_as_set_def)
done


lemma eq0 [simp]: "
       vctx_stack x1 = v # w # ta \<Longrightarrow>
program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Arith inst_EQ) \<Longrightarrow>
 (insert (GasElm (vctx_gas x1 - Gverylow))
              (insert (ContinuingElm True)
                (contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx - stack_as_set (v # w # ta) \<union> stack_as_set (r # ta) -
                 {GasElm (vctx_gas x1)})) -
             {StackHeightElm (Suc (length ta))} -
             {StackElm (length ta, r)} -
             {PcElm (vctx_pc x1 + 1)} -
             {GasElm (vctx_gas x1 - Gverylow)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Arith inst_EQ)}) =
 (insert (ContinuingElm True) (contexts_as_set x1 co_ctx) - {StackHeightElm (Suc (Suc (length ta)))} -
             {StackElm (Suc (length ta), v)} -
             {StackElm (length ta, w)} -
             {PcElm (vctx_pc x1)} -
             {GasElm (vctx_gas x1)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Arith inst_EQ)})
"
apply(auto)
   apply(rename_tac elm; case_tac elm; auto)
  apply(rename_tac elm; case_tac elm; auto)
 apply(rename_tac elm; case_tac elm; auto)
apply(rename_tac elm; case_tac elm; auto)
 apply(case_tac "a = Suc (length ta)"; simp)
apply(case_tac "a = length ta"; simp)
done

lemma eq_gas_triple :
  "triple {OutOfGas}  ( \<langle> h \<le> 1023 \<rangle> **
                        stack_height (h + 2) **
                        stack (h + 1) v **
                        stack h w **
                        program_counter k **
                        gas_pred g **
                        continuing
                      )
                      {(k, Arith inst_EQ)}
                      ( stack_height (h + 1) **
                        stack h (if v = w then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word)) **
                        program_counter (k + 1) **
                        gas_pred (g - Gverylow) **
                        continuing )"
apply(auto simp add: triple_def)
 apply(rule_tac x = 1 in exI)
 apply(case_tac presult; auto simp add: failed_for_reasons_def
       instruction_result_as_set_def) (* takes too much time *)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: failed_for_reasons_def
      instruction_result_as_set_def)
done

lemma tmp1 [simp]:
  "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Arith ADD) \<Longrightarrow>
   vctx_stack x1 = v # w # ta \<Longrightarrow>
   (insert (GasElm (vctx_gas x1 - Gverylow))
              (insert (ContinuingElm True)
                (contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx - stack_as_set (v # w # ta) \<union> stack_as_set ((v + w) # ta) -
                 {GasElm (vctx_gas x1)})) -
             {StackHeightElm (Suc (length ta))} -
             {StackElm (length ta, v + w)} -
             {PcElm (vctx_pc x1 + 1)} -
             {GasElm (vctx_gas x1 - Gverylow)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Arith ADD)}) =
  (insert (ContinuingElm True) (contexts_as_set x1 co_ctx) - {StackHeightElm (Suc (Suc (length ta)))} -
             {StackElm (Suc (length ta), v)} -
             {StackElm (length ta, w)} -
             {PcElm (vctx_pc x1)} -
             {GasElm (vctx_gas x1)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Arith ADD)})"
apply(auto)
   apply(rename_tac elm; case_tac elm; auto)
  apply(rename_tac elm; case_tac elm; auto)
 apply(rename_tac elm; case_tac elm; auto)
apply(rename_tac elm; case_tac elm; auto)
 apply(rename_tac l)
 apply(case_tac "l = length ta"; auto)
apply(rename_tac l)
apply(case_tac "l = length ta"; auto)
done

lemma add_triple :
   "triple {}
           (\<langle> h \<le> 1023 \<and> g \<ge> Gverylow \<rangle> **
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