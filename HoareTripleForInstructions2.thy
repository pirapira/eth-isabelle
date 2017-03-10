theory HoareTripleForInstructions2

imports Main "./HoareTripleForInstructions"
"./HoareTripleForStorage"

begin

lemma "reverse_lookup" [simp] :
  "n < length lst \<Longrightarrow>
   rev lst ! (length lst - Suc n) = lst ! n
  "
  using nth_rev_alt by fastforce

lemma deep_lookup [simp] :
  "w = rev (vctx_stack x1) ! (length (vctx_stack x1) - Suc (unat n)) \<Longrightarrow>
   unat n < length (vctx_stack x1) \<Longrightarrow>
   index (vctx_stack x1) (unat n) = Some w"
apply(simp)
done

lemma dup_advance [simp] :
"      program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Dup n) \<Longrightarrow>
       k = vctx_pc x1 \<Longrightarrow>
       vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1
"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps)
done

lemma dup_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1023 \<and> unat n < h \<rangle> **
                       stack_height h **
                       stack (h - (unat n) - 1) w **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Dup n)}
                      (stack_height (h + 1) **
                       stack (h - (unat n) - 1) w **
                       stack h w **
                       program_counter (k + 1) **
                       gas_pred (g - Gverylow) **
                       continuing
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm; case_tac elm; simp)
apply(clarify)
apply(simp)
apply(rename_tac elm; case_tac elm; simp)
apply(auto)
done


lemma address_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<rangle> ** stack_height h ** program_counter k ** this_account t ** gas_pred g ** continuing)
          {(k, Info ADDRESS)}
          (stack_height (h + 1) ** stack h (ucast t)
           ** program_counter (k + 1) ** this_account t ** gas_pred (g - Gbase) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm; case_tac elm; simp)
apply(clarify)
apply(simp)
apply(rename_tac elm; case_tac elm; simp)
apply(auto)
done


lemma push_advance [simp] :
"      vctx_pc x1 = k \<Longrightarrow>
       lst \<noteq> [] \<Longrightarrow>
       length lst \<le> 32 \<Longrightarrow>
       program_content (cctx_program co_ctx) k = Some (Stack (PUSH_N lst)) \<Longrightarrow>
       vctx_pc (vctx_advance_pc co_ctx x1) = k + 1 + (int (length lst))"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps stack_inst_code.simps)
done



lemma push_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1023 \<and> length lst > 0 \<and> 32 \<ge> length lst\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N lst))}
                      (stack_height (h + 1) **
                       stack h (word_rcat lst) **
                       program_counter (k + 1 + (int (length lst))) **
                       gas_pred (g - Gverylow) **
                       continuing
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; simp add: instruction_result_as_set_def constant_mark_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm; case_tac elm; simp)
apply(clarify)
apply(simp)
apply(rename_tac elm; case_tac elm; simp)
apply(auto)
done


lemma jumpi_size [simp] :
  "inst_size (Pc JUMPI) = 1"
apply(simp add: inst_size_def inst_code.simps)
done

lemma jumpi_false_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<rangle> **
                       stack_height (h + 2) **
                       stack (h + 1) d **
                       stack h 0 **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Pc JUMPI)}
                      (stack_height h **
                       program_counter (k + 1) **
                       gas_pred (g - Ghigh) **
                       continuing)"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(simp add: instruction_result_as_set_def)
apply(case_tac presult; auto simp add: instruction_result_as_set_def vctx_advance_pc_def)
apply(rule leibniz)
 apply blast
apply(auto)
apply(auto simp add: stack_as_set_def)
done

lemma jumpi_true_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<and> cond \<noteq> 0 \<rangle> **
                       stack_height (h + 2) **
                       stack (h + 1) d **
                       stack h cond **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Pc JUMPI), ((uint d), Pc JUMPDEST)}
                      (stack_height h **
                       program_counter (uint d) **
                       gas_pred (g - Ghigh) **
                       continuing
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(simp add: instruction_result_as_set_def)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(auto)
apply(auto simp add: stack_as_set_def)
done


lemma jump_gas_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1023 \<rangle> **
                       stack_height (h + 1) **
                       stack h d **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Pc JUMP), ((uint d), Pc JUMPDEST)}
                      (stack_height h **
                       program_counter (uint d) **
                       gas_pred (g - Gmid) **
                       continuing
                      )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(auto)
apply(auto simp add: stack_as_set_def)
done

declare jump_def [simp del]


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

lemma notin_diff [simp] :
  "x \<notin> A - B =
   (x \<notin> A \<or> x \<in> B)"
  by blast

lemma stack_elm_append [dest] :
  "x = StackElm (idx, lst ! idx) \<Longrightarrow>
   x \<in> contexts_as_set x1 co_ctx \<Longrightarrow>
   (idx < length (vctx_stack x1) \<and> rev (vctx_stack x1) ! idx = lst ! idx)"
apply(simp add: contexts_as_set_def)
done

lemma not_appended [dest] :
  "(rev ta @ [cond, d]) ! aa \<noteq> cond \<Longrightarrow>
   aa \<noteq> length ta
  "
apply(auto)
done

lemma not_first [simp] :
  "((cond # lst) ! n \<noteq> cond) = ((n \<noteq> 0) \<and> lst ! (n - 1) \<noteq> cond)"
apply(case_tac n; auto)
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
 apply(auto simp add: stack_as_set_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm; case_tac elm; simp)
 apply(rename_tac pair; case_tac pair; simp)
 apply(auto)
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
   vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps)
done

lemma storage_continue [simp] :
  "StorageElm x3
       \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
   (StorageElm x3 \<in> variable_ctx_as_set x1)"
apply(simp add: instruction_result_as_set_def)
done

lemma memory_continue [simp] :
  "MemoryElm x4
       \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
   (MemoryElm x4 \<in> variable_ctx_as_set x1)"
apply(simp only: instruction_result_as_set_def)
apply(simp)
done

lemma union_cong :
  "a = b \<Longrightarrow> c = d \<Longrightarrow> a \<union> c = b \<union> d"
apply(simp)
done

lemma contract_action_not_vctx [simp] :
  "ContractActionElm x19 \<notin> variable_ctx_as_set x1"
apply(simp add: variable_ctx_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma continuing_not_vctx [simp] :
  "ContinuingElm b \<notin> variable_ctx_as_set v"
apply(simp add: variable_ctx_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma vctx_gas_changed [simp] :
   "variable_ctx_as_set
             (v \<lparr> vctx_gas := g \<rparr>) =
    variable_ctx_as_set v - { GasElm (vctx_gas v)} \<union> { GasElm g }"
apply(simp)
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; simp)
apply(clarify)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; simp)
apply(auto)
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
apply(clarify)
apply(rule leibniz)
 apply blast
apply(simp add: instruction_result_as_set_def contexts_as_set_def)
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm; case_tac elm; simp)
apply(clarify)
apply(simp)
apply(rename_tac elm; case_tac elm; simp)
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
apply(case_tac presult; simp)
apply(case_tac "vctx_stack x1"; simp)
apply(rule leibniz)
 apply blast
apply(simp add: instruction_result_as_set_def)
apply(rule Set.equalityI)
 apply(clarsimp)
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac x2; simp)
 apply(case_tac "aa = length list"; simp)
apply(clarsimp)
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac " fst x2 < Suc (length list)"; auto)
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
 apply(simp add: instruction_result_as_set_def)
 apply(case_tac presult; auto simp add: failed_for_reasons_def
       instruction_result_as_set_def)
 apply(rule leibniz)
  apply blast
 apply(rule Set.equalityI)
  apply(clarsimp)
  apply(rename_tac elm; case_tac elm; simp)
  apply(case_tac "fst x2 < length ta"; simp)
 apply(clarsimp)
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length ta"; simp)
 apply(case_tac "rev ta ! fst x2 = snd x2 "; simp)
 apply(auto)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: failed_for_reasons_def
      instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarsimp)
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length ta"; simp)
apply(clarsimp)
apply(rename_tac elm; case_tac elm; simp)
apply(case_tac "fst x2 < Suc (Suc (length ta))"; simp)
apply auto
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
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarsimp)
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length ta"; simp)
apply(clarsimp)
apply(rename_tac elm; case_tac elm; simp)
apply auto
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
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarsimp)
 apply(rename_tac elm; case_tac elm; simp)
 apply(case_tac "fst x2 < length ta"; simp)
apply(clarsimp)
apply(rename_tac elm; case_tac elm; auto)

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

(*
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
 defer
 apply(rule weaken_post)
 apply(rule_tac h = h and v = "x + v" and w = w and k = "k + 1" and g = "g - Gverylow" in add_triple)
 apply(auto)
apply(rule weaken_post)
 apply(rule strengthen_pre)
oops
*)

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
      instruction_result_as_set_def
      )
apply(auto simp add: stack_as_set_def)
apply(rule leibniz)
 apply blast
apply(auto)
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
done

lemma caller_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<rangle> ** stack_height h ** program_counter k ** caller c ** gas_pred g ** continuing)
          {(k, Info CALLER)}
          (stack_height (h + 1) ** stack h (ucast c)
           ** program_counter (k + 1) ** caller c ** gas_pred (g - Gbase) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply(auto)
  apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
 apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
apply(rename_tac elm; case_tac elm; auto simp add: stack_as_set_def)
done


end
