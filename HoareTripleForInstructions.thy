theory HoareTripleForInstructions

imports Main "./Hoare"

begin

(* how to declare [simp] in a limited scope? *)
context

begin

(**
 ** Hoare Triple for each instruction
 **)
 
declare insert_functional [intro]

lemma arith_inst_size_one [simp]:
  "inst_size (Arith a) = 1"
apply(simp add: inst_size_def inst_code.simps)
done

declare data_sent_as_set_def [simp]

lemma caller_elm_means [simp] : "
 (CallerElm x12
           \<in> variable_ctx_as_set v) =
 (x12 = vctx_caller v)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma lst_longer [dest!]:
  "length l = Suc h \<Longrightarrow> \<exists> a t. l = a # t \<and> length t = h"
	by (simp add: length_Suc_conv)

lemma advance_pc_advance [simp]:
  " vctx_next_instruction x1 co_ctx = Some i \<Longrightarrow>
    inst_size i = 1 \<Longrightarrow>
    vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_no_gas_change [simp] :
  "vctx_gas (vctx_advance_pc co_ctx x1) = vctx_gas x1"
apply(simp add: vctx_advance_pc_def)
done

lemma constant_diff_stack_height [simp] :
 "constant_ctx_as_set co_ctx - {StackHeightElm h} = constant_ctx_as_set co_ctx"
apply(auto simp add: constant_ctx_as_set_def)
apply(auto simp add: program_as_set_def)
done

lemma constant_diff_stack [simp] :
 "constant_ctx_as_set co_ctx - {StackElm s} = constant_ctx_as_set co_ctx"
apply(auto simp add: constant_ctx_as_set_def)
apply(auto simp add: program_as_set_def)
done

lemma constant_diff_pc [simp] :
 "constant_ctx_as_set co_ctx - {PcElm p} =
  constant_ctx_as_set co_ctx"
apply(auto simp add: constant_ctx_as_set_def)
apply(auto simp add: program_as_set_def)
done

lemma constant_diff_gas [simp] :
 "constant_ctx_as_set co_ctx - {GasElm g} =
  constant_ctx_as_set co_ctx"
apply(auto simp add: constant_ctx_as_set_def)
apply(auto simp add: program_as_set_def)
done

lemma stack_height_element_means [simp] :
 "(StackHeightElm h \<in> variable_ctx_as_set v) =
  (length (vctx_stack v) = h)
 "
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma stack_element_means [simp] :
 "(StackElm pw \<in> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) = (snd pw) \<and> (fst pw) < length (vctx_stack v))"
apply(case_tac pw)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma stack_element_notin_means [simp] :
 "(StackElm pw \<notin> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) \<noteq> (snd pw) \<or> (fst pw) \<ge> length (vctx_stack v))"
apply(case_tac pw)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done


lemma storage_element_means [simp] :
  "StorageElm idxw \<in> variable_ctx_as_set v =
   (vctx_storage v (fst idxw) = (snd idxw))"
apply(case_tac idxw; simp)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma memory_element_means [simp] :
  "MemoryElm addrw \<in> variable_ctx_as_set v =
   (vctx_memory v (fst addrw) = snd addrw)"
apply(case_tac addrw; simp)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done


lemma pc_element_means [simp] :
  "(PcElm p \<in> variable_ctx_as_set v) =
   (vctx_pc v = p)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma gas_element_means [simp] :
  "(GasElm g \<in> variable_ctx_as_set v) =
    (vctx_gas v = g)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma log_element_means [simp] :
  "(LogElm p \<in> variable_ctx_as_set v) =
   (vctx_logs v ! (fst p) = (snd p) \<and> fst p < length (vctx_logs v))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
apply(case_tac p; auto)
done

lemma memory_usage_element_means [simp] :
  "(MemoryUsageElm u \<in> variable_ctx_as_set v) = (vctx_memory_usage v = u)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma code_element_means [simp] :
  "(CodeElm (x, y) \<in> constant_ctx_as_set c) = 
   (program_content (cctx_program c) x = Some y \<or>
    program_content (cctx_program c) x = None \<and>
    y = Misc STOP)"
apply(auto simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma origin_element_means [simp] :
  "(OriginElm orig \<in> variable_ctx_as_set v) = (orig = vctx_origin v)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma sent_value_means [simp] :
  "SentValueElm x14 \<in> variable_ctx_as_set x1 = (x14 = vctx_value_sent x1)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma sent_data_means [simp] :
"SentDataElm p \<in> variable_ctx_as_set x1 = 
 (vctx_data_sent x1 ! (fst p) = (snd p) \<and> (fst p) < (length (vctx_data_sent x1)))"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def)
apply(rule_tac x = "fst p" in exI; simp)
done



lemma sent_data_length_means [simp] :
  "SentDataLengthElm x15 \<in> variable_ctx_as_set x1 = (x15 = length (vctx_data_sent x1))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
done


lemma inst_size_nonzero [simp] : "inst_size a \<noteq> 0"
apply(simp add: inst_size_def)
apply(case_tac a; auto simp add: inst_code.simps dup_inst_code_def)
apply(rename_tac s)
apply(case_tac s; simp add: stack_inst_code.simps)
apply(rename_tac l)
apply(case_tac l; simp)
apply(split if_splits; auto)
done

lemma advance_pc_different [simp] :
  "vctx_pc (vctx_advance_pc co_ctx x1) \<noteq> vctx_pc x1"
apply(simp add: vctx_advance_pc_def)
apply(case_tac "vctx_next_instruction x1 co_ctx"; auto)
done

lemma stack_elm_not_program [simp]:
 "StackElm x2 \<notin> program_as_set (cctx_program co_ctx)"
apply(simp add: program_as_set_def)
done

lemma stack_elm_not_constant [simp] :
   "StackElm x2 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def)
done

lemma storage_elm_not_constant [simp] :
   "StorageElm x \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def)
apply(simp add: program_as_set_def)
done

lemma stack_height_elm_not_constant [simp]:
  "StackHeightElm h \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done


lemma memory_elm_not_constant [simp] :
  "MemoryElm m \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma pc_elm_not_constant [simp] :
"PcElm x \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma gas_elm_not_constant [simp] :
"GasElm x \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma code_elm_not_variable [simp] :
 "CodeElm c \<notin> variable_ctx_as_set v"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma this_account_elm_not_variable [simp] :
  "ThisAccountElm t
           \<notin> variable_ctx_as_set v"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
done

lemma fst_pair [simp] : "fst (a, b) = a"
apply(simp add: fst_def)
done

lemma rev_append [simp] :
  "(rev l ! a \<noteq> (rev l @ l') ! a) =
   ((a \<ge> length l) \<and> (rev l) ! a \<noteq> l' ! (a - length l))"
apply(simp add: nth_append)
done

lemma rev_append_inv [simp] :
  "((rev l @ l') ! a \<noteq> rev l ! a) =
   ((a \<ge> length l) \<and> (rev l) ! a \<noteq> l' ! (a - length l))"
apply(auto simp add: nth_append)
done

lemma rev_rev_append [simp] :
  "((rev l @ a0) ! idx \<noteq> (rev l @ a1) ! idx)
   =
   (idx \<ge> length l \<and> a0 ! (idx - length l) \<noteq> a1 ! (idx - length l))"
apply(auto simp add: nth_append)
done

lemma over_one [simp]:
 "length lst = a \<Longrightarrow> (rev lst @ (v # l)) ! a = v"
apply(simp add: nth_append)
done

lemma over_one_rev [simp] :
  "((rev l @ (w # x)) ! idx \<noteq> w) =
    (idx < (length l) \<and> (rev l) ! idx \<noteq> w ) \<or> ( idx > (length l) \<and> x ! (idx - length l - 1) \<noteq> w)"
apply(simp add: nth_append)
by (simp add: nth_Cons')

lemma over_one_rev' [simp] :
  "((rev l @ [w, v]) ! idx \<noteq> w) =
    (idx < (length l) \<and> (rev l) ! idx \<noteq> w ) \<or> ( idx > (length l) \<and> [v] ! (idx - length l - 1) \<noteq> w)"
apply(auto simp add: nth_append nth_Cons')
done


lemma over_two [simp]:
 "Suc (length lst) = a \<Longrightarrow> (rev lst @ (v # w # l)) ! a = w"
apply(simp add: nth_append)
done

lemma over_two_rev [simp] :
  "((rev l @ (w #  v # x)) ! idx \<noteq> v) =
    (idx \<le> (length l) \<and> (rev l @ [w]) ! idx \<noteq> v ) \<or> ( idx > Suc (length l) \<and> x ! (idx - length l - 2) \<noteq> v )"
apply(simp add: nth_append)
(* sledgehammer *)
by (metis Suc_diff_Suc diff_self_eq_0 less_antisym linorder_neqE_nat nth_Cons_0 nth_Cons_Suc)


lemma advance_pc_preserves_storage [simp] :
 "vctx_storage (vctx_advance_pc co_ctx x1) = vctx_storage x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_memory [simp] :
  "vctx_memory (vctx_advance_pc co_ctx x1) = vctx_memory x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_logs [simp] :
  "vctx_logs (vctx_advance_pc co_ctx x1) = vctx_logs x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_memory_usage [simp] :
  "vctx_memory_usage (vctx_advance_pc co_ctx x1) = vctx_memory_usage x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_balance [simp] :
   "vctx_balance (vctx_advance_pc co_ctx x1) = vctx_balance x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_caller [simp] :
  "vctx_caller (vctx_advance_pc co_ctx x1) = vctx_caller x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preseerves_caller [simp] :
  "vctx_value_sent (vctx_advance_pc co_ctx x1) = vctx_value_sent x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_origin [simp] :
  " vctx_origin (vctx_advance_pc co_ctx x1) = vctx_origin x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_preserves_block [simp] :
  " vctx_block (vctx_advance_pc co_ctx x1) = vctx_block x1"
apply(simp add: vctx_advance_pc_def)
done

lemma balance_elm_means [simp] :
 "BalanceElm p \<in> variable_ctx_as_set v = (vctx_balance v (fst p) = (snd p))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def)
apply(case_tac p; auto)
done

lemma advance_pc_keeps_stack [simp] :
  "(vctx_stack (vctx_advance_pc co_ctx v)) = vctx_stack v"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_change [simp] :
  "vctx_pc x1 \<noteq> vctx_pc (vctx_advance_pc co_ctx x1)"
	by (metis advance_pc_different)



(****** specifying each instruction *******)

declare predict_gas_def [simp]
        C_def [simp] Cmem_def [simp]
        Gmemory_def [simp]
        new_memory_consumption.simps [simp]
        thirdComponentOfC.simps [simp]
        subtract_gas.simps [simp]
        vctx_next_instruction_default_def [simp]
        stack_2_1_op_def [simp]
        inst_stack_numbers.simps [simp]
        arith_inst_numbers.simps [simp]

lemma eq0 [simp]: "
       vctx_stack x1 = v # w # ta \<Longrightarrow>
program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Arith inst_EQ) \<Longrightarrow>
(insert (ContinuingElm True)
              (contexts_as_set (vctx_advance_pc co_ctx x1\<lparr>vctx_stack := r # ta, vctx_gas := vctx_gas x1 - Gverylow\<rparr>) co_ctx) -
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
apply(auto simp add: contexts_as_set_def vctx_advance_pc_def vctx_next_instruction_def)
 apply(rename_tac elm)
 apply(case_tac elm; auto)
 apply(auto simp add: variable_ctx_as_set_def stack_as_set_def) (* takes too much time *)
 apply(case_tac "idx = Suc (length ta)"; simp)
apply(case_tac "idx = length ta"; simp)
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
 apply(case_tac presult; auto simp add: program_sem.simps failed_for_reasons_def vctx_next_instruction_def
       instruction_result_as_set_def instruction_sem_def) (* takes too much time *)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: program_sem.simps failed_for_reasons_def vctx_next_instruction_def
      instruction_result_as_set_def instruction_sem_def)
done

lemma tmp1 [simp]: 
  "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Arith ADD) \<Longrightarrow>
   vctx_stack x1 = v # w # ta \<Longrightarrow>
   (insert (ContinuingElm True)
              (contexts_as_set
                (vctx_advance_pc co_ctx x1
                 \<lparr>vctx_stack := (v + w) # ta, vctx_gas := vctx_gas x1 - Gverylow\<rparr>)
                co_ctx) -
             {StackHeightElm (Suc (length ta))} -
             {StackElm (length ta, v + w)} -
             {PcElm (vctx_pc x1 + 1)} -
             {GasElm (vctx_gas x1 - Gverylow)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Arith ADD)}) =
  (insert (ContinuingElm True) (contexts_as_set x1 co_ctx) -
             {StackHeightElm (Suc (Suc (length ta)))} -
             {StackElm (Suc (length ta), v)} -
             {StackElm (length ta, w)} -
             {PcElm (vctx_pc x1)} -
             {GasElm (vctx_gas x1)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Arith ADD)})"
apply(auto simp add: contexts_as_set_def Set.Un_Diff)
 apply(rename_tac elm)
 apply(case_tac elm; auto simp add: variable_ctx_as_set_def  vctx_advance_pc_def stack_as_set_def vctx_next_instruction_def)
apply(rename_tac elm)
apply(case_tac elm; auto simp add: variable_ctx_as_set_def  vctx_advance_pc_def stack_as_set_def vctx_next_instruction_def)
 apply(case_tac "idx < length ta"; auto)
 apply(case_tac "idx = length ta"; auto)
apply(case_tac "idx < length ta"; auto)
apply(case_tac "idx = length ta"; auto)
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
apply(case_tac presult; auto simp add: program_sem.simps vctx_next_instruction_def instruction_sem_def check_resources_def
      instruction_result_as_set_def)
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
apply(case_tac presult; auto simp add: program_sem.simps vctx_next_instruction_def instruction_sem_def check_resources_def
      instruction_result_as_set_def)
apply(simp add: failed_for_reasons_def)
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

lemma pred_equiv_R_assoc [simp] :
  "pred_equiv a ((b ** c) ** d) = pred_equiv a (b ** c ** d)"
apply(auto)
 apply(rule pred_equiv_trans_other)
  apply(rule pred_equiv_sep_assoc)
 apply(simp)
apply(rule pred_equiv_trans_other)
 apply(rule pred_equiv_symm)
 apply(rule pred_equiv_sep_assoc)
apply(simp)
done

lemma Gverylow_positive [simp]:
  "Gverylow > 0"
apply(simp add: Gverylow_def)
done


lemma pred_equiv_R_pure :
  "b \<Longrightarrow> pred_equiv a c \<Longrightarrow> pred_equiv a (\<langle> b \<rangle> ** c)"
apply(simp add: pred_equiv_def)
done

lemma pred_equiv_L_pure :
  "b \<Longrightarrow> pred_equiv a c \<Longrightarrow> pred_equiv (\<langle> b \<rangle> ** a) c"
apply(simp add: pred_equiv_def)
done


lemma pred_equiv_R_comm :
  "pred_equiv a (c ** d) \<Longrightarrow> pred_equiv a (d ** c)"
apply(simp add: pred_equiv_def)
(* sledgehammer *)
	by (simp add: pred_equiv_sep_comm pred_equiv_sound)


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


lemma saying_zero [simp] :
  "(x - Suc 0 < x) = (x \<noteq> 0)"
apply(case_tac x; auto)
done

lemma inst_size_pop [simp] :
  "inst_size (Stack POP) = 1"
apply(simp add: inst_code.simps inst_size_def stack_inst_code.simps)
done

lemma pop_advance [simp] :
  "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Stack POP) \<Longrightarrow>
   vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def vctx_next_instruction_def)
done


lemma advance_pc_as_set [simp] :
  "program_content (cctx_program co_ctx) (vctx_pc v) = Some (Stack POP) \<Longrightarrow>
   (contexts_as_set (vctx_advance_pc co_ctx v) co_ctx) =
   (contexts_as_set v co_ctx) \<union> {PcElm (vctx_pc v + 1)} - {PcElm (vctx_pc v)}"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def
      vctx_advance_pc_def vctx_next_instruction_def)
done



lemma gas_change_as_set [simp] :
  "(contexts_as_set (x1\<lparr>vctx_gas := new_gas\<rparr>) co_ctx) 
    = ((contexts_as_set x1 co_ctx  - {GasElm (vctx_gas x1) }) \<union> { GasElm new_gas } )"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def)
done

lemma stack_change_as_set [simp] :
   "(contexts_as_set (v\<lparr>vctx_stack := t\<rparr>) co_ctx) =
     (contexts_as_set v co_ctx - stack_as_set (vctx_stack v)) \<union> stack_as_set t 
    "
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def)
done

lemma stack_height_in [simp] :
  "StackHeightElm (length t) \<in> stack_as_set t"
apply(simp add: stack_as_set_def)
done

lemma pc_not_stack [simp] :
 "PcElm k \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done 

lemma code_not_stack [simp] :
  "CodeElm p \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

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
apply(auto simp add: program_sem.simps vctx_next_instruction_def instruction_sem_def check_resources_def
      stack_inst_numbers.simps
      pop_def
      instruction_result_as_set_def
      )
apply(auto simp add: stack_as_set_def)
done

end (* context *)

end
