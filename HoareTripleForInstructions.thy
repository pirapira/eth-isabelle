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
apply(case_tac "vctx_next_instruction x1 co_ctx"; auto)
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
 "StackElm x2 \<notin> program_as_set (cctx_program co_ctx) = True"
apply(simp add: program_as_set_def)
done

lemma stack_elm_not_constant [simp] :
   "StackElm x2 \<notin> constant_ctx_as_set co_ctx = True"
apply(simp add: constant_ctx_as_set_def)
done

lemma storage_elm_not_constant [simp] :
   "StorageElm x \<notin> constant_ctx_as_set c = True"
apply(simp add: constant_ctx_as_set_def)
apply(simp add: program_as_set_def)
done

lemma memory_elm_not_constant [simp] :
  "MemoryElm m \<notin> constant_ctx_as_set c = True"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

value "(vctx_pc (vctx_advance_pc co_ctx v))"

lemma fst_pair [simp] : "fst (a, b) = a"
apply(simp add: fst_def)
done

lemma rev_append [simp] :
  "(rev l ! a \<noteq> (rev l @ l') ! a) =
   ((a \<ge> length l) \<and> (rev l) ! a \<noteq> l' ! (a - length l))"
apply(simp add: nth_append)
done

lemma over_one [simp]:
 "length lst = a \<Longrightarrow> (rev lst @ [v]) ! a = v"
apply(simp add: nth_append)
done

lemma advance_pc_preserves_storage [simp] :
 "vctx_storage (vctx_advance_pc co_ctx x1) = vctx_storage x1"
apply(simp add: vctx_advance_pc_def)
apply(case_tac "vctx_next_instruction x1 co_ctx"; auto)
done

lemma advance_pc_preserves_memory [simp] :
  "vctx_memory (vctx_advance_pc co_ctx x1) = vctx_memory x1"
apply(simp add: vctx_advance_pc_def)
apply(case_tac "vctx_next_instruction x1 co_ctx"; auto)
done

lemma advance_pc_preserves_logs [simp] :
  "vctx_logs (vctx_advance_pc co_ctx x1) = vctx_logs x1"
apply(simp add: vctx_advance_pc_def)
apply(case_tac "vctx_next_instruction x1 co_ctx"; auto)
done


lemma stack_touching_operations_leaves [simp] :
"(contexts_as_set
              (vctx_advance_pc co_ctx x1\<lparr>vctx_stack := (v + w) # (vctx_stack x1), vctx_gas := vctx_gas x1 - Gverylow\<rparr>) co_ctx -
             {StackHeightElm (Suc (length (vctx_stack x1)))} -
             {StackElm (length (vctx_stack x1), v + w)} -
             {PcElm (vctx_pc x1 + 1)} -
             {GasElm (vctx_gas x1 - Gverylow)} -
             {CodeElm (vctx_pc x1, Arith ADD)})
=
 (contexts_as_set x1 co_ctx - {StackHeightElm (Suc (Suc (length (vctx_stack x1))))} - {StackElm (Suc (length (vctx_stack x1)), v)} -
             {StackElm (length (vctx_stack x1), w)} -
             {PcElm (vctx_pc x1)} -
             {GasElm (vctx_gas x1)} -
             {CodeElm (vctx_pc x1, Arith ADD)})
"
apply(simp add: contexts_as_set_def Set.Un_Diff)
apply(auto)
 apply(rename_tac elm)
 apply(case_tac elm; auto)

oops


lemma add_triple : "triple (\<langle> h \<le> 1023 \<and> g \<ge> Gverylow \<rangle> **
                            stack_height (h + 2) **
                            stack (h + 1) v **
                            stack h w **
                            program_counter k **
                            gas_pred g
                           )
                           {(k, Arith ADD)}
                           (stack_height (h + 1) **
                            stack h (v + w) **
                            program_counter (k + 1) **
                            gas_pred (g - Gverylow)
                            )"
apply(auto simp add: triple_def)
apply(rule_tac x = "1" in exI)
apply(case_tac presult; simp)
apply(auto simp add: program_sem.simps vctx_next_instruction_def instruction_sem_def check_resources_def
      inst_stack_numbers.simps arith_inst_numbers.simps predict_gas_def C_def Cmem_def
      Gmemory_def new_memory_consumption.simps thirdComponentOfC.simps
      vctx_next_instruction_default_def stack_2_1_op_def subtract_gas.simps)



(*

apply(case_tac "vctx_stack x1"; simp)
apply(case_tac list; simp)
apply(auto simp add: subtract_gas.simps strict_if_def program_sem.simps
      vctx_advance_pc_def vctx_next_instruction_def inst_size_def inst_code.simps                                                                               
      contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def stack_as_set_def
      program_as_set_def)
apply(simp add: insert_Diff_if)
apply(rule pred_functional)
 apply(simp)

apply(rule insert_functional; blast?)
apply(rule insert_functional; blast?)
apply(rule insert_functional; blast?)
apply(rule insert_functional; blast?)
apply(rule insert_functional; blast?)
apply(rule insert_functional; blast?)
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(drule disjE; simp)
 apply(drule disjE; simp?)
  apply(blast)
 apply(drule disjE; simp?)
  defer
  apply(clarify)
  apply(simp)
  apply(case_tac "idx \<ge> length lista"; simp)
  apply(case_tac "idx = Suc (length lista)"; simp)
 apply(clarify)
 apply(simp)
 apply(drule disjE; simp?)
  apply(drule disjE; simp?)
   apply(blast)
  apply(drule disjE; simp?)
   defer
   apply(clarify)
   apply(simp)
   apply(case_tac "idx = (length lista)"; simp)
  apply(drule disjE; simp?)
   apply(blast)
  apply(drule disjE; simp?)
 apply(clarify)
 apply(simp)
apply(clarify)
apply(simp)
done

*)
end (* context *)

end
