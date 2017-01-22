theory HoareTripleForInstructions

imports Main "./Hoare"

begin


(**
 ** Hoare Triple for each instruction
 **)
 
declare insert_functional [intro]

lemma continuing_not_context [simp]:
  "ContinuingElm b \<notin> contexts_as_set x32 co_ctx"
apply(simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def program_as_set_def stack_as_set_def
data_sent_as_set_def  ext_program_as_set_def)
done

lemma arith_inst_size_one [simp]:
  "inst_size (Arith a) = 1"
apply(simp add: inst_size_def inst_code.simps)
done

declare data_sent_as_set_def [simp]

lemma caller_elm_means [simp] : "
 (CallerElm x12
           \<in> variable_ctx_as_set v) =
 (x12 = vctx_caller v)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def  ext_program_as_set_def)
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
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma stack_element_means [simp] :
 "(StackElm pw \<in> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) = (snd pw) \<and> (fst pw) < length (vctx_stack v))"
apply(case_tac pw)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def  ext_program_as_set_def)
done

lemma stack_element_notin_means [simp] :
 "(StackElm pw \<notin> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) \<noteq> (snd pw) \<or> (fst pw) \<ge> length (vctx_stack v))"
apply(case_tac pw)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done


lemma storage_element_means [simp] :
  "StorageElm idxw \<in> variable_ctx_as_set v =
   (vctx_storage v (fst idxw) = (snd idxw))"
apply(case_tac idxw; simp)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma memory_element_means [simp] :
  "MemoryElm addrw \<in> variable_ctx_as_set v =
   (vctx_memory v (fst addrw) = snd addrw)"
apply(case_tac addrw; simp)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done


lemma pc_element_means [simp] :
  "(PcElm p \<in> variable_ctx_as_set v) =
   (vctx_pc v = p)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma gas_element_means [simp] :
  "(GasElm g \<in> variable_ctx_as_set v) =
    (vctx_gas v = g)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma log_element_means [simp] :
  "(LogElm p \<in> variable_ctx_as_set v) =
   (vctx_logs v ! (fst p) = (snd p) \<and> fst p < length (vctx_logs v))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
apply(case_tac p; auto)
done

lemma memory_usage_element_means [simp] :
  "(MemoryUsageElm u \<in> variable_ctx_as_set v) = (vctx_memory_usage v = u)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma code_element_means [simp] :
  "(CodeElm xy \<in> constant_ctx_as_set c) = 
   (program_content (cctx_program c) (fst xy) = Some (snd xy) \<or>
    program_content (cctx_program c) (fst xy) = None \<and>
    (snd xy) = Misc STOP)"
apply(case_tac xy; auto simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma origin_element_means [simp] :
  "(OriginElm orig \<in> variable_ctx_as_set v) = (orig = vctx_origin v)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma sent_value_means [simp] :
  "SentValueElm x14 \<in> variable_ctx_as_set x1 = (x14 = vctx_value_sent x1)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma sent_data_means [simp] :
"SentDataElm p \<in> variable_ctx_as_set x1 = 
 (vctx_data_sent x1 ! (fst p) = (snd p) \<and> (fst p) < (length (vctx_data_sent x1)))"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def  ext_program_as_set_def)
apply(rule_tac x = "fst p" in exI; simp)
done



lemma sent_data_length_means [simp] :
  "SentDataLengthElm x15 \<in> variable_ctx_as_set x1 = (x15 = length (vctx_data_sent x1))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma this_account_elm_not_variable [simp] :
  "ThisAccountElm t
           \<notin> variable_ctx_as_set v"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
apply(case_tac p; auto)
done

lemma advance_pc_keeps_stack [simp] :
  "(vctx_stack (vctx_advance_pc co_ctx v)) = vctx_stack v"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_change [simp] :
  "vctx_pc x1 \<noteq> vctx_pc (vctx_advance_pc co_ctx x1)"
	by (metis advance_pc_different)

lemma caller_sep [simp]:
  "(caller c ** rest) s =
   (CallerElm c \<in> s \<and> rest (s - {CallerElm c}))"
apply(auto simp add: caller_def sep_def)
done

lemma balance_sep [simp] :
  "(balance a b ** rest) s =
   (BalanceElm (a, b) \<in> s \<and> rest (s - {BalanceElm (a, b)}))"
apply(auto simp add: balance_def sep_def)
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
      vctx_advance_pc_def vctx_next_instruction_def ext_program_as_set_def)
done



lemma gas_change_as_set [simp] :
  "(contexts_as_set (x1\<lparr>vctx_gas := new_gas\<rparr>) co_ctx) 
    = ((contexts_as_set x1 co_ctx  - {GasElm (vctx_gas x1) }) \<union> { GasElm new_gas } )"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma stack_change_as_set [simp] :
   "(contexts_as_set (v\<lparr>vctx_stack := t\<rparr>) co_ctx) =
     (contexts_as_set v co_ctx - stack_as_set (vctx_stack v)) \<union> stack_as_set t 
    "
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
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

lemma action_not_context [simp]:
  "ContractActionElm a \<notin> contexts_as_set x1 co_ctx"
apply(simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def stack_as_set_def
      program_as_set_def ext_program_as_set_def)
done

lemma failed_is_failed [simp]:
   "failed_for_reasons {OutOfGas} (InstructionToEnvironment (ContractFail [OutOfGas]) a b)"
apply(simp add: failed_for_reasons_def)
done

lemma stack_height_increment [simp]:
  "StackHeightElm (Suc (length lst)) \<in> stack_as_set (x # lst)"
apply(simp add: stack_as_set_def)
done

lemma stack_inc_element [simp] :
   "StackElm (length lst, elm)
     \<in> stack_as_set (elm # lst)"
apply(simp add: stack_as_set_def)
done

lemma caller_elm_means_c [simp] :
  "(CallerElm c \<in> contexts_as_set x1 co_ctx) = (vctx_caller x1 = c)"
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def program_as_set_def)
done

lemma continue_not_failed [simp] :
  "\<not> failed_for_reasons {OutOfGas}
           (InstructionContinue v)"
apply(simp add: failed_for_reasons_def)
done

lemma info_single_advance [simp] :
  "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Info i) \<Longrightarrow>
   vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def vctx_next_instruction_def inst_size_def
      inst_code.simps)
done

lemma caller_not_stack [simp]:
  "CallerElm c \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma advance_keeps_storage_elm [simp] :
  "StorageElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (StorageElm ab \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_memory_elm [simp] :
"MemoryElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
 = (MemoryElm ab \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_log_elm [simp] :
"LogElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
 (LogElm ab \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_memory_usage_elm [simp] :
  "MemoryUsageElm x8 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (MemoryUsageElm x8 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_this_account_elm [simp] :
  "ThisAccountElm x10 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (ThisAccountElm x10 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_balance_elm [simp] :
  "BalanceElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (BalanceElm ab \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_origin_elm [simp] :
  "OriginElm x13 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (OriginElm x13 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_sent_value_elm [simp] :
  "SentValueElm x14 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (SentValueElm x14 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma sent_data_length_not_constant [simp] :
  "SentDataLengthElm x15 \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma data_sent_advance_pc [simp] :
  "vctx_data_sent (vctx_advance_pc co_ctx x1) = vctx_data_sent x1"
apply(simp add: vctx_advance_pc_def)
done


lemma advance_keeps_sent_data_length_elm [simp] :
  "SentDataLengthElm x15 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (SentDataLengthElm x15 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_sent_data_elm [simp] :
  "SentDataElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (SentDataElm ab \<in> contexts_as_set x1 co_ctx)
  "
apply(simp add: contexts_as_set_def)
done

lemma ext_program_size_not_constant [simp] :
  "ExtProgramSizeElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma ext_program_size_elm_means [simp] :
   "ExtProgramSizeElm ab \<in> variable_ctx_as_set v =
    (program_length (vctx_ext_program v (fst ab)) = snd ab)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
apply(case_tac ab; auto)
done

lemma ext_program_size_c_means [simp] :
  "ExtProgramSizeElm ab \<in> contexts_as_set v co_ctx =
   (program_length (vctx_ext_program v (fst ab)) = snd ab)"
apply(simp add: contexts_as_set_def)
done

lemma ext_program_advance_pc [simp] :
  " vctx_ext_program (vctx_advance_pc co_ctx x1)
  = vctx_ext_program x1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_keeps_ext_program_size_elm [simp] :
  "ExtProgramSizeElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (ExtProgramSizeElm ab \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def)
done

lemma ext_program_elm_not_constant [simp] :
   "ExtProgramElm abc \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma ext_program_elm_means [simp] :
  "ExtProgramElm abc \<in> variable_ctx_as_set v =
   (program_as_natural_map ((vctx_ext_program v) (fst abc)) (fst (snd abc)) = (snd (snd abc)))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
apply(case_tac abc; auto)
done

lemma ext_program_c_means [simp] :
  "ExtProgramElm abc \<in> contexts_as_set v co_ctx =
   (program_as_natural_map ((vctx_ext_program v) (fst abc)) (fst (snd abc)) = (snd (snd abc)))"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_ext_program_elm [simp] :
  "ExtProgramElm abc \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
= (ExtProgramElm abc \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma blockhash_not_constant [simp] :
  "BlockhashElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma blockhash_elm_means [simp] :
  "BlockhashElm ab \<in> variable_ctx_as_set x1 =
   (block_blockhash (vctx_block x1) (fst ab) = snd ab)"
apply(simp add: variable_ctx_as_set_def ext_program_as_set_def stack_as_set_def)
apply(case_tac ab; auto)
done

lemma blockhash_c_means [simp] :
  "BlockhashElm ab \<in> contexts_as_set x1 co_ctx =
   (block_blockhash (vctx_block x1) (fst ab) = snd ab)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_blockhash_elm [simp] :
  "BlockhashElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (BlockhashElm ab \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma coinbase_elm_not_constant [simp] :
"CoinbaseElm x22 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma coinbase_elm_means [simp] :
  "CoinbaseElm x22 \<in> variable_ctx_as_set x2 =
   ((block_coinbase (vctx_block x2)) = x22)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma coinbase_c_means [simp] :
  "CoinbaseElm x23 \<in> contexts_as_set x1 co_ctx =
  (block_coinbase (vctx_block x1) = x23)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_conbase_elm [simp] :
  "CoinbaseElm x22 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (CoinbaseElm x22 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma timestamp_not_constant [simp] :
  "TimestampElm t \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma timestamp_elm_means [simp] :
  "TimestampElm t \<in> variable_ctx_as_set x1 =
   (t = block_timestamp (vctx_block x1))"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma timestamp_c_means [simp] :
 "TimestampElm t \<in> contexts_as_set x1 co_ctx =
   (t = block_timestamp (vctx_block x1))"
apply(simp add: contexts_as_set_def)
done


lemma advance_keeps_timestamp_elm [simp] :
  "TimestampElm t \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
  = (TimestampElm t \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma difficulty_not_constant [simp] :
  "DifficultyElm x24 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma difficulty_elm_means [simp] :
  "DifficultyElm x24 \<in> variable_ctx_as_set x1 =
   (x24 = block_difficulty (vctx_block x1))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma difficulty_c_means [simp] :
  "DifficultyElm x24 \<in> contexts_as_set x1 co_ctx =
   (x24 = block_difficulty (vctx_block x1))"
apply(simp add: contexts_as_set_def)
done


lemma advance_keeps_difficulty_elm [simp] :
  "DifficultyElm x24 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
  = (DifficultyElm x24 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma gaslimit_not_constant [simp] :
  "GaslimitElm x25 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma gaslimit_elm_means [simp] :
  "GaslimitElm x25 \<in> variable_ctx_as_set x1
  = (x25 = block_gaslimit (vctx_block x1))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma gaslimit_elm_c [simp] :
  "GaslimitElm x25 \<in> contexts_as_set x1 co_ctx
  = (x25 = block_gaslimit (vctx_block x1))"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_gaslimit_elm [simp] :
  "GaslimitElm x25 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (GaslimitElm x25 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma gasprice_not_constant [simp] :
  "GaspriceElm x26 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma gasprice_elm_means [simp] :
  "GaspriceElm x26 \<in> variable_ctx_as_set x1
  = (x26 = block_gasprice (vctx_block x1))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma gasprice_c_means [simp] :
  "GaspriceElm x26 \<in> contexts_as_set x1 co_ctx
  = (x26 = block_gasprice (vctx_block x1))"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_gasprice_elm [simp] :
"GaspriceElm x26 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
 = (GaspriceElm x26 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma stackheight_different [simp] :
"
StackHeightElm len \<in> stack_as_set lst =
(len = length lst)
"
apply(simp add: stack_as_set_def)
done

lemma stack_element_in_stack [simp] :
  "StackElm ab \<in> stack_as_set lst =
   ((fst ab) < length lst \<and> rev lst ! (fst ab) = snd ab)"
apply(case_tac ab; auto simp add: stack_as_set_def)
done

lemma storage_not_stack [simp] :
  "StorageElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma memory_not_stack [simp] :
  "MemoryElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma log_not_stack [simp] :
  "LogElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma gas_not_stack [simp] :
   "GasElm x7 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma memory_usage_not_stack [simp] :
  "MemoryUsageElm x8 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma this_account_not_stack [simp] :
  "ThisAccountElm x10 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma balance_not_stack [simp]:
  "BalanceElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma code_elm_means [simp]:
  "CodeElm xy \<in> instruction_result_as_set c (InstructionContinue x1) =
(program_content (cctx_program c) (fst xy) = Some (snd xy) \<or>
    program_content (cctx_program c) (fst xy) = None \<and>
    (snd xy) = Misc STOP)
"
apply(auto simp add: instruction_result_as_set_def contexts_as_set_def)
done

lemma pc_elm_means [simp]:
   "PcElm k \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
    (k = vctx_pc x1)"
apply(auto simp add: instruction_result_as_set_def)
done

lemma block_number_pred_sep [simp] :
  "(block_number_pred bn ** rest) s =
   ((BlockNumberElm bn \<in> s) \<and> rest (s - {BlockNumberElm bn}))"
apply(auto simp add: sep_def block_number_pred_def)
done

lemma block_number_elm_not_constant [simp] :
  "BlockNumberElm bn \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma block_number_elm_in_v_means [simp] :
  "BlockNumberElm bn \<in> variable_ctx_as_set v
   = ( bn = block_number (vctx_block v) )"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma block_number_elm_means [simp] :
  "BlockNumberElm bn \<in> instruction_result_as_set co_ctx (InstructionContinue v)
   = ( bn = block_number (vctx_block v) )"
apply(simp add: instruction_result_as_set_def contexts_as_set_def)
done

lemma stack_heigh_elm_means [simp] :
  "StackHeightElm h \<in> instruction_result_as_set co_ctx (InstructionContinue x1)
  = (length (vctx_stack x1) = h)"
apply(auto simp add: instruction_result_as_set_def)
done

lemma stack_elm_means [simp] :
  "StackElm ha \<in> instruction_result_as_set co_ctx (InstructionContinue v) =
  (fst ha < length (vctx_stack v) \<and> rev (vctx_stack v) ! fst ha = snd ha)"
apply(auto simp add: instruction_result_as_set_def contexts_as_set_def)
done

lemma balance_not_constant [simp] :
  "BalanceElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma balance_elm_i_means [simp] :
  "BalanceElm ab \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
     (vctx_balance x1 (fst ab) = (snd ab))
  "
apply(simp add: instruction_result_as_set_def contexts_as_set_def)
done

lemma gas_elm_i_means [simp] :
  "GasElm g \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
  (vctx_gas x1 = g)"
apply(simp add: instruction_result_as_set_def)
done

lemma continuing_continuing [simp] :
  "ContinuingElm True \<in> instruction_result_as_set co_ctx (InstructionContinue x1)"
apply(simp add: instruction_result_as_set_def)
done

lemma origin_not_stack [simp] :
   "OriginElm x13 \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma sent_value_not_stack [simp] :
 "SentValueElm x14 \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma sent_data_length_not_stack [simp] :
  "SentDataLengthElm x15 \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma ext_program_not_stack [simp] :
  "ExtProgramElm a \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma sent_data_not_stack [simp] :
"SentDataElm ab \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma contract_action_elm_not_stack [simp] :
 "ContractActionElm x19 \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma block_number_elm_c_means [simp] :
"BlockNumberElm x22 \<in> contexts_as_set x1 co_ctx =
 (x22 = block_number (vctx_block x1))"
apply(simp add: contexts_as_set_def)
done


lemma balance0 [simp] :
"length list = h \<Longrightarrow>
vctx_stack x1 = a # list \<Longrightarrow>
vctx_gas x1 = g \<Longrightarrow>
program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Info BALANCE) \<Longrightarrow>
(instruction_result_as_set co_ctx
              (InstructionContinue (vctx_advance_pc co_ctx x1\<lparr>vctx_stack := b # list, vctx_gas := g - 400\<rparr>)) -
             {BlockNumberElm (block_number (vctx_block x1))} -
             {StackHeightElm (Suc h)} -
             {StackElm (h, b)} -
             {PcElm (vctx_pc x1 + 1)} -
             {BalanceElm (ucast a, b)} -
             {GasElm (g - 400)} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Info BALANCE)})
=
(instruction_result_as_set co_ctx (InstructionContinue x1) - {BlockNumberElm (block_number (vctx_block x1))} -
             {StackHeightElm (Suc h)} -
             {StackElm (h, a)} -
             {PcElm (vctx_pc x1)} -
             {BalanceElm (ucast a, b)} -
             {GasElm g} -
             {ContinuingElm True} -
             {CodeElm (vctx_pc x1, Info BALANCE)})"
apply(auto)
 apply(rename_tac elm; case_tac elm; auto simp add: instruction_result_as_set_def stack_as_set_def)
apply(rename_tac elm; case_tac elm; auto simp add: instruction_result_as_set_def stack_as_set_def)
done

lemma ext_program_size_elm_not_stack [simp] :
"ExtProgramSizeElm ab \<notin> stack_as_set (1 # ta)"
apply(simp add: stack_as_set_def)
done

lemma continuing_not_stack [simp] :
"ContinuingElm b \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma block_hash_not_stack [simp] :
"BlockhashElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma block_number_not_stack [simp] :
"BlockNumberElm x22 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma coinbase_not_stack [simp] :
 "CoinbaseElm x23 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma timestamp_not_stack [simp] :
  "TimestampElm x24 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma difficulty_not_stack [simp] :
 "DifficultyElm k \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma gaslimit_not_stack [simp] :
 "GaslimitElm x26 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma gasprice_not_stack [simp] :
"GaspriceElm a \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma ext_program_size_not_stack [simp] :
 "ExtProgramSizeElm p \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma advance_keeps_stack_elm [simp] :
  "StackElm x2 \<in> contexts_as_set (vctx_advance_pc co_ctx v) co_ctx =
  (StackElm x2 \<in> contexts_as_set v co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma advance_keeps_code_elm [simp] :
  "CodeElm x9 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (CodeElm x9 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma storage_elm_means [simp] :
  "StorageElm ab \<in> contexts_as_set x1 co_ctx =
   (vctx_storage x1 (fst ab) = (snd ab))"
apply(simp add: contexts_as_set_def)
done

lemma memory_elm_means [simp] :
   "MemoryElm ab \<in> contexts_as_set x1 co_ctx =
    (vctx_memory x1 (fst ab) = (snd ab))"
apply(simp add: contexts_as_set_def)
done

lemma log_not_constant [simp] :
  "LogElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma log_elm_means [simp] :
  "LogElm ab \<in> contexts_as_set x1 co_ctx =
   (fst ab < length (vctx_logs x1) \<and> vctx_logs x1 ! (fst ab) = (snd ab))"
apply(auto simp add: contexts_as_set_def)
done

lemma this_account_means [simp] :
  "ThisAccountElm x10 \<in> contexts_as_set x1 co_ctx =
   (cctx_this co_ctx = x10)"
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def program_as_set_def)
done

lemma balance_elm_c_means [simp] :
  "BalanceElm ab \<in> contexts_as_set x1 co_ctx =
   (vctx_balance x1 (fst ab) = (snd ab))"
apply(auto simp add: contexts_as_set_def)
done

lemma origin_not_constant [simp] :
  "OriginElm x13 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma orogin_elm_c_means [simp] :
  "OriginElm x13 \<in> contexts_as_set x1 co_ctx =
   (vctx_origin x1 = x13)"
apply(auto simp add: contexts_as_set_def)
done

lemma sent_value_not_constant [simp] :
  "SentValueElm x14 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma sent_value_c_means [simp] :
  "SentValueElm x14 \<in> contexts_as_set x1 co_ctx
  = (vctx_value_sent x1 = x14)"
apply(auto simp add: contexts_as_set_def)
done

lemma sent_data_length_c_means [simp] :
  "SentDataLengthElm x15 \<in> contexts_as_set x1 co_ctx =
  (length (vctx_data_sent x1) = x15)"
apply(auto simp add: contexts_as_set_def)
done

lemma sent_data_not_constant [simp] :
  "SentDataElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma sent_data_elm_c_means [simp] :
  "SentDataElm ab \<in> contexts_as_set x1 co_ctx =
   (fst ab < length (vctx_data_sent x1) \<and> (vctx_data_sent x1) ! (fst ab) = snd ab)"
apply(auto simp add: contexts_as_set_def)
done

lemma short_rev_append [simp]:
 "a < length t \<Longrightarrow> (rev t @ lst) ! a = rev t ! a"
	by (simp add: nth_append)

lemma memory_usage_not_constant [simp] :
"MemoryUsageElm x8 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma code_elms [simp] :
 "{CodeElm (pos, i) |pos i. P pos i \<or> Q pos i} \<subseteq> S =
 ({CodeElm (pos, i) | pos i. P pos i} \<subseteq> S \<and> {CodeElm (pos, i) | pos i. Q pos i} \<subseteq> S)"
apply(auto)
done

lemma memory_usage_elm_means [simp] :
  "MemoryUsageElm x8 \<in> contexts_as_set x1 co_ctx =
   (vctx_memory_usage x1 = x8)"
apply(simp add: contexts_as_set_def)
done

lemma pc_update_v [simp] :
  "x \<in> variable_ctx_as_set (x1\<lparr>vctx_pc := p\<rparr>) =
  (x = PcElm p \<or> x \<in> variable_ctx_as_set x1 - {PcElm (vctx_pc x1)})"
apply(auto simp add: variable_ctx_as_set_def ext_program_as_set_def)
done

lemma pc_update [simp] :
  "x \<in> contexts_as_set (x1\<lparr>vctx_pc := p\<rparr>) co_ctx =
  (x = PcElm p \<or> x \<in> contexts_as_set x1 co_ctx - {PcElm (vctx_pc x1)})"
apply(auto simp add: contexts_as_set_def)
done

lemma stack_as_set_cons [simp] :
  "x \<in> stack_as_set (w # lst) =
   (x = StackHeightElm (Suc (length lst)) \<or>
   x = StackElm (length lst, w) \<or>
   x \<in> stack_as_set lst - {StackHeightElm (length lst)})"
apply(auto simp add: stack_as_set_def)
done


lemma not_continuing_sep [simp] :
  "(not_continuing ** rest) s =
   (ContinuingElm False \<in> s \<and> rest (s - {ContinuingElm False}))"
apply(auto simp add: sep_def not_continuing_def)
done

lemma this_account_sep [simp] :
  "(this_account t ** rest) s =
   (ThisAccountElm t \<in> s \<and> rest (s - {ThisAccountElm t}))"
apply(auto simp add: this_account_def sep_def)
done

lemma action_sep [simp] :
  "(action a ** rest) s =
   (ContractActionElm a \<in> s \<and> rest (s - {ContractActionElm a}))"
apply(auto simp add: action_def sep_def)
done


(****** specifying each instruction *******)

declare predict_gas_def [simp]
        C_def [simp] Cmem_def [simp]
        Gmemory_def [simp]
        new_memory_consumption.simps [simp]
        thirdComponentOfC.simps [simp]
        subtract_gas.simps [simp]
        vctx_next_instruction_default_def [simp]
        stack_2_1_op_def [simp]
        stack_1_1_op_def [simp]
        stack_0_0_op_def [simp]
        inst_stack_numbers.simps [simp]
        arith_inst_numbers.simps [simp]
        program_sem.simps [simp]
        vctx_next_instruction_def [simp]
        instruction_sem_def [simp]
        check_resources_def [simp]
        info_inst_numbers.simps [simp]
        Gbalance_def [simp]
        stack_inst_numbers.simps [simp]
        pc_inst_numbers.simps [simp]
        pop_def [simp]
        jump_def [simp]
        jumpi_def [simp]
        instruction_failure_result_def [simp]
        strict_if_def [simp]
        blocked_jump_def [simp]
blockedInstructionContinue_def [simp]
vctx_pop_stack_def [simp]
stack_0_1_op_def [simp]
general_dup_def [simp]
dup_inst_numbers_def [simp]
storage_inst_numbers.simps [simp]

lemma leibniz :
  "r (s :: state_element set) \<Longrightarrow> s = t \<Longrightarrow> r t"
apply(auto)
done

lemma sload_advance [simp] :
"       program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Storage SLOAD) \<Longrightarrow>
       k = vctx_pc x1 \<Longrightarrow>
       vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps)
done


lemma sload_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000\<rangle>
           ** block_number_pred bn ** stack_height (h + 1)
           ** stack h idx
           ** program_counter k ** storage idx w ** gas_pred g ** continuing)
          {(k, Storage SLOAD)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h w
           ** program_counter (k + 1) ** storage idx w ** gas_pred (g - Gsload (unat bn)) ** continuing )"
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
