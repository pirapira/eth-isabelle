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

lemma Gverylow_positive [simp]:
  "Gverylow > 0"
apply(simp add: Gverylow_def)
done

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

lemma cut_memory_head:
 "cut_memory b (n + 1) m = a # lst \<Longrightarrow> m b = a"
apply(simp add: cut_memory.psimps)
apply(split if_splits; simp)
done

declare cut_memory.simps [simp del]

lemma cut_memory_S1 :
  "cut_memory b (n + 1) m = [] \<or> cut_memory b (n + 1) m = m b # cut_memory (b + 1) n m"
apply(simp add: cut_memory.simps)
done

lemma cut_memory_tail:
  "cut_memory b (n + 1) m = a # lst \<Longrightarrow> cut_memory (b + 1) n m = lst"
proof -
 assume "cut_memory b (n + 1) m = a # lst"
 moreover have "cut_memory b (n + 1) m = [] \<or> cut_memory b (n + 1) m = (m b # cut_memory (b + 1) n m)"
  by(rule cut_memory_S1)
 ultimately moreover have "cut_memory b (n + 1) m = m b # cut_memory (b + 1) n m"
  by simp
 ultimately show "cut_memory (b + 1) n m = lst"
  by simp
qed

lemma cut_memory_zero [simp] :
"cut_memory b 0 m = []"
apply(simp add: cut_memory.simps)
done

lemma cut_memory_cons0 :
  "(cut_memory b (n + 1) m = a # lst) =
   (n + 1 \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) n m = lst)"
apply(auto simp add: cut_memory_head cut_memory_tail)
apply(simp add: cut_memory.simps)
done

lemma cut_memory_cons1 :
  "(cut_memory b (n - 1 + 1) m = a # lst) =
   (n \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) (n - 1) m = lst)"
apply(simp only: cut_memory_cons0)
apply(simp)
done

lemma cut_memory_cons [simp] :
  "(cut_memory b n m = a # lst) =
   (n \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) (n - 1) m = lst)"
proof -
 have "(cut_memory b n m = a # lst) = (cut_memory b (n - 1 + 1) m = a # lst)"
   by simp
 moreover have "(cut_memory b (n - 1 + 1) m = a # lst) =
   (n \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) (n - 1) m = lst)"
   by (rule cut_memory_cons1)
 ultimately show "(cut_memory b n m = a # lst) =
   (n \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) (n - 1) m = lst)"
   by blast
qed

lemma memory8_sep :
  "(rest ** memory8 b a) s ==
   MemoryElm (b, a) \<in> s \<and> rest (s - {MemoryElm (b,a)})"
apply(simp add: memory8_def sep_def)
by (smt DiffE Diff_insert_absorb insertI1 insert_Diff)

lemma memory8_short
 :"      (memory8 b a ** rest)
        (instruction_result_as_set c (InstructionContinue v)) \<Longrightarrow>
       vctx_memory v b = a"
apply(simp add: memory8_sep)
apply(simp add: instruction_result_as_set_def)
done

lemma memory8_short2
 :"      (q ** memory8 b a ** rest)
        (instruction_result_as_set c (InstructionContinue v)) \<Longrightarrow>
       vctx_memory v b = a"
proof -
 assume "(q ** memory8 b a ** rest)
        (instruction_result_as_set c (InstructionContinue v))"
 then have "(memory8 b a ** q ** rest)
        (instruction_result_as_set c (InstructionContinue v))"
  by auto
 then show "vctx_memory v b = a"
  by (rule memory8_short)
qed


lemma sep_ac:
"(a ** b ** c) s \<Longrightarrow> (b ** a ** c) s"
 using sep_assoc by (simp add: sep_commute)

lemma memory_range_cons :
"(memory_range b (a # lst) ** rest) s = (memory8 b a ** memory_range (b + 1) lst ** rest) s"
apply(auto)
done

declare Hoare.memory8_sep [simp del]

lemma cut_memory_memory_range :
  "\<forall> rest b n.
   unat n = length lst \<longrightarrow>
   (memory_range b lst ** rest) (instruction_result_as_set c (InstructionContinue v))
   \<longrightarrow> cut_memory b n (vctx_memory v) = lst"
apply(induction lst)
 apply(simp add: unat_eq_0)
apply(auto simp add: memory_range_cons memory8_short)
 apply(rule memory8_short2)
 apply blast
apply(drule sep_ac)
apply(drule_tac x = "memory8 b a ** rest" in spec)
apply(drule_tac x = "b + 1" in spec)
apply(drule_tac x = "n - 1" in spec)
apply(auto)
apply(drule unat_suc)
by blast
declare Hoare.memory8_sep [simp]



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
Gbase_def [simp]


lemma emp_sep [simp] :
  "(emp ** rest) s = rest s"
apply(simp add: emp_def sep_def)
done

lemma memory_range_elms_index_aux :
"\<forall> i a begin_word. MemoryElm (i, a) \<in> memory_range_elms begin_word input \<longrightarrow>
    (\<exists>pos. \<not> length input \<le> pos \<and> begin_word + word_of_int (int pos) = i)"
apply(induction input)
 apply(simp)
apply(auto)
apply(drule_tac x = i in spec)
apply(drule_tac x = aa in spec)
apply(drule_tac x = "begin_word + 1" in spec)
apply(auto)
apply(rule_tac x = "Suc pos" in exI)
apply(auto)
apply(simp add: Word.wi_hom_syms(1))
done

lemma memory_range_elms_index :
"MemoryElm (i, a) \<in> memory_range_elms begin_word input \<longrightarrow>
    (\<exists>pos. \<not> length input \<le> pos \<and> begin_word + word_of_int (int pos) = i)"
apply(auto simp add: memory_range_elms_index_aux)
done

lemma memory_range_elms_index_meta :
"MemoryElm (i, a) \<in> memory_range_elms begin_word input \<Longrightarrow>
    (\<exists>pos. \<not> length input \<le> pos \<and> begin_word + word_of_int (int pos) = i)"
apply(auto simp add: memory_range_elms_index_aux)
done


lemma contra:
  "\<not> P \<longrightarrow> \<not> Q \<Longrightarrow> Q \<longrightarrow> P"
apply(auto)
done

lemma memory_range_elms_index_contra :
"(\<forall> pos. pos \<ge> length input \<or> begin_word + (word_of_int (int pos)) \<noteq> i) \<longrightarrow>
 MemoryElm (i, a) \<notin> memory_range_elms begin_word input"
apply(rule contra)
apply(simp)
apply(rule memory_range_elms_index)
done

lemma memory_range_elms_index_contra_meta :
"(\<forall> pos. pos \<ge> length input \<or> begin_word + (word_of_int (int pos)) \<noteq> i) \<Longrightarrow>
 MemoryElm (i, a) \<notin> memory_range_elms begin_word input"
apply(auto simp add: memory_range_elms_index_contra)
done

lemma suc_is_word :
"unat (len_word :: w256) = Suc n \<Longrightarrow>
n < 2 ^ 256 - 1
"
proof -
  have "unat (len_word :: 256 word) < 2 ^ 256"
    by (rule order_less_le_trans, rule unat_lt2p, simp)
  moreover assume "unat (len_word :: w256) = Suc n"
  ultimately have "Suc n < 2 ^ 256"
    by auto
  then show "n < 2 ^ 256 - 1"
    by auto
qed

lemma w256_add_com :
"(a :: w256) + b = b + a"
apply(auto)
done

lemma word_of_int_mod :
  "(word_of_int i = (w :: w256)) =
   (i mod 2 ^ 256 = uint w)"
apply(auto simp add:word_of_int_def Word.word.Abs_word_inverse Word.word.uint_inverse)
done

lemma too_small_to_overwrap :
  "(1 :: 256 word) + word_of_int (int pos) = 0 \<Longrightarrow>
   (pos :: nat) \<ge> 2 ^ 256 - 1"
proof -
  have "word_of_int (int pos) + (1 :: 256 word) = (1 :: 256 word) + word_of_int (int pos)"
    by (rule w256_add_com)
  moreover assume "(1 :: 256 word) + word_of_int (int pos) = 0"
  ultimately have "word_of_int (int pos) + (1 :: 256 word) = 0"
    by auto
  then have "word_of_int (int pos) = (max_word :: 256 word)"
    by (rule Word.max_word_wrap)
  then have "(int pos) mod 2^256 = (uint (max_word :: 256 word))"
    by (simp add: word_of_int_mod)
  then have "pos \<ge> nat (uint (max_word :: 256 word))"
    (* sledgehammer *)
    proof -
    have "(0::int) \<le> 2"
      by auto
    then show ?thesis
      by (metis (no_types) Divides.mod_less_eq_dividend Divides.transfer_nat_int_functions(2) Nat_Transfer.transfer_nat_int_function_closures(4) Nat_Transfer.transfer_nat_int_function_closures(9) \<open>int pos mod 2 ^ 256 = uint max_word\<close> nat_int.Rep_inverse)
    qed
  then show "(pos :: nat) \<ge> 2 ^ 256 - 1"
    by(simp add: max_word_def)
  qed

lemma no_overwrap [simp]:
  "unat (len_word :: w256) = Suc (length input) \<Longrightarrow>
   MemoryElm (begin_word, a) \<notin> memory_range_elms (begin_word + 1) input"
apply(rule memory_range_elms_index_contra_meta)
apply(drule suc_is_word)
apply(auto)
apply(drule too_small_to_overwrap)
apply(auto)
done

lemma insert_is :
       "(e \<in> va \<and>
        va - {e} = R) =
       (va = insert e R \<and> e \<notin> R)"
apply(auto)
done


lemma memory_range_alt :
       "\<forall> len_word begin_word va.
        unat (len_word :: w256) = length input \<longrightarrow>
        memory_range begin_word input va =
        (va = memory_range_elms begin_word input)"
apply(induction input)
 apply(simp add: emp_def)
apply(clarify)
apply(drule_tac x = "len_word - 1" in spec)
apply(drule_tac x = "begin_word + 1" in spec)
apply(drule_tac x = "va - {MemoryElm (begin_word, a)}" in spec)
apply(subgoal_tac "unat (len_word - 1) = length input")
 apply (simp add: insert_is)
apply(simp)
apply (metis diff_Suc_1 lessI unat_eq_zero unat_minus_one zero_order(3))
done


lemma memory_range_sep :
"  \<forall> begin_word len_word rest s.
       unat (len_word :: w256) = length input \<longrightarrow>
       (memory_range begin_word input ** rest) s =
       ((memory_range_elms begin_word input \<subseteq> s) \<and> rest (s - memory_range_elms begin_word input)) 
"
apply(auto simp add: sep_def memory_range_alt)
apply(rule leibniz)
 apply blast
apply(auto)
done

lemma continuging_not_memory_range [simp] :
  "\<forall> in_begin. ContinuingElm False \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma contractaction_not_memory_range [simp] :
  "\<forall> in_begin a. ContractActionElm a
       \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma pc_not_memory_range [simp] :
  "\<forall> in_begin k. PcElm k \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma this_account_not_memory_range [simp] :
  "\<forall> this in_begin. ThisAccountElm this \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma balance_not_memory_range [simp] :
  "\<forall> in_begin. BalanceElm p \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma code_not_memory_range [simp] :
  "\<forall> k in_begin. CodeElm pair \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma continuing_not_memory_range [simp] :
  "\<forall> b in_begin. ContinuingElm b \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma stack_not_memory_range [simp] :
  "\<forall> in_begin. StackElm e \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma stack_height_not_memory_range [simp] :
  "\<forall> in_begin. StackHeightElm h \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma gas_not_memory_range [simp] :
  "\<forall> in_begin. GasElm g \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

declare memory_range_elms.simps [simp del]
declare memory_range_elms.psimps [simp del]

declare predict_gas_def [simp del]
declare misc_inst_numbers.simps [simp]

definition triple_alt ::
 "failure_reason set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> (int * inst) set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "triple_alt allowed_failures pre insts post ==
    \<forall> co_ctx presult rest stopper. no_assertion co_ctx \<longrightarrow>
       (code insts ** pre ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k.
         ((post ** code insts ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx k presult)))
         \<or> failed_for_reasons allowed_failures (program_sem stopper co_ctx k presult))"

lemma code_ac :
  "(code c ** pre ** rest) s =
   (pre ** code c ** rest) s"
  using sep_ac by blast

lemma triple_triple_alt :
  "triple s pre c post = triple_alt s pre c post"
apply(simp only: triple_def triple_alt_def code_ac)
done

declare stack_height_sep [simp del]
declare stack_sep [simp del]
declare balance_sep [simp del]
declare program_counter_sep [simp del]

(*
     apply(simp only: stack_height_sep)
     apply(simp only: stack_sep)
     apply(clarify)
     apply(simp only: balance_sep)
     apply(simp only: program_counter_sep)
     apply(simp only: gas_pred_sep)
     apply(clarify)
     apply(simp only: this_account_sep)
     apply(simp only: balance_sep)
     apply(simp only: not_continuing_sep)
*)

fun stack_topmost_elms :: "nat \<Rightarrow> w256 list \<Rightarrow> state_element set"
where
  "stack_topmost_elms h [] = { StackHeightElm h }"
| "stack_topmost_elms h (f # rest) = { StackElm (h, f) } \<union> stack_topmost_elms (h + 1) rest"

declare stack_topmost_elms.simps [simp del]

definition stack_topmost :: "nat \<Rightarrow> w256 list \<Rightarrow> state_element set \<Rightarrow> bool"
where
  "stack_topmost h lst s = (s = stack_topmost_elms h lst)"

lemma stack_topmost_sep [simp] :
  "(stack_topmost h lst ** rest) s =
   (stack_topmost_elms h lst \<subseteq> s \<and> rest (s - stack_topmost_elms h lst))"
apply(auto simp add: stack_topmost_def sep_def)
apply(rule leibniz)
 apply blast
apply(auto)
done

lemma this_account_not_stack_topmost [simp] :
  "\<forall> h. ThisAccountElm this
       \<notin> stack_topmost_elms h lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma gas_not_stack_topmost [simp] :
  "\<forall> h. GasElm g
       \<notin> stack_topmost_elms h lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma stack_topmost_empty [simp] :
 "x \<in> stack_topmost_elms h [] = (x = StackHeightElm h)"
apply(simp add: stack_topmost_elms.simps)
done

lemma memory_range_elms_not_pc [simp] :
  "(memory_range_elms in_begin input \<subseteq> s - {PcElm k}) =
   (memory_range_elms in_begin input \<subseteq> s)"
apply(auto)
done


lemma memory_range_elms_not_code [simp] :
  "(memory_range_elms in_begin input
       \<subseteq> s - {CodeElm pair}) =
   (memory_range_elms in_begin input \<subseteq> s)
  "
apply(auto)
done

lemma memory_not_stack_topmost [simp] :
  "\<forall> h. MemoryElm p \<notin> stack_topmost_elms h lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma stack_topmost_not_memory [simp] :
  "\<forall> in_begin. (stack_topmost_elms h lst
       \<subseteq> s - memory_range_elms in_begin input) =
   (stack_topmost_elms h lst \<subseteq> s)"
apply(induction input; auto simp add: memory_range_elms.simps)
done

lemma pc_not_stack_topmost [simp] :
  "\<forall> h. PcElm (vctx_pc x1) \<notin> stack_topmost_elms h lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma stack_topmost_not_pc [simp] :
  "\<forall> h. stack_topmost_elms h lst
       \<subseteq> s - {PcElm (vctx_pc x1)} =
     (stack_topmost_elms h lst \<subseteq> s)"
apply(auto)
done

lemma stack_topmost_not_code [simp] :
  "\<forall> h. stack_topmost_elms h lst
       \<subseteq> s - {CodeElm (vctx_pc x1, Misc CALL)} =
     (stack_topmost_elms h lst \<subseteq> s)"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma memory_subtract_gas [simp] :
 "x \<in> memory_range_elms in_begin input \<Longrightarrow>
  x \<in> instruction_result_as_set co_ctx
          (subtract_gas g r) =
  (x \<in> instruction_result_as_set co_ctx r)"
apply(simp add: instruction_result_as_set_def)
apply(case_tac r; simp)
 apply(case_tac x; simp)
apply(case_tac x; simp)
done

lemma stack_height_after_call [simp] :
       "vctx_balance x1 (cctx_this co_ctx) \<ge> vctx_stack x1 ! 2 \<Longrightarrow>
        (StackHeightElm (h + 7) \<in>
          instruction_result_as_set co_ctx (InstructionContinue x1)) \<Longrightarrow>
        (StackHeightElm h
          \<in> instruction_result_as_set co_ctx (subtract_gas g (call x1 co_ctx)))
        "
apply(simp add: call_def)
apply(case_tac "vctx_stack x1"; simp)
apply(case_tac list; simp)
apply(case_tac lista; simp)
apply(case_tac listb; simp)
apply(case_tac listc; simp)
apply(case_tac listd; simp)
apply(case_tac liste; simp)
apply(auto simp add: instruction_result_as_set_def)
done

lemma drop_suc :
 "drop (Suc h) lst =
  drop 1 (drop h lst)"
  by simp

lemma pqqp :
 "(P :: bool) \<longrightarrow> Q \<Longrightarrow>
  Q \<longrightarrow> P \<Longrightarrow>
  P = Q"
apply(case_tac P; case_tac Q; simp)
done


lemma topmost_elms_means [simp] :
   "\<forall> h x1.
    stack_topmost_elms h lst
       \<subseteq> instruction_result_as_set co_ctx (InstructionContinue x1) =
    (length (vctx_stack x1) = h + (length lst) \<and>
     drop h (rev (vctx_stack x1)) = lst)
    "
apply(induction lst; simp)
 apply(simp add: stack_topmost_elms.simps)
 apply blast
apply(simp add: stack_topmost_elms.simps)
apply(rule allI)
apply(rule allI)
apply(rule pqqp; simp)
  (* sledgehammer *)
  apply (metis Cons_nth_drop_Suc length_rev)
apply(simp only: drop_suc)
apply(rule impI)
apply(rule conjI)
 apply(rule List.nth_via_drop)
 apply blast
apply(simp)
done

lemma to_environment_not_continuing [simp] :
  "ContinuingElm True
       \<notin> instruction_result_as_set co_ctx (InstructionToEnvironment x31 x32 x33)"
apply(simp add: instruction_result_as_set_def)
done

lemma balance_not_topmost [simp] :
  "\<forall> h. BalanceElm pair \<notin> stack_topmost_elms h lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma continue_not_topmost [simp] :
  "\<forall> len. ContinuingElm b
       \<notin> stack_topmost_elms len lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma this_account_i_means [simp] :
  "ThisAccountElm this \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
   (cctx_this co_ctx = this)"
apply(simp add: instruction_result_as_set_def)
done

lemma memory_usage_not_memory_range [simp] :
  "\<forall> in_begin. MemoryUsageElm u \<notin> memory_range_elms in_begin input"
apply(induction input; auto simp add: memory_range_elms.simps)
done

lemma memory_usage_not_topmost [simp] :
  "\<forall> len. MemoryUsageElm u
       \<notin> stack_topmost_elms len lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma call_new_balance [simp] :
      "v \<le> fund \<Longrightarrow>
       ThisAccountElm this \<in> instruction_result_as_set co_ctx (InstructionContinue x1) \<Longrightarrow>
       vctx_balance x1 this = fund \<Longrightarrow>
       predict_gas (Misc CALL) x1 co_ctx \<le> vctx_gas x1 \<Longrightarrow>
       vctx_stack x1 = g # r # v # in_begin # in_size # out_begin # out_size # tf \<Longrightarrow>
       BalanceElm (this, fund - v)
       \<in> instruction_result_as_set co_ctx
           (subtract_gas (predict_gas (Misc CALL) x1 co_ctx) (call x1 co_ctx))"
apply(clarify)
apply(auto simp add: call_def failed_for_reasons_def)
apply(simp add: instruction_result_as_set_def)
apply(simp add: update_balance_def)
done

lemma advance_pc_call [simp] :
      "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Misc CALL) \<Longrightarrow>
       k = vctx_pc x1 \<Longrightarrow>
       vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps)
done

lemma memory_range_elms_not_continuing [simp] :
  "(memory_range_elms in_begin input
       \<subseteq> insert (ContinuingElm True) (contexts_as_set x1 co_ctx))
  = (memory_range_elms in_begin input
       \<subseteq> (contexts_as_set x1 co_ctx))
  "
apply(auto)
done

lemma suc_unat :
"Suc n = unat (aa :: w256) \<Longrightarrow>
n = unat (aa - 1)
"
apply(rule HOL.sym)
apply(drule HOL.sym)
apply(rule unat_suc)
apply(simp)
done

lemma memory_range_elms_cut_memory [simp] :
       "\<forall> in_begin in_size.
        length lst = unat in_size \<longrightarrow> 
        memory_range_elms in_begin lst \<subseteq> variable_ctx_as_set x1 \<longrightarrow>
        cut_memory in_begin in_size (vctx_memory x1) = lst"
apply(induction lst)
 apply(simp add: unat_eq_0)
apply(rule allI)
apply(rule allI)
apply(drule_tac x = "in_begin + 1" in spec)
apply(drule_tac x = "in_size - 1" in spec)
apply(auto simp add: memory_range_elms.simps)
apply(drule suc_unat)
apply(simp)
done

lemma stack_height_in_topmost [simp] :
   "\<forall> h. StackHeightElm x1a
       \<in> stack_topmost_elms h lst =
    (x1a = h + length lst)"
apply(induction lst)
 apply(simp)
apply(auto simp add: stack_topmost_elms.simps)
done

lemma code_elm_not_stack_topmost [simp] :
 "\<forall> len. CodeElm x9
       \<notin> stack_topmost_elms len lst"
apply(induction lst)
 apply(auto)
apply(auto simp add: stack_topmost_elms.simps)
done

lemma stack_elm_c_means [simp] :
  "StackElm x
       \<in> contexts_as_set v c =
   (
    rev (vctx_stack v) ! fst x = snd x \<and>
    fst x < length (vctx_stack v) )"
apply(simp add: contexts_as_set_def)
done

lemma stack_elm_in_topmost [simp] :
  "\<forall> len. StackElm x2
       \<in> stack_topmost_elms len lst =
   (fst x2 \<ge> len \<and> fst x2 < len + length lst \<and> lst ! (fst x2 - len) = snd x2)"
apply(induction lst)
 apply(simp)
apply(rule allI)
apply(drule_tac x = "Suc len" in spec)
apply(case_tac x2)
apply(auto simp only: stack_topmost_elms.simps; simp)
 apply(case_tac "aa \<le> len"; auto)
apply(case_tac "aa = len"; auto)
done

lemma rev_append_eq :
  "(rev tf @ l) ! a =
   (if a < length tf then rev tf ! a else l ! (a - length tf))"
apply(auto)
  by (simp add: nth_append)

lemma code_elm_in_c :
  "CodeElm x9 \<in> contexts_as_set x1 co_ctx =
   (program_content (cctx_program co_ctx) (fst x9) = Some (snd x9) \<or>
    program_content (cctx_program co_ctx) (fst x9) = None \<and> snd x9 = Misc STOP)"
apply(simp add: contexts_as_set_def)
done

lemma storage_not_stack_topmost [simp] :
   "\<forall> len. StorageElm x3
       \<notin> stack_topmost_elms len lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma log_not_topmost [simp] :
 "\<forall> len. LogElm x5
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma caller_not_topmost [simp]:
       "\<forall> len. CallerElm x12
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma origin_not_topmost [simp] :
  "\<forall> len. OriginElm x13
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma sent_valie_not_topmost [simp] :
  "\<forall> len. SentValueElm x14
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma sent_data_length_not_topmost [simp] :
       "\<forall> len. SentDataLengthElm x15
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add : stack_topmost_elms.simps)
done

lemma sent_data_not_topmost [simp]:
   "\<forall> len. SentDataElm x16
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma ext_program_size_not_topmost [simp] :
   "\<forall> len. ExtProgramSizeElm x17
        \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma code_elm_c [simp] :
  "CodeElm x \<in> contexts_as_set y c = (CodeElm x \<in> constant_ctx_as_set c)"
apply(simp add: contexts_as_set_def)
done

lemma ext_program_not_topmost_elms [simp] :
  "\<forall> len. ExtProgramElm x18
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done


lemma block_hash_not_topmost [simp] :
       "\<forall> len. BlockhashElm x21
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma block_number_not_topmost [simp] :
 "\<forall> len. BlockNumberElm n
   \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma coinbase_not_topmost [simp] :
  "\<forall> len.     CoinbaseElm x23
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma timestamp_not_topmost [simp] :
  "\<forall> len. TimestampElm t
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma difficulty_not_topmost [simp] :
  "\<forall> len. DifficultyElm d
        \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma memory_range_gas_update [simp] :
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
   x \<in> variable_ctx_as_set
               (x1
                \<lparr>vctx_gas := g \<rparr>) =
   (x \<in> variable_ctx_as_set x1)"
apply(auto simp add: variable_ctx_as_set_def)
done

lemma memory_range_stack [simp] :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (x1\<lparr>vctx_stack := sta\<rparr>)
      = (x \<in> variable_ctx_as_set x1)"
apply(case_tac x; simp)
done

lemma memory_range_memory_usage [simp] :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (x1\<lparr>vctx_memory_usage := u\<rparr>)
      = (x \<in> variable_ctx_as_set x1)"
apply(case_tac x; simp)
done


lemma memory_range_balance [simp] :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (x1\<lparr>vctx_balance := u\<rparr>)
      = (x \<in> variable_ctx_as_set x1)"
apply(case_tac x; simp)
done


lemma memory_range_advance_pc [simp] :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (vctx_advance_pc co_ctx x1)
     = (x \<in> variable_ctx_as_set x1)
"
apply(case_tac x; simp)
done

(*
       x \<in> memory_range_elms in_begin input \<Longrightarrow>
       \<not> vctx_balance x1 (cctx_this co_ctx) < v \<Longrightarrow>
       x \<in> variable_ctx_as_set
             (vctx_advance_pc co_ctx x1
              \<lparr>vctx_stack := tf,
                 vctx_balance :=
                   update_balance (cctx_this co_ctx) (\<lambda>orig. orig - v) (vctx_balance x1),
                 vctx_memory_usage :=
                   M (M (vctx_memory_usage x1) in_begin in_size) out_begin out_size\<rparr>)
*)

lemma memory_range_action [simp] :
      "x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> instruction_result_as_set co_ctx
             (InstructionToEnvironment
               act
               v
               cont) =
       (x \<in> variable_ctx_as_set v)"
apply(auto simp add: instruction_result_as_set_def)
 apply(case_tac x; simp)
apply(case_tac x; simp)
done

lemma storage_not_memory_range [simp] :
  "\<forall> in_begin. StorageElm x3 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma memory_range_insert_cont [simp] :
   "memory_range_elms in_begin input
         \<subseteq> insert (ContinuingElm True) s =
    (memory_range_elms in_begin input
         \<subseteq> s)"
apply(auto)
done

lemma memory_range_constant_union [simp] :
  "memory_range_elms in_begin input \<subseteq> constant_ctx_as_set co_ctx \<union> s =
   (memory_range_elms in_begin input \<subseteq> s)"
apply(auto simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma memory_range_elms_i [simp] :
      "memory_range_elms in_begin input
       \<subseteq> instruction_result_as_set co_ctx (InstructionContinue x1) =
       (memory_range_elms in_begin input \<subseteq>
        variable_ctx_as_set x1)"
apply(auto simp add: instruction_result_as_set_def contexts_as_set_def)
done

lemma memory_range_continue [simp] :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
       (x \<in> variable_ctx_as_set x1)"
apply(auto simp add: instruction_result_as_set_def contexts_as_set_def constant_ctx_as_set_def program_as_set_def)
done

lemma call_memory_no_change [simp] :
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
   x \<in> instruction_result_as_set co_ctx
         (subtract_gas (predict_gas (Misc CALL) x1 co_ctx) (call x1 co_ctx)) =
  (x \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: call_def)
apply(case_tac "vctx_stack x1"; simp)
apply(case_tac list; simp)
apply(case_tac lista; simp)
apply(case_tac listb;simp)
apply(case_tac listc; simp)
apply(case_tac listd; simp)
apply(case_tac liste; simp)
done


lemma memory_call [simp] :
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
    x \<in> instruction_result_as_set co_ctx (call x1 co_ctx) =
    (x \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: call_def)
apply(case_tac "vctx_stack x1"; simp)
apply(case_tac list; simp)
apply(case_tac lista; simp)
apply(case_tac listb; simp)
apply(case_tac listc; simp)
apply(case_tac listd; simp)
apply(case_tac liste; simp)
done



lemma gas_limit_not_topmost [simp] :
  "\<forall> len. GaslimitElm g
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma gas_price_not_topmost [simp] :
" \<forall> len. GaspriceElm p
       \<notin> stack_topmost_elms len lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done


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
(*  defer
  apply(auto simp add: instruction_result_as_set_def memory_range_sep)
 apply(simp add: instruction_result_as_set_def memory_range_sep stack_height_sep) *)
  defer
  

apply(clarify)
apply(simp add: call_def)
  defer
  apply(simp add: balance_sep)
 apply(simp add: instruction_result_as_set_def failed_for_reasons_def program_counter_sep
     memory_range_sep balance_sep)
apply(simp add: program_counter_sep)
apply(split if_splits; auto)
   defer
   apply(simp add: memory_range_sep)
  apply(simp add: memory_range_sep)
 apply(simp add: memory_range_sep)
apply(simp add: memory_range_sep)
apply(auto simp add: call_def)
    apply(simp add: balance_sep)
   apply(simp add: instruction_result_as_set_def)
  apply(simp add: instruction_result_as_set_def)
 apply(simp add: balance_sep)
apply(simp add: balance_sep instruction_result_as_set_def)
apply(simp add: update_balance_def)
apply(simp add: program_counter_sep)
apply(rule_tac x = "vctx_gas x1 - predict_gas (Misc CALL) x1 co_ctx" in exI)
apply(simp add: failed_for_reasons_def)
apply(rule leibniz)
 apply blast
apply(rule Set.equalityI)
 apply(clarify)
 apply(rename_tac elm)
 apply(simp)
 apply(case_tac elm; simp)
   apply(clarify)
   apply(simp add: rev_append_eq)
   apply(split if_splits; simp)
  apply(simp add: contexts_as_set_def)
  apply(case_tac "program_content (cctx_program co_ctx) (fst x9) = Some (snd x9)"; simp)
 apply(simp add: update_balance_def)
 apply(split if_splits)
  apply(case_tac x11; simp)
 apply(case_tac x11; simp)
apply(clarify)
apply(rename_tac elm)
apply(simp)
apply(case_tac elm; simp)
apply(simp add: update_balance_def)
apply(split if_splits; simp)
apply(clarify)
apply(simp)
done


(*  I'm seeing something squared ---
    maybe use this in a blog post.
     \<not> (h + 3 = h + 4 \<and> in_begin = v) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     \<not> (h + 3 = h + 5 \<and> in_begin = r) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     \<not> (h + 3 = h + 6 \<and> in_begin = g) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     StackElm (h + 3, in_begin) \<notin> memory_range_elms in_begin input \<Longrightarrow>
     StackElm (h + 3, in_begin) \<noteq> StackHeightElm (h + 7) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     StackElm (h + 3, in_begin) \<in> insert (ContinuingElm True) (contexts_as_set x1 co_ctx) \<Longrightarrow>
     StackElm (h + 3, in_begin) \<noteq> PcElm (vctx_pc x1) \<Longrightarrow>
     StackElm (h + 3, in_begin) \<notin> {} \<Longrightarrow>
     StackElm (h + 3, in_begin) \<noteq> CodeElm (vctx_pc x1, Misc CALL) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     \<not> (Suc (Suc h) = h + 3 \<and> in_size = in_begin) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     \<not> (Suc (Suc h) = h + 4 \<and> in_size = v) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     \<not> (Suc (Suc h) = h + 5 \<and> in_size = r) \<Longrightarrow>
     \<not> False \<Longrightarrow>
     \<not> (Suc (Suc h) = h + 6 \<and> in_size = g) \<Longrightarrow>
*)

(* perhaps, think about spliting call into some functions *)
(*
       StackElm (Suc (Suc h), in_size) \<notin> memory_range_elms in_begin input \<and>
       GasElm own_gas \<notin> memory_range_elms in_begin input \<and>
       ThisAccountElm this \<in> instruction_result_as_set co_ctx (InstructionContinue x1) \<and>
       vctx_balance x1 this = fund \<and>
       k = vctx_pc x1 \<and>
       program_content (cctx_program co_ctx) k = Some (Misc CALL) \<and>
       rest (instruction_result_as_set co_ctx (InstructionContinue x1) -
             memory_range_elms in_begin input -
             {StackHeightElm (h + 7)} -
             {StackElm (h + 6, g)} -
             {StackElm (h + 5, r)} -
             {StackElm (h + 4, v)} -
             {StackElm (h + 3, in_begin)} -
             {StackElm (Suc (Suc h), in_size)} -
             {StackElm (Suc h, out_begin)} -
             {StackElm (h, out_size)} -
             {GasElm own_gas} -
             {ThisAccountElm this} -
             {BalanceElm (this, fund)} -
             {PcElm k} -
             {ContinuingElm True} -
             {CodeElm (k, Misc CALL)}) \<Longrightarrow>
       \<not> failed_for_reasons {OutOfGas}
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<Longrightarrow>
       memory_range_elms in_begin input
       \<subseteq> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       StackHeightElm h
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       StackHeightElm h \<notin> memory_range_elms in_begin input \<and>
       BalanceElm (this, fund)
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       PcElm (vctx_pc x1)
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       GasElm (own_gas - X)
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       GasElm (own_gas - X) \<notin> memory_range_elms in_begin input \<and>
       ContinuingElm False
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       ContractActionElm
        (ContractCall
          \<lparr>callarg_gas = g, callarg_code = ucast r, callarg_recipient = ucast r, callarg_value = v,
             callarg_data = input, callarg_output_begin = out_begin, callarg_output_size = out_size\<rparr>)
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       CodeElm (vctx_pc x1, Misc CALL)
       \<in> instruction_result_as_set co_ctx
           (case case program_content (cctx_program co_ctx) (vctx_pc x1) of None \<Rightarrow> Some (Misc STOP)
                 | Some x \<Rightarrow> Some x of
            None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
            | Some i \<Rightarrow>
                if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                else InstructionToEnvironment
                      (ContractFail
                        (case inst_stack_numbers i of
                         (consumed, produced) \<Rightarrow>
                           (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                            else [TooLongStack]) @
                           (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                      x1 None) \<and>
       rest (instruction_result_as_set co_ctx
              (case case program_content (cctx_program co_ctx) (vctx_pc x1) of
                    None \<Rightarrow> Some (Misc STOP) | Some x \<Rightarrow> Some x of
               None \<Rightarrow> InstructionToEnvironment (ContractFail [ShouldNotHappen]) x1 None
               | Some i \<Rightarrow>
                   if check_resources x1 co_ctx (vctx_stack x1) i then instruction_sem x1 co_ctx i
                   else InstructionToEnvironment
                         (ContractFail
                           (case inst_stack_numbers i of
                            (consumed, produced) \<Rightarrow>
                              (if int (length (vctx_stack x1)) + produced - consumed \<le> 1024 then []
                               else [TooLongStack]) @
                              (if predict_gas i x1 co_ctx \<le> vctx_gas x1 then [] else [OutOfGas])))
                         x1 None) -
             memory_range_elms in_begin input -
             {StackHeightElm h} -
             {BalanceElm (this, fund)} -
             {PcElm (vctx_pc x1)} -
             {GasElm (own_gas - X)} -
             {ContinuingElm False} -
             {ContractActionElm
               (ContractCall
                 \<lparr>callarg_gas = g, callarg_code = ucast r, callarg_recipient = ucast r,
                    callarg_value = v, callarg_data = input, callarg_output_begin = out_begin,
                    callarg_output_size = out_size\<rparr>)} -
             {CodeElm (vctx_pc x1, Misc CALL)})
StackElm (h, out_size) \<notin> memory_range_elms in_begin input
*)

declare stack_height_sep [simp]
declare stack_sep [simp]
declare balance_sep [simp]
declare program_counter_sep [simp]
declare predict_gas_def [simp]
declare gas_def [simp]



lemma gas_gas_triple :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<rangle> ** stack_height h ** program_counter k ** gas_pred g ** continuing)
          {(k, Info GAS)}
          (stack_height (h + 1) ** stack h (word_of_int (g - 2))
           ** program_counter (k + 1) ** gas_pred (g - 2) ** continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult; auto simp add: instruction_result_as_set_def)
 apply(simp add: gas_def  Word.wi_hom_syms(2))
apply(rule leibniz)
 apply blast
apply(rule  Set.equalityI; clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; simp)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; auto simp add: gas_def Word.wi_hom_syms(2))
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
