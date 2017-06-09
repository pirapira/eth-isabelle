theory HoareTripleForInstructions

imports Main "./Hoare"

begin


(**
 ** Hoare Triple for each instruction
 **)
declare insert_functional [intro]
declare balance_as_set_def [simp del]

lemma continuing_not_context [simp]:
  "ContinuingElm b \<notin> contexts_as_set x32 co_ctx"
apply(simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def program_as_set_def stack_as_set_def
data_sent_as_set_def  ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def  ext_program_as_set_def balance_as_set_def)
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
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma stack_element_means [simp] :
 "(StackElm pw \<in> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) = (snd pw) \<and> (fst pw) < length (vctx_stack v))"
apply(case_tac pw)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def  ext_program_as_set_def balance_as_set_def)
done

lemma stack_element_notin_means [simp] :
 "(StackElm pw \<notin> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) \<noteq> (snd pw) \<or> (fst pw) \<ge> length (vctx_stack v))"
apply(case_tac pw)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done


lemma storage_element_means [simp] :
  "StorageElm idxw \<in> variable_ctx_as_set v =
   (vctx_storage v (fst idxw) = (snd idxw))"
apply(case_tac idxw; simp)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma memory_element_means [simp] :
  "MemoryElm addrw \<in> variable_ctx_as_set v =
   (vctx_memory v (fst addrw) = snd addrw)"
apply(case_tac addrw; simp)
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma pc_not_balance [simp] :
  "PcElm p \<notin> balance_as_set b"
apply(simp add: balance_as_set_def)
done


lemma pc_element_means [simp] :
  "(PcElm p \<in> variable_ctx_as_set v) =
   (vctx_pc v = p)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def)
done

lemma gas_element_means [simp] :
  "(GasElm g \<in> variable_ctx_as_set v) =
    (vctx_gas v = g)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma log_element_means [simp] :
  "(LogElm p \<in> variable_ctx_as_set v) =
   (rev (vctx_logs v) ! (fst p) = (snd p) \<and> fst p < length (vctx_logs v))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
apply(case_tac p; auto)
done

lemma memory_usage_element_means [simp] :
  "(MemoryUsageElm u \<in> variable_ctx_as_set v) = (vctx_memory_usage v = u)"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma sent_value_means [simp] :
  "SentValueElm x14 \<in> variable_ctx_as_set x1 = (x14 = vctx_value_sent x1)"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma sent_data_means [simp] :
"SentDataElm p \<in> variable_ctx_as_set x1 = 
 (vctx_data_sent x1 ! (fst p) = (snd p) \<and> (fst p) < (length (vctx_data_sent x1)))"
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def  ext_program_as_set_def balance_as_set_def)
apply(rule_tac x = "fst p" in exI; simp)
done



lemma sent_data_length_means [simp] :
  "SentDataLengthElm x15 \<in> variable_ctx_as_set x1 = (x15 = length (vctx_data_sent x1))"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma this_account_elm_not_variable [simp] :
  "ThisAccountElm t
           \<notin> variable_ctx_as_set v"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
apply(case_tac p; auto)
done

lemma advance_pc_keeps_stack [simp] :
  "(vctx_stack (vctx_advance_pc co_ctx v)) = vctx_stack v"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_change [simp] :
  "vctx_pc x1 \<noteq> vctx_pc (vctx_advance_pc co_ctx x1)"
	by (metis advance_pc_different)

lemma caller_sep:
  "(caller c ** rest) s =
   (CallerElm c \<in> s \<and> rest (s - {CallerElm c}))"
 by (solve_sep_iff simp: caller_def)

lemma sep_caller:
  "(rest ** caller c) s =
   (CallerElm c \<in> s \<and> rest (s - {CallerElm c}))"
 by (solve_sep_iff simp: caller_def)

lemma sep_caller_sep:
  "(a ** caller c ** rest) s =
   (CallerElm c \<in> s \<and> (a ** rest) (s - {CallerElm c}))"
  (is "?L = ?R")
proof -
  have "?L = (caller c ** a ** rest) s"
    by simp
  moreover have "(caller c ** a ** rest) s = ?R"
    by (rule caller_sep)
  ultimately show ?thesis
    by auto
qed

lemma balance_sep :
  "(balance a b ** rest) s =
   (BalanceElm (a, b) \<in> s \<and> rest (s - {BalanceElm (a, b)}))"
 by (solve_sep_iff simp: balance_def)

lemma sep_balance :
  "(rest ** balance a b) s =
   (BalanceElm (a, b) \<in> s \<and> rest (s - {BalanceElm (a, b)}))"
 by (solve_sep_iff simp: balance_def)

lemma sep_balance_sep :
  "(q ** balance a b ** rest) s =
   (BalanceElm (a, b) \<in> s \<and> (q ** rest) (s - {BalanceElm (a, b)}))"
  (is "?L = ?R")
proof -
  have "?L = (balance a b ** q ** rest) s"
    by simp
  moreover have "(balance a b ** q ** rest) s = ?R"
    by (rule balance_sep)
  ultimately show ?thesis
    by auto
qed

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
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma stack_change_as_set [simp] :
   "(contexts_as_set (v\<lparr>vctx_stack := t\<rparr>) co_ctx) =
     (contexts_as_set v co_ctx - stack_as_set (vctx_stack v)) \<union> stack_as_set t 
    "
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
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
      program_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
apply(case_tac ab; auto)
done

lemma ext_program_size_c_means [simp] :
  "ExtProgramSizeElm ab \<in> contexts_as_set v co_ctx =
   (program_length (vctx_ext_program v (fst ab)) = snd ab)"
apply(simp add: contexts_as_set_def balance_as_set_def)
done

lemma ext_program_advance_pc [simp] :
  " vctx_ext_program (vctx_advance_pc co_ctx x1)
  = vctx_ext_program x1"
apply(simp add: vctx_advance_pc_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def ext_program_as_set_def stack_as_set_def balance_as_set_def)
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
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(auto simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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
 by (solve_sep_iff simp: block_number_pred_def)

lemma sep_block_number_pred_sep [simp] :
  "(rest ** block_number_pred bn ** a) s =
   ((BlockNumberElm bn \<in> s) \<and> (rest ** a) (s - {BlockNumberElm bn}))"
 apply (rule iffI)
 apply (sep_select_asm 2)
 apply (subst (asm) block_number_pred_sep, simp)
 apply (sep_select 2)
 apply (subst  block_number_pred_sep, simp)
 done

lemma block_number_elm_not_constant [simp] :
  "BlockNumberElm bn \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma block_number_elm_in_v_means [simp] :
  "BlockNumberElm bn \<in> variable_ctx_as_set v
   = ( bn = block_number (vctx_block v) )"
apply(simp add: variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def balance_as_set_def)
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

lemma log_num_v_advance [simp] :
  "LogNumElm x6 \<in> variable_ctx_as_set (vctx_advance_pc co_ctx x1) =
   (LogNumElm x6 \<in> variable_ctx_as_set x1)"
apply(simp add: variable_ctx_as_set_def)
done

lemma log_num_advance [simp] :
  "LogNumElm x6 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (LogNumElm x6 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def)
done
lemma account_existence_not_in_constant [simp] :
  "AccountExistenceElm p \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma account_existence_not_in_stack [simp] :
  "AccountExistenceElm p \<notin> stack_as_set (vctx_stack x1)"
apply(simp add: stack_as_set_def)
done

lemma account_existence_not_in_balance [simp] :
  "AccountExistenceElm p \<notin> balance_as_set (vctx_balance x1)"
apply(simp add: balance_as_set_def)
done

lemma account_existence_not_ext [simp] :
  "AccountExistenceElm p \<notin> ext_program_as_set (vctx_ext_program x1)"
apply(simp add: ext_program_as_set_def)
done

lemma account_existence_elm_means [simp] :
  "AccountExistenceElm p \<in> variable_ctx_as_set x =
   (vctx_account_existence x (fst p) = snd p)"
apply(case_tac p)
apply(auto simp add: variable_ctx_as_set_def)
done

lemma account_existence_elm_means_c [simp] :
  "AccountExistenceElm p \<in> contexts_as_set x c =
   (vctx_account_existence x (fst p) = snd p)"
apply(auto simp add: contexts_as_set_def)
done

lemma account_existence_advance [simp] :
  "AccountExistenceElm (aa, x) \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (AccountExistenceElm (aa, x) \<in> contexts_as_set x1 co_ctx)"
apply(simp add: contexts_as_set_def vctx_advance_pc_def)
done

lemma account_existence_advance_v [simp] :
  "vctx_account_existence (vctx_advance_pc co_ctx x1) aa =
  (vctx_account_existence x1 aa)"
apply(simp add: vctx_advance_pc_def)
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
 apply(rename_tac elm; case_tac elm; auto simp add: instruction_result_as_set_def stack_as_set_def balance_as_set_def)
apply(rename_tac elm; case_tac elm; auto simp add: instruction_result_as_set_def stack_as_set_def balance_as_set_def)
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
   (fst ab < length (vctx_logs x1) \<and> rev (vctx_logs x1) ! (fst ab) = (snd ab))"
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


lemma not_continuing_sep :
  "(not_continuing ** rest) s =
   (ContinuingElm False \<in> s \<and> rest (s - {ContinuingElm False}))"
 by (solve_sep_iff simp: not_continuing_def)

lemma sep_not_continuing :
  "(rest ** not_continuing ) s =
   (ContinuingElm False \<in> s \<and> rest (s - {ContinuingElm False}))"
 by (solve_sep_iff simp: not_continuing_def)

lemma sep_not_continuing_sep :
  "(a ** not_continuing ** rest) s =
   (ContinuingElm False \<in> s \<and> (a ** rest) (s - {ContinuingElm False}))"
	by (simp add: not_continuing_sep)

lemma this_account_sep :
  "(this_account t ** rest) s =
   (ThisAccountElm t \<in> s \<and> rest (s - {ThisAccountElm t}))"
 by (solve_sep_iff simp: this_account_def)

lemma sep_this_account :
  "(rest ** this_account t) s =
   (ThisAccountElm t \<in> s \<and> rest (s - {ThisAccountElm t}))"
 by (solve_sep_iff simp: this_account_def)

lemma sep_this_account_sep :
  "(a ** this_account t ** rest) s =
   (ThisAccountElm t \<in> s \<and> (a ** rest) (s - {ThisAccountElm t}))"
proof -
  have "(a ** this_account t ** rest) = (this_account t ** a ** rest)"
    by simp
  moreover have "(this_account t ** a ** rest) s = (ThisAccountElm t \<in> s \<and> (a ** rest) (s - {ThisAccountElm t}))"
    by (rule this_account_sep)
  ultimately show ?thesis
    by auto
qed




lemma action_sep :
  "(action a ** rest) s =
   (ContractActionElm a \<in> s \<and> rest (s - {ContractActionElm a}))"
 by (solve_sep_iff simp: action_def)

lemma sep_action :
  "(rest ** action a) s =
   (ContractActionElm a \<in> s \<and> rest (s - {ContractActionElm a}))"
 by (solve_sep_iff simp: action_def)


lemma sep_action_sep :
  "(b ** action a ** rest) s =
   (ContractActionElm a \<in> s \<and> (b ** rest) (s - {ContractActionElm a}))"
  apply (rule iffI)
   apply (sep_simp_asm simp: action_sep, fastforce)
  apply (sep_simp_no_asm simp: action_sep)
 done

lemma iota0_non_empty_aux:
  "\<forall> b x len lst a.
    len \<le> l \<longrightarrow>
    iota0 b len (lst @ [a]) = a # iota0 b len lst"
apply(induction l)
 apply(simp add: iota0.simps)
apply(auto simp add: iota0.simps)
apply(case_tac "len = Suc l")
 apply clarsimp
 apply(simp add: iota0.simps)
 apply(drule_tac x = "b + 1" in spec)
 apply(drule_tac x = l in spec)
 apply simp
 apply(drule_tac x = "b # lst" in spec)
 apply(drule_tac x = "a" in spec)
 apply simp
apply simp
done

lemma iota0_non_empty_aux':
  "\<forall> b x len lst a l.
    len \<le> l \<longrightarrow>
    iota0 b len (lst @ [a]) = a # iota0 b len lst"
using iota0_non_empty_aux apply auto
done

lemma iota0_non_empty:
  "iota0 b len (lst @ [a]) = a # iota0 b len lst"
using iota0_non_empty_aux' apply auto
done

lemma iota0_singleton':
  "iota0 b len ([] @ [a]) = a # iota0 b len []"
using iota0_non_empty apply blast
done

lemma iota0_singleton:
  "iota0 b len [a] = a # iota0 b len []"
using iota0_singleton' apply auto
done

lemma cut_memory_aux_alt_eqv :
  "\<forall> b. cut_memory_aux_alt b len m = cut_memory_aux b len m"
apply(induction len)
 apply(simp add: cut_memory_aux.simps cut_memory_aux_alt_def iota0.simps)
apply(simp add: cut_memory_aux.simps cut_memory_aux_alt_def iota0.simps iota0_singleton)
done

lemma cut_memory_head:
 "cut_memory b (n + 1) m = a # lst \<Longrightarrow> m b = a"
apply(simp add: cut_memory_aux.simps cut_memory_def cut_memory_aux_alt_eqv)
apply(cases "unat (n+1)")
apply(simp add: cut_memory_aux.simps cut_memory_def)
apply(simp add: cut_memory_aux.simps cut_memory_def)
done

(*
declare cut_memory.simps [simp del]
*)

lemma my_unat_suc : "unat (n::256 word) = x \<Longrightarrow> unat (n+1) > 0 \<Longrightarrow>
  unat (n+1) = x+1"
  by (metis Suc_eq_plus1 add.commute neq0_conv unatSuc unat_eq_zero)


lemma cut_memory_aux :
"cut_memory_aux b (Suc n) m = m b # cut_memory_aux (b+1) n m"
apply(simp add:cut_memory_aux.simps)
done

lemma cut_memory_S1 :
  "cut_memory b (n + 1) m = [] \<or> cut_memory b (n + 1) m = m b # cut_memory (b + 1) n m"
apply(simp add: cut_memory_def cut_memory_aux_alt_eqv)
apply(cases "unat (n + 1)")
apply(simp add:cut_memory_aux.simps)
apply(cases "unat n")
apply(simp add:cut_memory_aux.simps)
  apply (simp add: cut_memory_aux.simps(1) unat_eq_zero)

apply(simp add:cut_memory_aux.simps)
apply(cases "unat (n + 1)")
apply(simp)
apply(subst (asm) my_unat_suc)
apply(simp add:cut_memory_aux.simps)
apply(auto)
apply(subst cut_memory_aux)
apply(auto)
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
apply(simp add: cut_memory_aux.simps cut_memory_def cut_memory_aux_alt_eqv)
done

(*
lemma cut_memory_cons0 :
  "(cut_memory b (n + 1) m = a # lst) =
   (n + 1 \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) n m = lst)"
apply(auto simp add: cut_memory_head cut_memory_tail)
apply(simp add: cut_memory_aux.simps cut_memory_def)
apply(cases "unat n")
apply(cases "unat (n+1)")
apply(simp add: cut_memory_aux.simps cut_memory_def)
  using unat_eq_zero apply auto[1]
apply(simp add: cut_memory_aux.simps cut_memory_def)

done

lemma cut_memory_cons1 :
  "(cut_memory b (n - 1 + 1) m = a # lst) =
   (n \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) (n - 1) m = lst)"
apply(simp only: cut_memory_cons0)
apply(simp)
done
*)

lemma cut_memory_aux_cons [simp] :
  "(cut_memory_aux b (Suc n) m = a # lst) =
   (m b = a \<and> cut_memory_aux (b + 1) n m = lst)"
apply(simp add: cut_memory_aux.simps cut_memory_def)
done

lemma unat_minus_one2 : "unat x = Suc n \<Longrightarrow> unat (x - 1) = n"
  by (metis diff_Suc_1 nat.simps(3) unat_eq_zero unat_minus_one)

lemma cut_memory_cons [simp] :
  "(cut_memory b n m = a # lst) =
   (n \<noteq> 0 \<and> m b = a \<and> cut_memory (b + 1) (n - 1) m = lst)"
apply(auto simp:cut_memory_def cut_memory_aux.simps cut_memory_aux_alt_eqv)
apply(cases "unat n", auto simp:cut_memory_aux.simps)
apply(cases "unat n", auto simp:cut_memory_aux.simps unat_minus_one)
apply(cases "unat n", auto simp:cut_memory_aux.simps)
apply (metis diff_Suc_1 nat.simps(3) unat_eq_zero unat_minus_one)
apply(cases "unat n", auto simp:cut_memory_aux.simps)
apply (metis unat_eq_zero )
done

(*
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
*)

lemma sep_memory8 :
  "(rest ** memory8 b a) s ==
   MemoryElm (b, a) \<in> s \<and> rest (s - {MemoryElm (b,a)})"
apply (rule eq_reflection)
apply (solve_sep_iff simp: memory8_def)
done

lemma memory8_short
 :"      (memory8 b a ** rest)
        (instruction_result_as_set c (InstructionContinue v)) \<Longrightarrow>
       vctx_memory v b = a"
apply(simp add: sep_memory8)
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

lemma memory_range_cons :
"(memory_range b (a # lst) ** rest) s = (memory8 b a ** memory_range (b + 1) lst ** rest) s"
 apply (simp only: memory_range.simps sep_conj_ac)
done

declare Hoare.memory8_sep [simp del]
declare sep_memory8_sep [simp del]

lemma cut_memory_memory_range :
  "\<forall> rest b n.
   unat n = length lst \<longrightarrow>
   (memory_range b lst ** rest) (instruction_result_as_set c (InstructionContinue v))
   \<longrightarrow> cut_memory b n (vctx_memory v) = lst"
apply(induction lst)
 apply(simp add: unat_eq_0)
apply(auto simp add: memory_range_cons memory8_short)
 apply(rule memory8_short2)
 apply (sep_cancel)
apply(drule_tac x = "memory8 b a ** rest" in spec)
apply(drule_tac x = "b + 1" in spec)
apply(drule_tac x = "n - 1" in spec)
apply(auto)
apply(drule unat_suc)
apply blast
apply (simp add: sep_conj_ac)
done


declare Hoare.memory8_sep [simp]
declare sep_memory8_sep [simp]



(****** specifying each instruction *******)

lemmas simp_for_triples =
        meter_gas_def
        C_def Cmem_def
        Gmemory_def
        new_memory_consumption.simps
        thirdComponentOfC_def
        subtract_gas.simps
        vctx_next_instruction_default_def
        stack_2_1_op_def
        stack_1_1_op_def
        stack_0_0_op_def
        inst_stack_numbers.simps
        arith_inst_numbers.simps
        program_sem.simps
        vctx_next_instruction_def
        instruction_sem_def
        check_resources_def
        info_inst_numbers.simps
        Gbalance_def
        stack_inst_numbers.simps
        pc_inst_numbers.simps
        pop_def
        jump_def
        jumpi_def
        instruction_failure_result_def
        strict_if_def
        blocked_jump_def
        blockedInstructionContinue_def
        vctx_pop_stack_def
        stack_0_1_op_def
        general_dup_def
        dup_inst_numbers_def
        storage_inst_numbers.simps
        Gbase_def
        Gsreset_def

lemma emp_sep [simp] :
  "(emp ** rest) s = rest s"
apply(simp add: emp_def sep_basic_simps)
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
 apply(simp add: emp_def sep_set_conv)
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
"   unat (len_word :: w256) = length input \<longrightarrow>
       (memory_range begin_word input ** rest) s =
       ((memory_range_elms begin_word input \<subseteq> s) \<and> rest (s - memory_range_elms begin_word input)) 
"
  apply(induction input arbitrary: begin_word s len_word rest)
   apply clarsimp
  apply (clarsimp simp: sep_conj_ac)
  apply (drule_tac x="begin_word + 1" in meta_spec)
  apply (drule_tac x="s - {MemoryElm (begin_word, a)}" in meta_spec)
  apply (drule_tac x="len_word -1" in meta_spec)
  apply (drule_tac x=rest in meta_spec)
  apply (erule impE)
   apply (fastforce simp: unat_arith_simps)
  apply clarsimp
  apply (rule iffI)
    apply (rule conjI)
     apply (auto simp add: sep_basic_simps )[1]
   apply clarsimp
    apply (rule conjI)
    apply (auto simp add: sep_basic_simps )[1]
   apply (simp add: set_diff_eq)
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply (simp add: set_diff_eq)
 done
    
lemma sep_memory_range :
"  \<forall> begin_word len_word rest s.
       unat (len_word :: w256) = length input \<longrightarrow>
       (rest ** memory_range begin_word input) s =
       ((memory_range_elms begin_word input \<subseteq> s) \<and> rest (s - memory_range_elms begin_word input)) 
"
 by (metis sep_conj_commute memory_range_sep)

lemma account_existence_sep :
"(account_existence a b ** R) s =
 ( AccountExistenceElm (a, b) \<in> s \<and> R (s - {AccountExistenceElm (a, b)}))"
by (solve_sep_iff simp: account_existence_def)

lemma sep_account_existence_sep :
"(p ** account_existence a b ** q) s =
 ( AccountExistenceElm (a, b) \<in> s \<and> (p ** q) (s - {AccountExistenceElm (a, b)}))"
  apply (subst sep_conj_commute)
  apply (subst sep_conj_assoc)
  apply (subst account_existence_sep)
  apply (simp only: sep_conj_commute)
  done

lemma sep_sep_account_existence_sep :
"(n ** p ** account_existence a b ** q) s =
 ( AccountExistenceElm (a, b) \<in> s \<and> (n ** p ** q) (s - {AccountExistenceElm (a, b)}))"
proof -
  have "(n ** p ** account_existence a b ** q) s = ((n ** p) ** account_existence a b ** q) s"
    by (auto simp: sep_conj_ac)
  moreover have "((n ** p) ** account_existence a b ** q) s =
    ( AccountExistenceElm (a, b) \<in> s \<and> ((n ** p) ** q) (s - {AccountExistenceElm (a, b)}))"
    by (rule "sep_account_existence_sep")
  moreover have "( AccountExistenceElm (a, b) \<in> s \<and> ((n ** p) ** q) (s - {AccountExistenceElm (a, b)})) =
     ( AccountExistenceElm (a, b) \<in> s \<and> (n ** p ** q) (s - {AccountExistenceElm (a, b)}))"
    by (auto simp: sep_conj_ac)
  ultimately show ?thesis
    by auto
qed




lemma sep_account_existence :
"(p ** account_existence a b ) s =
 ( AccountExistenceElm (a, b) \<in> s \<and> p (s - {AccountExistenceElm (a, b)}))"
  apply (subst sep_conj_commute)
  apply (simp only: account_existence_sep)
 done

lemma sep_memory_range_sep :
"unat (len_word :: w256) = length input \<Longrightarrow>
 (a ** memory_range begin_word input ** rest) s =
 ((memory_range_elms begin_word input \<subseteq> s) \<and> (a ** rest) (s - memory_range_elms begin_word input)) 
"
  apply (subst sep_conj_commute)
  apply (subst sep_conj_assoc)
  apply (subst memory_range_sep[rule_format], assumption)
  apply (simp add: sep_conj_commute)
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

declare meter_gas_def [simp del]
declare misc_inst_numbers.simps [simp]

definition triple_alt ::
 "network \<Rightarrow> failure_reason set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> (int * inst) set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "triple_alt net allowed_failures pre insts post ==
    \<forall> co_ctx presult rest stopper.
       (code insts ** pre ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k.
         ((post ** code insts ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)))
         \<or> failed_for_reasons allowed_failures (program_sem stopper co_ctx k net presult))"

lemma code_ac :
  "(code c ** pre ** rest) s =
   (pre ** code c ** rest) s"
by simp

lemma triple_triple_alt :
  "triple net s pre c post = triple_alt net s pre c post"
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
  apply (rule iffI)
  apply (clarsimp simp add: sep_basic_simps stack_topmost_def set_diff_eq)
    apply (erule back_subst[where P=rest])
   apply blast
  apply clarsimp
  apply (clarsimp simp add: sep_basic_simps stack_topmost_def set_diff_eq)
  apply (exI_pick_last_conj)
  done

lemma sep_stack_topmost :
  "(rest ** stack_topmost h lst) s =
   (stack_topmost_elms h lst \<subseteq> s \<and> rest (s - stack_topmost_elms h lst))"
 by (rule iffI ; sep_simp simp: stack_topmost_sep)

lemma fourth_stack_topmost [simp] :
  "(a ** b ** c ** stack_topmost h lst ** rest) s =
   (stack_topmost_elms h lst \<subseteq> s \<and> (a ** b ** c ** rest) (s - stack_topmost_elms h lst))"
  by (rule iffI ; sep_simp simp: stack_topmost_sep)

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

lemma account_ex_is_not_memory_range [simp] :
  "\<forall> in_begin. AccountExistenceElm p \<notin> memory_range_elms in_begin input"
apply(induction input)
 apply(simp add: memory_range_elms.simps)
apply(simp add: memory_range_elms.simps)
done

lemma memory_range_elms_not_account_existence [simp] :
  "(memory_range_elms in_begin input \<subseteq> s - {AccountExistenceElm p}) =
   (memory_range_elms in_begin input \<subseteq> s)"
apply auto
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
  "\<forall> h. PcElm p \<notin> stack_topmost_elms h lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma stack_topmost_not_pc [simp] :
  "\<forall> h. stack_topmost_elms h lst
       \<subseteq> s - {PcElm (vctx_pc x1)} =
     (stack_topmost_elms h lst \<subseteq> s)"
 by auto
    
lemma ae_not_stack_topmost [simp] :
 "\<forall> h. AccountExistenceElm p \<notin> stack_topmost_elms h lst"
 by(induction lst; auto simp add: stack_topmost_elms.simps)

lemma stack_topmost_not_account_existence [simp] :
  "\<forall> h. stack_topmost_elms h lst
       \<subseteq> s - {AccountExistenceElm p} =
     (stack_topmost_elms h lst \<subseteq> s)"
 by (auto)



lemma stack_topmost_not_code [simp] :
  "\<forall> h. stack_topmost_elms h lst
       \<subseteq> s - {CodeElm (vctx_pc x1, Misc CALL)} =
     (stack_topmost_elms h lst \<subseteq> s)"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma memory_usage_not_in_memory_range [simp] :
"MemoryUsageElm x8
       \<in> memory_range_elms in_begin
           input \<Longrightarrow> False"
apply (induction input arbitrary:in_begin)
apply (auto simp:memory_range_elms.simps)
done


lemma stack_height_after_call [simp] :
       "vctx_balance x1 (cctx_this co_ctx) \<ge> vctx_stack x1 ! 2 \<Longrightarrow>
        (StackHeightElm (h + 7) \<in>
          instruction_result_as_set co_ctx (InstructionContinue x1)) \<Longrightarrow>
        (StackHeightElm h
          \<in> instruction_result_as_set co_ctx (subtract_gas g memu (call net x1 co_ctx)))
        "
apply(simp add: call_def)
apply(case_tac "vctx_stack x1"; simp)
apply(case_tac list; simp)
apply(case_tac lista; simp)
apply(case_tac listb; simp)
apply(case_tac listc; simp)
apply(case_tac listd; simp)
apply(case_tac liste; simp)
  apply(auto simp add: instruction_result_as_set_def
simp_for_triples)
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

lemma this_not_topmost [simp] :
  "\<forall> h. ThisAccountElm pair \<notin> stack_topmost_elms h lst"
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

lemma gas_not_topmost [simp] :
  "\<forall> h. GasElm pair \<notin> stack_topmost_elms h lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done


lemma call_new_balance [simp] :
      "v \<le> fund \<Longrightarrow>
       ThisAccountElm this \<in> instruction_result_as_set co_ctx (InstructionContinue x1) \<Longrightarrow>
       vctx_balance x1 this = fund \<Longrightarrow>
       meter_gas (Misc CALL) x1 co_ctx net \<le> vctx_gas x1 \<Longrightarrow>
       vctx_stack x1 = g # r # v # in_begin # in_size # out_begin # out_size # tf \<Longrightarrow>
       BalanceElm (this, fund - v)
       \<in> instruction_result_as_set co_ctx
           (subtract_gas (meter_gas (Misc CALL) x1 co_ctx net) memu (call net x1 co_ctx))"
apply(clarify)
apply(auto simp add: call_def failed_for_reasons_def)
apply(simp add: instruction_result_as_set_def subtract_gas.simps strict_if_def)
apply(case_tac "vctx_balance x1 (cctx_this co_ctx) < v")
 apply(simp add: update_balance_def)
apply(simp add: strict_if_def subtract_gas.simps update_balance_def)
done


lemma advance_pc_call [simp] :
      "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Misc CALL) \<Longrightarrow>
       k = vctx_pc x1 \<Longrightarrow>
       vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
  apply(simp add: vctx_advance_pc_def inst_size_def inst_code.simps
                 simp_for_triples)
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
 apply(simp add: stack_topmost_elms.simps)
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

lemma lognum_not_memory [simp] :
  "\<forall> x6 in_begin. LogNumElm x6 \<notin> memory_range_elms in_begin input"
apply(induction input)
 apply(simp add: memory_range_elms.simps)
apply(simp add: memory_range_elms.simps)
done

lemma account_existence_not_memory [simp] :
  "\<forall> in_begin. AccountExistenceElm x29 \<notin> memory_range_elms in_begin input"
apply(induction input)
 apply(simp add: memory_range_elms.simps)
apply(simp add: memory_range_elms.simps)
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
notes simp_for_triples[simp]
shows
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
   x \<in> instruction_result_as_set co_ctx
         (subtract_gas (meter_gas (Misc CALL) x1 co_ctx net) memu (call net x1 co_ctx)) =
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
notes simp_for_triples[simp]
shows
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
    x \<in> instruction_result_as_set co_ctx (call net x1 co_ctx) =
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

lemma fourth_last_pure [simp] :
"(a ** b ** c ** \<langle> P \<rangle>) s =
 (P \<and> (a ** b ** c) s)"
	by (metis get_pure sep_three)

lemma lookup_over4':
  "(listf @ a # b # c # d # e # rest) ! Suc (Suc (Suc (Suc (length listf))))
   = e"
   (is "?app ! ?idx = e")
proof -
  have "?idx = length listf + 4"
    by auto
  then have "?app ! ?idx = ?app ! (length listf + 4)"
    by (simp add: \<open>Suc (Suc (Suc (Suc (length listf)))) = length listf + 4\<close>)
  moreover have "?app ! (length listf + 4) = (a # b # c # d # e # rest) ! 4"
    by (rule nth_append_length_plus)
  ultimately have "?app ! ?idx = (a # b # c # d # e # rest) ! 4"
    by auto
  then show ?thesis
    by simp
qed

lemma lookup_over_suc [simp] :
  "n \<ge> length lst \<Longrightarrow> (rev lst @ a # rest) ! Suc n = (rev lst @ rest) ! n"
proof -
  assume "n \<ge> length lst"
  then have "n = length lst + (n - length lst)"
    by simp
  then have " (rev lst @ a # rest) ! Suc n =  (rev lst @ a # rest) ! (length lst + Suc (n - length lst))"
    by simp
  moreover have "(rev lst @ a # rest) ! (length lst + Suc (n - length lst)) = (rev lst @ a # rest) ! (length (rev lst) + Suc (n - length lst))"
    by simp
  moreover have "(rev lst @ a # rest) ! (length (rev lst) + Suc (n - length lst)) = (a # rest) ! Suc (n - length lst)"
    by (rule nth_append_length_plus)
  ultimately have "(rev lst @ a # rest) ! Suc n = (a # rest) ! Suc (n - length lst)"
    by auto
  moreover have "(a # rest) ! Suc (n - length lst) = rest ! (n - length lst)"
    by auto
  ultimately have " (rev lst @ a # rest) ! Suc n = rest ! (n - length lst)"
    by simp
  moreover assume "n \<ge> length lst"
  then have "n = length lst + (n - length lst)"
    by simp
  then have "(rev lst @ rest) ! n = (rev lst @ rest) ! (length lst + (n - length lst))"
    by simp
  then have "(rev lst @ rest) ! n = (rev lst @ rest) ! (length (rev lst) + (n - length lst))"
    by simp
  moreover have "(rev lst @ rest) ! (length (rev lst) + (n - length lst)) = rest ! (n - length lst)"
    by (rule nth_append_length_plus)
  ultimately show ?thesis
    by auto
qed
  

lemma lookup_over4 [simp]:
  "(rev listf @ a # b # c # d # e # rest) ! Suc (Suc (Suc (Suc (length listf))))
   = e"
apply(simp)
done

lemma lookup_over3 [simp] :
  "(rev listf @ a # b # c # d # lst) ! Suc (Suc (Suc (length listf))) = d"
apply(simp)
done


lemma memory_range_elms_in_minus_this [simp] :
  "memory_range_elms in_begin input
       \<subseteq> X - {ThisAccountElm t} =
   (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done

lemma memory_range_elms_in_minus_stackheight [simp] :
  "memory_range_elms in_begin input
       \<subseteq> X - {StackHeightElm h} =
   (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done

lemma memory_range_elms_in_minus_continuing [simp] :
  "memory_range_elms in_begin input
       \<subseteq> X - {ContinuingElm b} =
   (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done

lemma memory_range_elms_in_minus_gas [simp] :
  "memory_range_elms in_begin input
       \<subseteq> X - {GasElm b} =
   (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done

lemma log_not_memory_range [simp] :
  "\<forall> in_begin. LogElm x5 \<notin> memory_range_elms in_begin input"
apply(induction input; auto simp add: memory_range_elms.simps)
done

lemma caller_not_memory_range [simp] :
  "\<forall> in_begin. CallerElm x5 \<notin> memory_range_elms in_begin input"
apply(induction input; auto simp add: memory_range_elms.simps)
done

lemma origin_not_memory_range [simp] :
  "\<forall> in_begin. OriginElm x5 \<notin> memory_range_elms in_begin input"
apply(induction input; auto simp add: memory_range_elms.simps)
done

lemma sent_value_not_memory_range [simp] :
  "\<forall> in_begin. SentValueElm x5 \<notin> memory_range_elms in_begin input"
apply(induction input; auto simp add: memory_range_elms.simps)
done

lemma sent_data_length_not_memory_range [simp] :
  "\<forall> in_begin. SentDataLengthElm x5 \<notin> memory_range_elms in_begin input"
apply(induction input; auto simp add: memory_range_elms.simps)
done



lemma memory_range_elms_in_insert_continuing [simp] :
  "(memory_range_elms in_begin input
   \<subseteq> insert (ContinuingElm b) X) =
  (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done

lemma memory_range_elms_in_insert_contract_action [simp] :
  "(memory_range_elms in_begin input
   \<subseteq> insert (ContractActionElm b) X) =
  (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done


lemma memory_range_elms_in_insert_gas [simp] :
  "(memory_range_elms in_begin input
   \<subseteq> insert (GasElm b) X) =
  (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done

lemma memory_range_elms_in_minus_stack [simp]:
  "memory_range_elms in_begin input
       \<subseteq> X -
          { StackElm pair } =
  (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma minus_h [simp] :
  "x - {a, b, c, d, e, f, g, h} = 
   x - {a} - {b} - {c} - {d} - {e} - {f} - {g} - {h}"
apply auto
done

lemma stack_topmost_in_minus_balance [simp] :
  "stack_topmost_elms h lst \<subseteq> X - {BalanceElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
apply auto
done

lemma stack_topmost_in_minus_this [simp] :
  "stack_topmost_elms h lst \<subseteq> X - {ThisAccountElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto)


lemma stack_topmost_in_minus_pc [simp] :
  "stack_topmost_elms h lst \<subseteq> X - {PcElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
apply auto
done

lemma stack_topmost_in_minus_memoryusage [simp] :
  "stack_topmost_elms h lst \<subseteq> X - {MemoryUsageElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
apply auto
done

lemma stack_topmost_in_minus_gas [simp] :
  "stack_topmost_elms h lst \<subseteq> X - {GasElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
apply auto
done

lemma stack_topmost_in_minus_continuing [simp] :
  "stack_topmost_elms h lst \<subseteq> X - {ContinuingElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
apply auto
done

lemma stack_topmost_in_insert_cont [simp] :
  "stack_topmost_elms l lst \<subseteq> insert (ContinuingElm b) X =
   (stack_topmost_elms l lst \<subseteq> X)"
apply auto
done

lemma contract_action_not_stack_topmost [simp] :
  "\<forall> l. ContractActionElm x19 \<notin> stack_topmost_elms l lst"
apply(induction lst; auto simp add: stack_topmost_elms.simps)
done

lemma stack_topmost_in_insert_contractaction [simp] :
  "stack_topmost_elms l lst \<subseteq> insert (ContractActionElm a) X =
   (stack_topmost_elms l lst \<subseteq> X)"
apply auto
done

lemma stack_topmost_in_insert_gas [simp] :
  "stack_topmost_elms l lst \<subseteq> insert (GasElm a) X =
   (stack_topmost_elms l lst \<subseteq> X)"
apply auto
done


lemma lognum_not_program [simp] :
 "LogNumElm x6 \<notin> program_as_set p"
apply(simp add: program_as_set_def)
done

lemma lognum_not_constant [simp] :
  "LogNumElm x6 \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def)
done

lemma stack_topmost_not_constant [simp]:
  "elm \<in> stack_topmost_elms h lst \<Longrightarrow> elm \<notin> constant_ctx_as_set c"
apply(case_tac elm; simp)
done

lemma stack_topmost_in_c [simp] :
  "stack_topmost_elms h lst
       \<subseteq> contexts_as_set v c =
   (stack_topmost_elms h lst \<subseteq> variable_ctx_as_set v)"
apply (auto simp add: contexts_as_set_def)
done 

lemma ppq :
  "(P = (P \<and> Q)) = (P \<longrightarrow> Q)"
apply(case_tac Q; simp)
done

lemma drop_eq_cons_when :
  "\<forall> a orig.
     a = orig ! h \<longrightarrow> h < length orig \<longrightarrow> lst = drop (Suc h) orig \<longrightarrow> drop h orig = orig ! h # drop (Suc h) orig"
apply(induction h)
 apply(clarify)
 apply(case_tac orig; auto)
apply(simp)
apply(clarify)
apply(case_tac orig; auto)
done


lemma drop_cons :
  "(drop h orig = a # lst) = 
   (orig ! h = a \<and> drop (Suc h) orig = lst \<and> length orig > h)"
apply(auto)
   apply (simp add: nth_via_drop)
  apply(simp only: drop_suc)
  apply(simp)
 using not_less apply fastforce
by (simp add: drop_eq_cons_when)

lemma topmost_elms_in_vctx_means [simp]:
  "\<forall> h v. stack_topmost_elms h lst
       \<subseteq> variable_ctx_as_set v =
  ((length (vctx_stack v) = h + length lst \<and> drop h (rev (vctx_stack v)) = lst))"
apply(induction lst; simp)
 apply(simp add: stack_topmost_elms.simps ppq)
apply(rule allI)
apply(rule allI)
apply(simp only: stack_topmost_elms.simps)
apply(simp add: drop_cons)
apply blast
done

lemma memory_range_not_stack_topmost [simp]:
  "x \<in> memory_range_elms in_begin input \<Longrightarrow> x \<notin> stack_topmost_elms h lst"
  by (case_tac x; simp)

lemma memory_range_elms_in_minus_statck_topmost [simp] :
  "memory_range_elms in_begin input
       \<subseteq> X -
          stack_topmost_elms h lst =
   (memory_range_elms in_begin input \<subseteq> X)"
by(auto)

lemma memory_range_elms_in_c [simp] :
  "memory_range_elms in_begin input
       \<subseteq> contexts_as_set v c =
  (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
apply(auto simp add: contexts_as_set_def)
done

lemma memory_usage_not_ext_program [simp] :
  "MemoryUsageElm u \<notin> ext_program_as_set e"
apply(simp add: ext_program_as_set_def)
done

lemma memory_usage_not_balance [simp] :
  "MemoryUsageElm u \<notin> balance_as_set b"
apply(simp add: balance_as_set_def)
done

lemma variable_ctx_as_set_updte_mu [simp] :
  "variable_ctx_as_set (v\<lparr>vctx_memory_usage := u\<rparr>) =
   variable_ctx_as_set v - {MemoryUsageElm (vctx_memory_usage v)} \<union> {MemoryUsageElm u}"
apply(auto simp add: variable_ctx_as_set_def)
done

lemma memory_range_elms_in_mu [simp] :
  "memory_range_elms in_begin input \<subseteq> insert (MemoryUsageElm u) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma sent_data_not_in_mr [simp] :
 "\<forall> in_begin. SentDataElm x16 \<notin> memory_range_elms in_begin input"
apply (induction input; simp add: memory_range_elms.simps)
done

lemma ext_program_not_in_mr [simp] :
  "\<forall> in_begin. ExtProgramSizeElm x17 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma ext_pr_not_in_mr[simp] :
  "\<forall> in_begin. ExtProgramElm x18 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma blockhash_not_in_mr [simp] :
  "\<forall> in_begin. BlockhashElm x21 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma blocknumber_not_in_mr [simp] :
  "\<forall> in_begin. BlockNumberElm x22 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma coinbase_not_in_mr [simp] :
  "\<forall> in_begin. 
     CoinbaseElm x23 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma timestamp_not_in_mr [simp] :
  "\<forall> in_begin. TimestampElm x24 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma difficulty_not_in_mr [simp] :
"\<forall> in_begin. DifficultyElm x25 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma gaslimit_not_in_mr [simp] :
"\<forall> in_begin. GaslimitElm x26 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma gasprice_not_in_mr [simp] :
  "\<forall> in_begin. GaspriceElm x27 \<notin> memory_range_elms in_begin input"
apply(induction input; simp add: memory_range_elms.simps)
done

lemma memory_range_elms_in_minus_mu [simp] :
  "memory_range_elms in_begin input \<subseteq> X - {MemoryUsageElm u} =
  (memory_range_elms in_begin input \<subseteq> X)"
apply auto
done


lemma memory_range_elms_update_memory_usage [simp] :
  "memory_range_elms in_begin input \<subseteq>
    variable_ctx_as_set
           (v\<lparr>vctx_memory_usage := u\<rparr>) =
   (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
apply(simp)
done

lemma memory_range_in_caller [simp] :
  "memory_range_elms in_begin input
     \<subseteq> insert (CallerElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma memory_range_in_sent_value [simp] :
  "memory_range_elms in_begin input
     \<subseteq> insert (SentValueElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma memory_range_in_origin [simp] :
  "memory_range_elms in_begin input
     \<subseteq> insert (OriginElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma memory_range_in_pc [simp] :
  "memory_range_elms in_begin input
     \<subseteq> insert (PcElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done


lemma memory_range_in_sd [simp] :
  "memory_range_elms in_begin input
     \<subseteq> insert (SentDataLengthElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma memory_range_in_coinbase [simp] :
  "memory_range_elms in_begin input
     \<subseteq> insert (CoinbaseElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
apply(auto)
done

lemma vset_update_balance [simp] :
  "variable_ctx_as_set
           (v\<lparr>vctx_balance := u\<rparr>) =
   variable_ctx_as_set v - balance_as_set (vctx_balance v) \<union> balance_as_set u"
apply(auto simp add: variable_ctx_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma memory_range_elms_update_balance [simp] :
  "memory_range_elms in_begin input \<subseteq>
    variable_ctx_as_set
           (v\<lparr>vctx_balance := u\<rparr>) =
   (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
apply(auto simp add: balance_as_set_def)
done

lemma small_min [simp] :
  "Suc n < h \<Longrightarrow>
   min (h - Suc 0) n = n"
apply auto
done

lemma sucsuc_minus_two [simp] :
  "h > 1 \<Longrightarrow>
   Suc (Suc (h - 2)) = h"
apply auto
done

lemma swap_advance [simp] :
 "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Swap n) \<Longrightarrow>
  vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: simp_for_triples vctx_advance_pc_def inst_size_def inst_code.simps)
done

lemma minus_one_bigger [simp] :
  "h > 1 \<Longrightarrow>
   h - Suc (Suc n) \<noteq> h - Suc 0"
apply auto
done

lemma storage_elm_kept_by_gas_update [simp]:
 "StorageElm x3
  \<in> instruction_result_as_set co_ctx (InstructionContinue
     (x1\<lparr>vctx_gas := g - Gverylow\<rparr>)) =
  (StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: simp_for_triples instruction_result_as_set_def)
done

lemma storage_elm_kept_by_stack_updaate [simp] :
  "StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue (x1\<lparr>vctx_stack := s\<rparr>))
 = (StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: instruction_result_as_set_def)
done

lemma advance_pc_keeps_storage_elm [simp] :
  "StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue (vctx_advance_pc co_ctx x1)) =
  (StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: instruction_result_as_set_def)
done

lemma rev_drop [simp] :
"a < length lst - n \<Longrightarrow>
 rev (drop n lst) ! a = rev lst ! a"
	by (simp add: rev_drop)

lemma less_than_minus_two [simp] :
  "1 < h \<Longrightarrow>
   a < h - Suc (Suc (unat n)) \<Longrightarrow> a < Suc (h - 2)"
apply auto
done

lemma suc_minus_two [simp] :
  "1 < h \<Longrightarrow>
   Suc (h - 2) = h - Suc 0"
apply auto
done

lemma minus_one_two [simp] :
 "1 < h \<Longrightarrow>
  h - Suc 0 \<noteq> h - Suc (Suc n)"
apply auto
done

lemma minus_two_or_less [simp] :
  "a < h - Suc n \<Longrightarrow>  a < h - Suc 0"
apply auto
done

lemma min_right [simp] :
 "(n :: nat) \<le> m \<Longrightarrow> min m n = n"
apply (simp add: min_def)
done


lemma rev_take_nth [simp] :
  "n \<le> length lst \<Longrightarrow>
   k < n \<Longrightarrow>
   rev (take n lst) ! k =  lst ! (n - k - 1)"
apply(simp add: List.rev_nth)
done

lemma stack_topmost_in_insert_memory_usage [simp] :
  "stack_topmost_elms h lst
       \<subseteq> insert (MemoryUsageElm u) X =
  (stack_topmost_elms h lst \<subseteq> X)"
apply(auto)
done

lemma memory_gane_elms_in_stack_update [simp] :
  "memory_range_elms in_begin input \<subseteq> variable_ctx_as_set (v\<lparr>vctx_stack := tf\<rparr>) =
  (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
apply(auto)
done

lemma stack_topmost_in_minus_balance_as [simp] :
  "stack_topmost_elms h lst
       \<subseteq> X - balance_as_set b =
  (stack_topmost_elms h lst \<subseteq> X)"
apply(auto simp add: balance_as_set_def)
done

lemma stack_topmost_in_union_balance [simp] :
  "stack_topmost_elms h lst
       \<subseteq> X \<union> balance_as_set b =
  (stack_topmost_elms h lst \<subseteq> X)"
apply(auto simp add: balance_as_set_def)
done

lemma memory_range_in_minus_balance_as [simp] :
  "memory_range_elms h lst
       \<subseteq> X - balance_as_set b =
  (memory_range_elms h lst \<subseteq> X)"
apply(auto simp add: balance_as_set_def)
done

lemma memory_range_in_union_balance [simp] :
  "memory_range_elms h lst
       \<subseteq> X \<union> balance_as_set b =
  (memory_range_elms h lst \<subseteq> X)"
apply(auto simp add: balance_as_set_def)
done

lemma memory_range_in_minus_balance [simp] :
  "memory_range_elms h lst
    \<subseteq> X - {BalanceElm pair} =
   (memory_range_elms h lst \<subseteq> X)"
apply(auto)
done

lemma memory_range_advance [simp] :
  "memory_range_elms in_begin input \<subseteq> variable_ctx_as_set (vctx_advance_pc co_ctx x1) =
  (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set x1)"
apply(auto)
done

lemma update_balance_match [simp] :
  "update_balance a f b a = f (b a)"
apply(simp add: update_balance_def)
done 

lemma lookup_o [simp]:
  "a \<ge> length tf \<Longrightarrow>
   (rev tf @ lst) ! a
   = lst ! (a - length tf)"
	by (simp add: rev_append_eq)

lemma update_balance_no_change [simp] :
  "update_balance changed f original a = original a =
   (changed \<noteq> a \<or> (changed = a \<and> f (original a) = original a))"
apply(auto simp add: update_balance_def)
done

lemma update_balance_changed [simp] :
  "original a \<noteq> update_balance changed f original a =
  (changed = a \<and> f (original a) \<noteq> original a)"
apply(auto simp add: update_balance_def)
done


lemma rev_append_look_up [simp] :
  "(rev ta @ lst) ! pos = val =
   ((pos < length ta \<and> rev ta ! pos = val) \<or>
    (length ta \<le> pos \<and> lst ! (pos - length ta) = val))"
apply (simp add: nth_append)
done

lemma pair_snd_eq [simp] : 
 "x3 \<noteq> (idx, snd x3) =
  (fst x3 \<noteq> idx)"
apply (case_tac x3; auto)
done


lemma log_num_memory_usage [simp] :
  "LogNumElm x6
       \<in> contexts_as_set
           (v
            \<lparr> vctx_memory_usage := m \<rparr>) co_ctx =
   (LogNumElm x6 \<in> contexts_as_set v co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma log_num_not_balance [simp] :
  "LogNumElm x6 \<notin> balance_as_set b"
apply(simp add: balance_as_set_def)
done

lemma log_num_balance_update [simp] :
  "LogNumElm x6
       \<in> contexts_as_set
           (v \<lparr>vctx_balance := b\<rparr>) co_ctx =
   (LogNumElm x6 \<in> contexts_as_set v co_ctx)"
apply(simp add: contexts_as_set_def)
done

lemma log_num_not_stack_topmost [simp] :
  "\<forall> n. LogNumElm x6 \<notin> stack_topmost_elms n lst"
apply(induction lst)
 apply(simp add: stack_topmost_elms.simps)
apply(simp add: stack_topmost_elms.simps)
done

lemma log_num_not_stack [simp] :
  "LogNumElm x6 \<notin> stack_as_set tf"
apply(simp add: stack_as_set_def)
done

lemma contract_action_not_vctx [simp] :
  "ContractActionElm x19 \<notin> variable_ctx_as_set x1"
apply(simp add: variable_ctx_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma continuing_not_vctx [simp] :
  "ContinuingElm b \<notin> variable_ctx_as_set v"
apply(simp add: variable_ctx_as_set_def ext_program_as_set_def balance_as_set_def)
done

lemma log_num_not_ext_program [simp] :
  "LogNumElm x6 \<notin> ext_program_as_set e"
apply(simp add: ext_program_as_set_def)
done

lemma log_num_elm_means [simp] :
  "LogNumElm x6 \<in> contexts_as_set x1 co_ctx =
   (length (vctx_logs x1) = x6)"
apply(simp add: contexts_as_set_def)
apply(auto simp add: variable_ctx_as_set_def)
done



lemma log_num_in_v_means [simp] :
 "LogNumElm x6 \<in> variable_ctx_as_set v =
  (length (vctx_logs v) = x6)"
apply(simp add: variable_ctx_as_set_def)
apply auto
done

lemma account_existence_means_v [simp] :
  "AccountExistenceElm x29 \<in> variable_ctx_as_set v =
   (vctx_account_existence v (fst x29) = snd x29)"
apply(auto simp add: variable_ctx_as_set_def)
 apply(rule_tac x = "fst x29" in exI)
 apply(case_tac x29)
 apply simp
apply(rule_tac x = "fst x29" in exI)
apply(case_tac x29)
apply simp
done

lemma account_existence_not_stack [simp] :
  "AccountExistenceElm p \<notin> stack_as_set ta"
apply(simp add: stack_as_set_def)
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

lemma lognum_not_stack_topmost [simp] :
  "LogNumElm n \<notin> stack_topmost_elms h lst"
apply(simp add: stack_topmost_elms.simps)
done

lemma stack_topmost_minus_lognum [simp] :
   "stack_topmost_elms h lst \<subseteq> X - {LogNumElm n} =
   (stack_topmost_elms h lst \<subseteq> X)"
apply auto
done

lemma vctx_pc_log_advance [simp] :
  "program_content (cctx_program co_ctx) k = Some (Log LOGx) \<Longrightarrow>
   vctx_pc v = k \<Longrightarrow>
   vctx_pc
     (vctx_advance_pc co_ctx v) =
   vctx_pc v + 1"
apply(simp add: simp_for_triples vctx_advance_pc_def inst_size_def inst_code.simps)
done

lemma memory_range_elms_in_x_minus_lognum [simp] :
  "memory_range_elms in_begin data \<subseteq> X - {LogNumElm n} =
   (memory_range_elms in_begin data \<subseteq> X)"
apply auto
done

lemma memory_range_elms_logs_update [simp] :
  "memory_range_elms in_begin data
             \<subseteq> variable_ctx_as_set (x1\<lparr>vctx_logs := ls\<rparr>) =
  (memory_range_elms in_begin data
             \<subseteq> variable_ctx_as_set x1)"
apply(auto simp add: variable_ctx_as_set_def)
done


lemma log0_create_logs [simp] :
   "vctx_stack x1 = logged_start # logged_size # ta  \<Longrightarrow>
    length data = unat logged_size \<Longrightarrow>
    memory_range_elms logged_start data \<subseteq> variable_ctx_as_set x1  \<Longrightarrow>
    create_log_entry 0 x1 co_ctx = \<lparr>log_addr = cctx_this co_ctx, log_topics = [], log_data = data\<rparr>"
apply(auto simp add: create_log_entry_def vctx_returned_bytes_def memory_range_elms_cut_memory)
done


lemma default_zero [simp] :
  "vctx_stack x1 = idx # ta \<Longrightarrow>
   vctx_stack_default 0 x1 = idx"
apply(simp add: vctx_stack_default_def)
done

lemma default_one [simp] :
  "vctx_stack x1 = idx # y # ta \<Longrightarrow>
   vctx_stack_default 1 x1 = y"
apply(simp add: vctx_stack_default_def)
done


lemmas sep_crunch = caller_sep
                    sep_caller
                    sep_caller_sep
                    balance_sep
                    sep_balance
                    sep_balance_sep
                    not_continuing_sep
                    sep_not_continuing_sep
                    this_account_sep
                    sep_this_account
                    sep_this_account_sep
                    action_sep
                    sep_action
                    sep_action_sep
                    sep_stack_topmost
                    sep_account_existence_sep
                    sep_account_existence
                    account_existence_sep
                    sep_sep_account_existence_sep
                    sep_conj_assoc

end
