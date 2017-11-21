theory HoareTripleForInstructions

imports Main "./Hoare"

begin
(**
 ** Hoare Triple for each instruction
 **)
lemmas as_set_simps =
  memory_as_set_def
  storage_as_set_def
  log_as_set_def
  balance_as_set_def
  next_state_def
  contract_action_as_set_def
  stack_as_set_def
  ext_program_as_set_def
  program_as_set_def
  constant_ctx_as_set_def
  variable_ctx_as_set_def
  contexts_as_set_def
  account_existence_as_set_def
  instruction_result_as_set_def

lemma continuing_not_context[simp]:
  "ContinuingElm b \<notin> contexts_as_set x32 co_ctx"
by (simp add:  as_set_simps)

lemma caller_elm_means: "
 (CallerElm x12
           \<in> variable_ctx_as_set v) =
 (x12 = vctx_caller v)"
  by (simp add:  as_set_simps)
 
lemma lst_longer [dest!]:
  "length l = Suc h \<Longrightarrow> \<exists> a t. l = a # t \<and> length t = h"
	by (simp add: length_Suc_conv)

	  
lemma rev_append  :
  "(rev l ! a \<noteq> (rev l @ l') ! a) =
   ((a \<ge> length l) \<and> (rev l) ! a \<noteq> l' ! (a - length l))"
apply(simp add: nth_append)
done

lemma rev_append_inv  :
  "((rev l @ l') ! a \<noteq> rev l ! a) =
   ((a \<ge> length l) \<and> (rev l) ! a \<noteq> l' ! (a - length l))"
apply(auto simp add: nth_append)
done

lemma rev_rev_append  :
  "((rev l @ a0) ! idx \<noteq> (rev l @ a1) ! idx)
   =
   (idx \<ge> length l \<and> a0 ! (idx - length l) \<noteq> a1 ! (idx - length l))"
apply(auto simp add: nth_append)
done

lemma over_one :
 "length lst = a \<Longrightarrow> (rev lst @ (v # l)) ! a = v"
apply(simp add: nth_append)
done

lemma over_one_rev  :
  "((rev l @ (w # x)) ! idx \<noteq> w) =
    (idx < (length l) \<and> (rev l) ! idx \<noteq> w ) \<or> ( idx > (length l) \<and> x ! (idx - length l - 1) \<noteq> w)"
apply(simp add: nth_append)
by (simp add: nth_Cons')

lemma over_one_rev'  :
  "((rev l @ [w, v]) ! idx \<noteq> w) =
    (idx < (length l) \<and> (rev l) ! idx \<noteq> w ) \<or> ( idx > (length l) \<and> [v] ! (idx - length l - 1) \<noteq> w)"
apply(auto simp add: nth_append nth_Cons')
done


lemma over_two :
 "Suc (length lst) = a \<Longrightarrow> (rev lst @ (v # w # l)) ! a = w"
apply(simp add: nth_append)
done

lemma over_two_rev  :
  "((rev l @ (w #  v # x)) ! idx \<noteq> v) =
    (idx \<le> (length l) \<and> (rev l @ [w]) ! idx \<noteq> v ) \<or> ( idx > Suc (length l) \<and> x ! (idx - length l - 2) \<noteq> v )"
apply(simp add: nth_append)
(* sledgehammer *)
by (metis Suc_diff_Suc diff_self_eq_0 less_antisym linorder_neqE_nat nth_Cons_0 nth_Cons_Suc)


lemma rev_append_look_up  :
  "(rev ta @ lst) ! pos = val =
   ((pos < length ta \<and> rev ta ! pos = val) \<or>
    (length ta \<le> pos \<and> lst ! (pos - length ta) = val))"
apply (simp add: nth_append)
done
    
lemmas rev_nth_simps =
(*   lookup_over
  lookup_over1 
  short_match*)
  rev_append
  rev_append_inv
  rev_rev_append
  over_one
  over_one_rev
  over_one_rev'
  over_two
  over_two_rev
  rev_append_look_up
	  
	  
lemma advance_pc_advance:
  " vctx_next_instruction x1 co_ctx = Some i \<Longrightarrow>
    inst_size i = 1 \<Longrightarrow>
    vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def)
done

lemma advance_pc_no_gas_change:
  "vctx_gas (vctx_advance_pc co_ctx x1) = vctx_gas x1"
apply(simp add: vctx_advance_pc_def)
done

lemma constant_diff_stack_height:
 "constant_ctx_as_set co_ctx - {StackHeightElm h} = constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps)

lemma constant_diff_stack :
 "constant_ctx_as_set co_ctx - {StackElm s} = constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps)

lemma constant_diff_pc :
 "constant_ctx_as_set co_ctx - {PcElm p} =
  constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps)

lemma constant_diff_gas:
 "constant_ctx_as_set co_ctx - {GasElm g} =
  constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps)

lemma stack_height_element_means:
 "(StackHeightElm h \<in> variable_ctx_as_set v) =
  (length (vctx_stack v) = h)
 "
by (auto simp add: as_set_simps)

lemma stack_element_means:
 "(StackElm pw \<in> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) = (snd pw) \<and> (fst pw) < length (vctx_stack v))"
  by (case_tac pw; auto simp: as_set_simps)

lemma stack_element_notin_means:
 "(StackElm pw \<notin> variable_ctx_as_set v) =
  (rev (vctx_stack v) ! (fst pw) \<noteq> (snd pw) \<or> (fst pw) \<ge> length (vctx_stack v))"
  by (case_tac pw; auto simp: as_set_simps)


lemma storage_element_means :
  "StorageElm idxw \<in> variable_ctx_as_set v =
   (vctx_storage v (fst idxw) = (snd idxw))"
  by (case_tac idxw; auto simp: as_set_simps)


lemma memory_element_means:
  "MemoryElm addrw \<in> variable_ctx_as_set v =
   (vctx_memory v (fst addrw) = snd addrw)"
  by (case_tac addrw; auto simp: as_set_simps)

lemma memory_usage_element_means:
  "MemoryUsageElm m \<in> variable_ctx_as_set v =
   (vctx_memory_usage v = m)"
  by (auto simp: as_set_simps)

lemma balance_all:
  "P \<in> balance_as_set b \<Longrightarrow> P \<in> range BalanceElm"
by (fastforce simp add: balance_as_set_def)

lemma not_balance_all:
  "p \<notin> range BalanceElm \<Longrightarrow> p \<notin> balance_as_set b"
by (fastforce simp add: balance_as_set_def)

lemma pc_not_balance:
  "PcElm p \<notin> balance_as_set b"
apply(simp add: balance_as_set_def)
done


lemma pc_element_means:
  "(PcElm p \<in> variable_ctx_as_set v) =
   (vctx_pc v = p)"
 by (auto simp: as_set_simps)

lemma gas_element_means:
  "(GasElm g \<in> variable_ctx_as_set v) =
    (vctx_gas v = g)"
  by (auto simp: as_set_simps)

lemma log_element_means:
  "(LogElm p \<in> variable_ctx_as_set v) =
   (rev (vctx_logs v) ! (fst p) = (snd p) \<and> fst p < length (vctx_logs v))"
  by (case_tac p; auto simp: as_set_simps)

lemma code_element_means:
  "(CodeElm xy \<in> constant_ctx_as_set c) = 
   (program_content (cctx_program c) (fst xy) = Some (snd xy) \<or>
    program_content (cctx_program c) (fst xy) = None \<and>
    (snd xy) = Misc STOP)"
  by (case_tac xy; auto simp: as_set_simps)

lemma origin_element_means:
  "(OriginElm orig \<in> variable_ctx_as_set v) = (orig = vctx_origin v)"
  by (auto simp: as_set_simps)

lemma sent_value_means:
  "SentValueElm x14 \<in> variable_ctx_as_set x1 = (x14 = vctx_value_sent x1)"
  by (auto simp: as_set_simps)

lemma sent_data_means:
"SentDataElm p \<in> variable_ctx_as_set x1 = 
 (p = vctx_data_sent x1)"
  by (case_tac p; auto simp: as_set_simps)

lemma block_number_elm_c_means :
"BlockNumberElm x22 \<in> contexts_as_set x1 co_ctx =
 (x22 = block_number (vctx_block x1))"
by (simp add: as_set_simps)

lemma balance_elm_means :
 "BalanceElm p \<in> variable_ctx_as_set v = (vctx_balance v (fst p) = (snd p))"
  by (case_tac p; auto simp: as_set_simps)

lemma stack_as_set_cons_means:
  "x \<in> stack_as_set (w # lst) =
   (x = StackHeightElm (Suc (length lst)) \<or>
   x = StackElm (length lst, w) \<or>
   x \<in> stack_as_set lst - {StackHeightElm (length lst)})"
 by (auto simp add: as_set_simps rev_nth_simps)

lemma ext_program_size_elm_means :
   "ExtProgramSizeElm ab \<in> variable_ctx_as_set v =
    (program_length (vctx_ext_program v (fst ab)) = snd ab)"
apply(auto simp add: as_set_simps)
apply(case_tac ab; auto)
done

lemma ext_program_size_c_means :
  "ExtProgramSizeElm ab \<in> contexts_as_set v co_ctx =
   (program_length (vctx_ext_program v (fst ab)) = snd ab)"
  apply (rule iffI)
  apply(clarsimp simp add: as_set_simps )+
  apply (rule exI[where x="(fst ab)"])
    apply clarsimp
  done

lemma ext_program_elm_means   :
  "ExtProgramElm abc \<in> variable_ctx_as_set v =
   (program_as_natural_map ((vctx_ext_program v) (fst abc)) (fst (snd abc)) = (snd (snd abc)))"
apply(case_tac abc ; auto simp add: as_set_simps)
done

lemma ext_program_c_means :
  "ExtProgramElm abc \<in> contexts_as_set v co_ctx =
   (program_as_natural_map ((vctx_ext_program v) (fst abc)) (fst (snd abc)) = (snd (snd abc)))"
  by(case_tac abc, auto simp add: as_set_simps)
lemma blockhash_elm_means :
  "BlockhashElm ab \<in> variable_ctx_as_set x1 =
   (block_blockhash (vctx_block x1) (fst ab) = snd ab)"
  by(case_tac ab; auto simp add: as_set_simps vctx_advance_pc_def)

lemma blockhash_c_means :
  "BlockhashElm ab \<in> contexts_as_set x1 co_ctx =
   (block_blockhash (vctx_block x1) (fst ab) = snd ab)"
  by(case_tac ab; auto simp add: as_set_simps vctx_advance_pc_def)

lemma coinbase_elm_means :
  "CoinbaseElm v \<in> variable_ctx_as_set x2 =
   ((block_coinbase (vctx_block x2)) = v)"
  by(case_tac v; auto simp add: as_set_simps)

lemma coinbase_c_means :
  "CoinbaseElm x23 \<in> contexts_as_set x1 co_ctx =
  (block_coinbase (vctx_block x1) = x23)"
by (auto simp add: as_set_simps)

lemma timestamp_elm_means :
  "TimestampElm t \<in> variable_ctx_as_set x1 =
   (t = block_timestamp (vctx_block x1))"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma timestamp_c_means :
 "TimestampElm t \<in> contexts_as_set x1 co_ctx =
   (t = block_timestamp (vctx_block x1))"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma difficulty_elm_means :
  "DifficultyElm x24 \<in> variable_ctx_as_set x1 =
   (x24 = block_difficulty (vctx_block x1))"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma difficulty_c_means :
  "DifficultyElm x24 \<in> contexts_as_set x1 co_ctx =
   (x24 = block_difficulty (vctx_block x1))"
  by (auto simp add: as_set_simps vctx_advance_pc_def)
    
lemmas stateelm_basic_means_simps = 
  stack_height_element_means
  stack_element_means
  stack_element_notin_means
  storage_element_means
  memory_element_means
  pc_not_balance
  pc_element_means
  gas_element_means
  log_element_means
  memory_usage_element_means
  code_element_means
  origin_element_means 
  sent_value_means
  sent_data_means
  caller_elm_means
  block_number_elm_c_means
  balance_elm_means
  stack_as_set_cons_means
  ext_program_size_elm_means
  ext_program_size_c_means
  ext_program_elm_means
  ext_program_c_means
  blockhash_elm_means
  blockhash_c_means
  coinbase_elm_means
  coinbase_c_means
  timestamp_elm_means
  timestamp_c_means
  difficulty_elm_means
  difficulty_c_means

lemma inst_size_nonzero[simp]:
 "inst_size a \<noteq> 0"
apply(simp add: inst_size_def)
apply(case_tac a; auto simp add: inst_code.simps dup_inst_code_def)
apply(rename_tac s)
apply(case_tac s; simp add: stack_inst_code.simps)
apply(rename_tac l)
apply(case_tac l; simp)
apply(split if_splits; auto)
done

lemma advance_pc_different[simp]:
  "vctx_pc (vctx_advance_pc co_ctx x1) \<noteq> vctx_pc x1"
apply(simp add: vctx_advance_pc_def)
apply(case_tac "vctx_next_instruction x1 co_ctx"; auto)
done

lemma stateelm_program_all:
  "P \<in> program_as_set ctx \<Longrightarrow> P \<in> range CodeElm"
by (auto simp add: program_as_set_def)

lemma stateelm_not_program_all:
  "P \<notin> range CodeElm \<Longrightarrow> P \<notin> program_as_set ctx"
by (auto simp add: program_as_set_def)

lemma stack_elm_not_program:
  "StackElm x2 \<notin> program_as_set (cctx_program co_ctx)"
apply(simp add: program_as_set_def)
done

lemma stack_elm_not_constant:
   "StackElm x2 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: as_set_simps)
done

lemma storage_elm_not_constant:
   "StorageElm x \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def)
apply(simp add: program_as_set_def)
done

lemma stack_height_elm_not_constant:
  "StackHeightElm h \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done


lemma memory_elm_not_constant :
  "MemoryElm m \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma memory_usage_elm_not_constant :
  "MemoryUsageElm m \<notin> constant_ctx_as_set c"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma pc_elm_not_constant:
"PcElm x \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma gas_elm_not_constant :
"GasElm x \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma contract_action_elm_not_constant:
	"ContractActionElm a \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma code_elm_not_variable[simp] :
 "CodeElm c \<notin> variable_ctx_as_set v"
  by (auto simp: as_set_simps)

lemma this_account_elm_not_variable [simp]:
  "ThisAccountElm t \<notin> variable_ctx_as_set v"
 by (auto simp: as_set_simps)

lemma advance_pc_preserves_storage :
 "vctx_storage (vctx_advance_pc co_ctx x1) = vctx_storage x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_memory:
  "vctx_memory (vctx_advance_pc co_ctx x1) = vctx_memory x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_logs :
  "vctx_logs (vctx_advance_pc co_ctx x1) = vctx_logs x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_memory_usage :
  "vctx_memory_usage (vctx_advance_pc co_ctx x1) = vctx_memory_usage x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_balance  :
   "vctx_balance (vctx_advance_pc co_ctx x1) = vctx_balance x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_caller :
  "vctx_caller (vctx_advance_pc co_ctx x1) = vctx_caller x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_value_sent :
  "vctx_value_sent (vctx_advance_pc co_ctx x1) = vctx_value_sent x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_origin :
  " vctx_origin (vctx_advance_pc co_ctx x1) = vctx_origin x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_preserves_block :
  " vctx_block (vctx_advance_pc co_ctx x1) = vctx_block x1"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_keeps_stack :
  "(vctx_stack (vctx_advance_pc co_ctx v)) = vctx_stack v"
by(simp add: vctx_advance_pc_def)

lemma advance_pc_change:
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
    by (metis sep_conj_assoc sep_conj_commute)
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
    by (metis sep_conj_assoc sep_conj_commute)
  moreover have "(balance a b ** q ** rest) s = ?R"
    by (rule balance_sep)
  ultimately show ?thesis
    by auto
qed

lemma Gverylow_positive[simp] :
  "Gverylow > 0"
apply(simp add: Gverylow_def)
done

lemma saying_zero :
  "(x - Suc 0 < x) = (x \<noteq> 0)"
apply(case_tac x; auto)
done

lemma inst_size_pop:
  "inst_size (Stack POP) = 1"
apply(simp add: inst_code.simps inst_size_def stack_inst_code.simps)
done

lemma pop_advance:
  "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Stack POP) \<Longrightarrow>
   vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def vctx_next_instruction_def inst_size_pop)
done


lemma advance_pc_as_set:
  "program_content (cctx_program co_ctx) (vctx_pc v) = Some (Stack POP) \<Longrightarrow>
   (contexts_as_set (vctx_advance_pc co_ctx v) co_ctx) =
   (contexts_as_set v co_ctx) \<union> {PcElm (vctx_pc v + 1)} - {PcElm (vctx_pc v)}"
  by (auto simp add: memory_usage_element_means as_set_simps vctx_next_instruction_def
       pop_advance advance_pc_preserves_memory_usage vctx_advance_pc_def inst_size_pop )

lemma gas_change_as_set:
  "(contexts_as_set (x1\<lparr>vctx_gas := new_gas\<rparr>) co_ctx) 
    = ((contexts_as_set x1 co_ctx  - {GasElm (vctx_gas x1) }) \<union> { GasElm new_gas } )"
by (auto simp add: as_set_simps)

lemma stack_change_as_set:
   "(contexts_as_set (v\<lparr>vctx_stack := t\<rparr>) co_ctx) =
     (contexts_as_set v co_ctx - stack_as_set (vctx_stack v)) \<union> stack_as_set t 
    "
by (auto simp add: as_set_simps)

lemma stack_height_in[simp]:
  "StackHeightElm (length t) \<in> stack_as_set t"
by(simp add: stack_as_set_def)

lemma pc_not_stack  :
 "PcElm k \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done 

lemma code_not_stack :
  "CodeElm p \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma action_not_context[simp]:
  "ContractActionElm a \<notin> contexts_as_set x1 co_ctx"
by (simp add: as_set_simps)

lemma failed_is_failed[simp]:
   "failed_for_reasons {OutOfGas} (InstructionToEnvironment (ContractFail [OutOfGas]) a b)"
apply(simp add: failed_for_reasons_def)
done

lemma stack_height_increment[simp]:
  "StackHeightElm (Suc (length lst)) \<in> stack_as_set (x # lst)"
apply(simp add: stack_as_set_def)
done

lemma stack_inc_element [simp] :
   "StackElm (length lst, elm) \<in> stack_as_set (elm # lst)"
by (simp add: as_set_simps nth_append)

lemma caller_elm_means_c:
  "(CallerElm c \<in> contexts_as_set x1 co_ctx) = (vctx_caller x1 = c)"
by (auto simp add: as_set_simps)

lemma continue_not_failed[simp] :
  "\<not> failed_for_reasons {OutOfGas}  (InstructionContinue v)"
apply(simp add: failed_for_reasons_def)
done

lemma info_single_advance:
  "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Info i) \<Longrightarrow>
   vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
apply(simp add: vctx_advance_pc_def vctx_next_instruction_def inst_size_def
      inst_code.simps)
done

lemma caller_not_stack :
  "CallerElm c \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma advance_keeps_storage_elm:
  "StorageElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (StorageElm ab \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_memory_elm:
"MemoryElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
 = (MemoryElm ab \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_log_elm:
"LogElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
 (LogElm ab \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_memory_usage_elm:
  "MemoryUsageElm x8 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (MemoryUsageElm x8 \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_this_account_elm:
  "ThisAccountElm x10 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (ThisAccountElm x10 \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_balance_elm:
  "BalanceElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (BalanceElm ab \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_origin_elm:
  "OriginElm x13 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (OriginElm x13 \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_sent_value_elm:
  "SentValueElm x14 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (SentValueElm x14 \<in> contexts_as_set x1 co_ctx)"
 by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma data_sent_advance_pc:
  "vctx_data_sent (vctx_advance_pc co_ctx x1) = vctx_data_sent x1"
 by (auto simp add: vctx_advance_pc_def)

lemma advance_keeps_sent_data_elm :
  "SentDataElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (SentDataElm ab \<in> contexts_as_set x1 co_ctx)
  "
  by(simp add: as_set_simps vctx_advance_pc_def)

lemma ext_program_size_not_constant:
  "ExtProgramSizeElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma ext_program_advance_pc :
  " vctx_ext_program (vctx_advance_pc co_ctx x1)
  = vctx_ext_program x1"
apply(simp add: vctx_advance_pc_def balance_as_set_def)
done

lemma advance_keeps_ext_program_size_elm:
  "ExtProgramSizeElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (ExtProgramSizeElm ab \<in> contexts_as_set x1 co_ctx)"
  by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma ext_program_elm_not_constant :
   "ExtProgramElm abc \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done


lemma advance_keeps_ext_program_elm :
  "ExtProgramElm abc \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
= (ExtProgramElm abc \<in> contexts_as_set x1 co_ctx)"
  by(auto simp add: as_set_simps vctx_advance_pc_def)

lemma blockhash_not_constant:
  "BlockhashElm ab \<notin> constant_ctx_as_set co_ctx"
  by(auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_blockhash_elm :
  "BlockhashElm ab \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (BlockhashElm ab \<in> contexts_as_set x1 co_ctx)"
  by(auto simp add: as_set_simps vctx_advance_pc_def)


lemma coinbase_elm_not_constant :
"CoinbaseElm v \<notin> constant_ctx_as_set co_ctx"
  by(case_tac v; auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_conbase_elm :
  "CoinbaseElm x22 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (CoinbaseElm x22 \<in> contexts_as_set x1 co_ctx)"
by (auto simp add:as_set_simps vctx_advance_pc_def)

lemma timestamp_not_constant :
  "TimestampElm t \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma advance_keeps_timestamp_elm :
  "TimestampElm t \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
  = (TimestampElm t \<in> contexts_as_set x1 co_ctx)"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma difficulty_not_constant :
  "DifficultyElm x24 \<notin> constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_difficulty_elm:
  "DifficultyElm x24 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
  = (DifficultyElm x24 \<in> contexts_as_set x1 co_ctx)"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma gaslimit_not_constant:
  "GaslimitElm x25 \<notin> constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma gaslimit_elm_means :
  "GaslimitElm x25 \<in> variable_ctx_as_set x1
  = (x25 = block_gaslimit (vctx_block x1))"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma gaslimit_elm_c :
  "GaslimitElm x25 \<in> contexts_as_set x1 co_ctx
  = (x25 = block_gaslimit (vctx_block x1))"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma advance_keeps_gaslimit_elm :
  "GaslimitElm x25 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (GaslimitElm x25 \<in> contexts_as_set x1 co_ctx)"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma gasprice_not_constant :
  "GaspriceElm x26 \<notin> constant_ctx_as_set co_ctx"
by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma gasprice_elm_means :
  "GaspriceElm x26 \<in> variable_ctx_as_set x1
  = (x26 = vctx_gasprice x1)"
  by (auto simp add: as_set_simps )

lemma gasprice_c_means :
  "GaspriceElm x26 \<in> contexts_as_set x1 co_ctx
  = (x26 = vctx_gasprice x1)"
by (auto simp add: as_set_simps)

lemma advance_keeps_gasprice_elm:
"GaspriceElm x26 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx
 = (GaspriceElm x26 \<in> contexts_as_set x1 co_ctx)"
  by (auto simp add: as_set_simps vctx_advance_pc_def)

lemma stackheight_different:
"
StackHeightElm len \<in> stack_as_set lst =
(len = length lst)
"
apply(simp add: stack_as_set_def)
done

lemma stack_element_in_stack :
  "StackElm ab \<in> stack_as_set lst =
   ((fst ab) < length lst \<and> rev lst ! (fst ab) = snd ab)"
apply(case_tac ab; auto simp add: stack_as_set_def)
done

lemma storage_not_stack :
  "StorageElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma memory_not_stack :
  "MemoryElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma log_not_stack :
  "LogElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma gas_not_stack :
   "GasElm x7 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma memory_usage_not_stack :
  "MemoryUsageElm x8 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma this_account_not_stack :
  "ThisAccountElm x10 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma balance_not_stack:
  "BalanceElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma code_elm_means:
  "CodeElm xy \<in> instruction_result_as_set c (InstructionContinue x1) =
(program_content (cctx_program c) (fst xy) = Some (snd xy) \<or>
    program_content (cctx_program c) (fst xy) = None \<and>
    (snd xy) = Misc STOP)
"
  by (case_tac xy, auto simp add: as_set_simps vctx_advance_pc_def instruction_result_as_set_def)

lemma pc_elm_means:
   "PcElm k \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
    (k = vctx_pc x1)"
  by (auto simp add: as_set_simps vctx_advance_pc_def instruction_result_as_set_def)

lemma memory_usage_elm_means:
   "MemoryUsageElm k \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
    (k = vctx_memory_usage x1)"
  by (auto simp add: as_set_simps vctx_advance_pc_def instruction_result_as_set_def)

lemma block_number_pred_sep:
  "(block_number_pred bn ** rest) s =
   ((BlockNumberElm bn \<in> s) \<and> rest (s - {BlockNumberElm bn}))"
 by (solve_sep_iff simp: block_number_pred_def)

lemma sep_block_number_pred_sep:
  "(rest ** block_number_pred bn ** a) s =
   ((BlockNumberElm bn \<in> s) \<and> (rest ** a) (s - {BlockNumberElm bn}))"
 apply (rule iffI)
 apply (sep_select_asm 2)
 apply (subst (asm) block_number_pred_sep, simp)
 apply (sep_select 2)
 apply (subst  block_number_pred_sep, simp)
 done

lemma block_number_elm_not_constant:
  "BlockNumberElm bn \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma block_number_elm_in_v_means:
  "BlockNumberElm bn \<in> variable_ctx_as_set v
   = ( bn = block_number (vctx_block v) )"
    by ( auto simp add: as_set_simps )

lemma block_number_elm_means:
  "BlockNumberElm bn \<in> instruction_result_as_set co_ctx (InstructionContinue v)
   = ( bn = block_number (vctx_block v) )"
by (simp add: instruction_result_as_set_def as_set_simps)

lemma stack_heigh_elm_means :
  "StackHeightElm h \<in> instruction_result_as_set co_ctx (InstructionContinue x1)
  = (length (vctx_stack x1) = h)"
apply(auto simp add: instruction_result_as_set_def as_set_simps)
done

lemma stack_elm_means :
  "StackElm ha \<in> instruction_result_as_set co_ctx (InstructionContinue v) =
  (fst ha < length (vctx_stack v) \<and> rev (vctx_stack v) ! fst ha = snd ha)"
apply(case_tac ha, auto simp add: instruction_result_as_set_def as_set_simps)
done

lemma balance_not_constant:
  "BalanceElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
  done
    
lemma balance_elm_i_means :
  "BalanceElm ab \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
     (vctx_balance x1 (fst ab) = (snd ab))
  "
apply(case_tac ab, auto simp add: instruction_result_as_set_def as_set_simps)
done

lemma gas_elm_i_means :
  "GasElm g \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
  (vctx_gas x1 = g)"
apply(auto simp add: instruction_result_as_set_def as_set_simps)
done

lemma continuing_continuing[simp]:
  "ContinuingElm True \<in> instruction_result_as_set co_ctx (InstructionContinue x1)"
apply(simp add: instruction_result_as_set_def)
  done

lemma stack_all:
 "P \<in> stack_as_set lst \<Longrightarrow> P \<in> range StackElm \<union> range StackHeightElm"
  by (induction lst ; auto simp add:as_set_simps)

lemma not_stack_all:
 "P \<notin> range StackElm \<union> range StackHeightElm \<Longrightarrow> P \<notin> stack_as_set lst"
  by (induction lst ; auto simp add:as_set_simps)

lemma origin_not_stack :
   "OriginElm x13 \<notin> stack_as_set lst"
by (auto dest: stack_all)

lemma sent_value_not_stack :
 "SentValueElm x14 \<notin> stack_as_set lst"
by (auto dest: stack_all)

lemma ext_program_not_stack:
  "ExtProgramElm a \<notin> stack_as_set lst"
by (auto dest: stack_all)

lemma sent_data_not_stack :
"SentDataElm ab \<notin> stack_as_set lst"
by (auto dest: stack_all)

lemma contract_action_elm_not_stack :
 "ContractActionElm x19 \<notin> stack_as_set lst"
by (auto dest: stack_all)

lemma log_num_v_advance  :
  "LogNumElm x6 \<in> variable_ctx_as_set (vctx_advance_pc co_ctx x1) =
   (LogNumElm x6 \<in> variable_ctx_as_set x1)"
by(simp add: as_set_simps vctx_advance_pc_def)

lemma log_num_advance :
  "LogNumElm x6 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
   (LogNumElm x6 \<in> contexts_as_set x1 co_ctx)"
apply(simp add: as_set_simps vctx_advance_pc_def)
done

lemma account_existence_not_in_constant [simp] :
  "AccountExistenceElm p \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma account_existence_not_in_stack  :
  "AccountExistenceElm p \<notin> stack_as_set (vctx_stack x1)"
apply(simp add: stack_as_set_def)
done

lemma account_existence_not_in_balance :
  "AccountExistenceElm p \<notin> balance_as_set (vctx_balance x1)"
apply(simp add: balance_as_set_def)
done

lemma account_existence_not_ext :
  "AccountExistenceElm p \<notin> ext_program_as_set (vctx_ext_program x1)"
apply(simp add: ext_program_as_set_def)
done

lemma account_existence_elm_means :
  "AccountExistenceElm p \<in> variable_ctx_as_set x =
   (vctx_account_existence x (fst p) = snd p)"
  by (case_tac p, auto simp add: as_set_simps vctx_advance_pc_def instruction_result_as_set_def)

lemma account_existence_elm_means_c :
  "AccountExistenceElm p \<in> contexts_as_set x c =
   (vctx_account_existence x (fst p) = snd p)"
by (case_tac p, auto simp add: as_set_simps)

lemma account_existence_advance :
  "AccountExistenceElm (aa, x) \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (AccountExistenceElm (aa, x) \<in> contexts_as_set x1 co_ctx)"
 by(simp add: as_set_simps vctx_advance_pc_def)

lemma account_existence_advance_v :
  "vctx_account_existence (vctx_advance_pc co_ctx x1) aa =
  (vctx_account_existence x1 aa)"
apply(simp add: vctx_advance_pc_def)
  done

lemma prog_content_vctx_next_instruction:
 "program_content (cctx_program y) (vctx_pc x) = Some v \<Longrightarrow> vctx_next_instruction x y = Some v"
  by (simp add: vctx_next_instruction_def split: option.split)

lemma inst_size_eq_1:
  "\<forall>x. inst \<noteq> Stack (PUSH_N x) \<Longrightarrow>
    inst_size inst = 1"
  apply (case_tac inst; simp add: inst_size_def inst_code.simps)
  apply (rename_tac x)
  apply (case_tac x  ;fastforce simp add: stack_inst_code.simps)
  done

lemma inst_size_no_stack_eq_1[simplified image_def, simp]:
  "inst \<notin> (Stack ` range PUSH_N) \<Longrightarrow> inst_size inst = 1"
  "inst \<notin> range Stack \<Longrightarrow> inst_size inst = 1"
  by (auto intro: inst_size_eq_1)

lemma advance_pc_no_inst:
 "vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 \<Longrightarrow> program_content (cctx_program co_ctx) (vctx_pc x1) = None"
  by (simp add: vctx_advance_pc_def vctx_next_instruction_def split:option.splits)

lemma advance_pc_inc_but_stack :
 "program_content (cctx_program co_ctx) (vctx_pc x) = Some inst \<Longrightarrow> inst \<notin> range Stack\<Longrightarrow> 
  vctx_pc (vctx_advance_pc co_ctx x) = vctx_pc x + 1"
by (case_tac inst; simp add: vctx_next_instruction_def vctx_advance_pc_def inst_size_def inst_code.simps)

lemmas advance_pc_simps =
  advance_pc_preserves_storage
  advance_pc_preserves_memory
  advance_pc_preserves_balance
  ext_program_advance_pc
  advance_pc_no_gas_change
  advance_pc_preserves_memory_usage
  advance_pc_keeps_stack
  data_sent_advance_pc
  advance_pc_preserves_logs
  advance_pc_preserves_value_sent
  advance_pc_preserves_caller
  advance_pc_preserves_origin
  advance_pc_preserves_block
(*  advance_pc_no_inst *)
(*   advance_pc_inc_but_stack *)
  log_num_v_advance
  log_num_advance
  advance_keeps_balance_elm
  advance_keeps_blockhash_elm
  advance_keeps_conbase_elm
  advance_keeps_difficulty_elm
  advance_keeps_ext_program_elm
  advance_keeps_ext_program_size_elm
  advance_keeps_gaslimit_elm
  advance_keeps_gasprice_elm
  advance_keeps_log_elm
  advance_keeps_memory_elm
  advance_keeps_memory_usage_elm
  advance_keeps_origin_elm
  advance_keeps_sent_data_elm
  advance_keeps_sent_value_elm
  advance_keeps_storage_elm
  advance_keeps_this_account_elm
  advance_keeps_timestamp_elm
  account_existence_advance
  (*pop_advance *)
  account_existence_advance_v


  

lemma balance0 :
notes rev_nth_simps[simp]
shows
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
  apply(auto simp: set_diff_eq)
         apply(rename_tac elm; case_tac elm; auto simp add: instruction_result_as_set_def as_set_simps vctx_advance_pc_def 
prog_content_vctx_next_instruction inst_size_eq_1)
        apply (simp add: instruction_result_as_set_def stateelm_equiv_simps advance_pc_simps)+
     apply(rename_tac elm; case_tac elm; auto simp add:  instruction_result_as_set_def stack_as_set_def balance_as_set_def stateelm_equiv_simps vctx_advance_pc_def vctx_next_instruction_def)
                      apply (clarsimp simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def )+
    apply (simp add: instruction_result_as_set_def stateelm_equiv_simps )+
  done

lemma ext_program_size_elm_not_stack:
  "ExtProgramSizeElm ab \<notin> stack_as_set (1 # ta)"
apply(simp add: stack_as_set_def)
done

lemma continuing_not_stack:
"ContinuingElm b \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
done

lemma block_hash_not_stack:
"BlockhashElm ab \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma block_number_not_stack:
"BlockNumberElm x22 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma coinbase_not_stack:
 "CoinbaseElm x23 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma timestamp_not_stack:
  "TimestampElm x24 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma difficulty_not_stack:
 "DifficultyElm k \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma gaslimit_not_stack:
 "GaslimitElm x26 \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma gasprice_not_stack:
"GaspriceElm a \<notin> stack_as_set s"
apply(simp add: stack_as_set_def)
done

lemma ext_program_size_not_stack:
 "ExtProgramSizeElm p \<notin> stack_as_set lst"
apply(simp add: stack_as_set_def)
  done

lemmas not_stack_simps = 
 ext_program_size_elm_not_stack
 continuing_not_stack
 block_hash_not_stack
 block_number_not_stack
 coinbase_not_stack
 timestamp_not_stack
 difficulty_not_stack
 gaslimit_not_stack
 gasprice_not_stack
 ext_program_size_not_stack

lemma advance_keeps_stack_elm:
  "StackElm x2 \<in> contexts_as_set (vctx_advance_pc co_ctx v) co_ctx =
  (StackElm x2 \<in> contexts_as_set v co_ctx)"
  by (simp add: contexts_as_set_def stateelm_basic_means_simps advance_pc_simps)

lemma advance_keeps_code_elm:
  "CodeElm x9 \<in> contexts_as_set (vctx_advance_pc co_ctx x1) co_ctx =
  (CodeElm x9 \<in> contexts_as_set x1 co_ctx)"
  by (simp add: contexts_as_set_def  code_elm_not_variable stateelm_basic_means_simps advance_pc_simps)

lemma storage_elm_means:
  "StorageElm ab \<in> contexts_as_set x1 co_ctx =
   (vctx_storage x1 (fst ab) = (snd ab))"
  by (simp add: contexts_as_set_def stateelm_basic_means_simps advance_pc_simps storage_elm_not_constant)

lemma memory_elm_means:
   "MemoryElm ab \<in> contexts_as_set x1 co_ctx =
    (vctx_memory x1 (fst ab) = (snd ab))"
  apply(simp add: contexts_as_set_def stateelm_basic_means_simps memory_elm_not_constant)
done

lemma memory_usage_elm_c_means:
   "MemoryUsageElm m \<in> contexts_as_set x1 co_ctx =
    (vctx_memory_usage x1 = m)"
  apply(simp add: contexts_as_set_def stateelm_basic_means_simps memory_usage_elm_not_constant)
done

lemma log_not_constant :
  "LogElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma log_elm_means :
  "LogElm ab \<in> contexts_as_set x1 co_ctx =
   (fst ab < length (vctx_logs x1) \<and> rev (vctx_logs x1) ! (fst ab) = (snd ab))"
apply(auto simp add: contexts_as_set_def log_not_constant stateelm_basic_means_simps )
done

lemma this_account_means:
  "ThisAccountElm x10 \<in> contexts_as_set x1 co_ctx =
   (cctx_this co_ctx = x10)"
by (auto simp: as_set_simps)

lemma balance_elm_c_means :
  "BalanceElm ab \<in> contexts_as_set x1 co_ctx =
   (vctx_balance x1 (fst ab) = (snd ab))"
  apply(auto simp add: contexts_as_set_def balance_elm_means stateelm_basic_means_simps balance_not_constant)
done

lemma origin_not_constant:
  "OriginElm x13 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma orogin_elm_c_means:
  "OriginElm x13 \<in> contexts_as_set x1 co_ctx =
   (vctx_origin x1 = x13)"
  apply(auto simp add: advance_keeps_origin_elm constant_ctx_as_set_def program_as_set_def contexts_as_set_def stateelm_basic_means_simps)
  done
    
lemma sent_value_not_constant:
  "SentValueElm x14 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma sent_value_c_means :
  "SentValueElm x14 \<in> contexts_as_set x1 co_ctx
  = (vctx_value_sent x1 = x14)"
  apply(auto simp add: contexts_as_set_def stateelm_basic_means_simps sent_value_not_constant)
done

lemma sent_data_not_constant:
  "SentDataElm ab \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma sent_data_elm_c_means :
  "SentDataElm ab \<in> contexts_as_set x1 co_ctx =
   (ab = vctx_data_sent x1)"
by (auto simp add: contexts_as_set_def  sent_data_not_constant stateelm_basic_means_simps )
   
lemmas not_constant_simps =
  stack_elm_not_constant
  storage_elm_not_constant
  stack_height_elm_not_constant
  memory_elm_not_constant
  memory_usage_elm_not_constant
  pc_elm_not_constant
  gas_elm_not_constant
  contract_action_elm_not_constant
  balance_not_constant
  sent_value_not_constant
  sent_data_not_constant


lemma short_rev_append:
 "a < length t \<Longrightarrow> (rev t @ lst) ! a = rev t ! a"
	by (simp add: nth_append)

lemma memory_usage_not_constant:
"MemoryUsageElm x8 \<notin> constant_ctx_as_set co_ctx"
apply(simp add: constant_ctx_as_set_def program_as_set_def)
done

lemma code_elms :
 "{CodeElm (pos, i) |pos i. P pos i \<or> Q pos i} \<subseteq> S =
 ({CodeElm (pos, i) | pos i. P pos i} \<subseteq> S \<and> {CodeElm (pos, i) | pos i. Q pos i} \<subseteq> S)"
apply(auto)
done

lemma pc_update_v:
  "x \<in> variable_ctx_as_set (x1\<lparr>vctx_pc := p\<rparr>) =
  (x = PcElm p \<or> x \<in> variable_ctx_as_set x1 - {PcElm (vctx_pc x1)})"
  by (auto simp add:  stateelm_basic_means_simps advance_pc_simps
 as_set_simps)

lemma pc_update :
  "x \<in> contexts_as_set (x1\<lparr>vctx_pc := p\<rparr>) co_ctx =
  (x = PcElm p \<or> x \<in> contexts_as_set x1 co_ctx - {PcElm (vctx_pc x1)})"
by (auto simp add: as_set_simps)

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
	by (metis not_continuing_sep sep_conj_assoc sep_conj_commute)

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
    by (metis sep_conj_assoc sep_conj_commute)
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
  by (sep_simp simp: action_sep)

lemma iota0_non_empty_aux:
  "\<forall> b x len lst a.
    len \<le> l \<longrightarrow>                     
    iota0 b len (lst @ [a]) = a # iota0 b len lst"
  apply(induction l)
    apply(simp add: iota0.simps)
  apply(simp add: iota0.simps)
  apply(rule allI)
  apply(rule allI)
  apply(case_tac "len = Suc l"; auto)
  apply(drule_tac x = "b + 1" in spec)
  apply(drule_tac x = l in spec)
  apply simp
  apply(drule_tac x = "b # lst" in spec)
  apply(drule_tac x = "a" in spec)
  by(simp add: iota0.simps)  


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
by(auto simp add:cut_memory_aux.simps)

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

lemma cut_memory_aux_cons[simp] :
  "(cut_memory_aux b (Suc n) m = a # lst) =
   (m b = a \<and> cut_memory_aux (b + 1) n m = lst)"
apply(simp add: cut_memory_aux.simps cut_memory_def)
done

lemma unat_minus_one2 : "unat x = Suc n \<Longrightarrow> unat (x - 1) = n"
  by (metis diff_Suc_1 nat.simps(3) unat_eq_zero unat_minus_one)

lemma cut_memory_cons[simp] :
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


lemma memory_range_cons :
"(memory_range b (a # lst) ** rest) s = (memory8 b a ** memory_range (b + 1) lst ** rest) s"
 by (simp only: memory_range.simps sep_conj_ac)

lemma cut_memory_memory_range[rule_format] :
  "\<forall> rest b n.
   unat n = length lst \<longrightarrow>
   (memory_range b lst ** rest) (instruction_result_as_set c (InstructionContinue v))
   \<longrightarrow> cut_memory b n (vctx_memory v) = lst"
  apply(induction lst)
   apply(simp add: unat_eq_0)
  apply clarsimp
  apply (sep_simp simp: memory8_sep)
  apply(drule_tac x = "memory8 b a ** rest" in spec)
  apply(drule_tac x = "b + 1" in spec)
  apply(drule_tac x = "n - 1" in spec)
  apply (erule impE)
   apply unat_arith
  apply (erule impE)
   apply (sep_simp simp: memory8_sep ; clarsimp)
  apply (simp add: cut_memory_cons)
  apply (rule conjI)
   apply unat_arith
      apply (simp add: instruction_result_as_set_def as_set_simps)
 done

(****** specifying each instruction *******)

bundle simp_for_triples_bundle =
        vctx_next_instruction_default_def[simp]
        stack_2_1_op_def[simp]
        stack_1_1_op_def[simp]
        stack_0_0_op_def[simp]
        vctx_next_instruction_def[simp]
        instruction_sem_def[simp]
        check_resources_def[simp]
        pop_def[simp]
        jump_def[simp]
        jumpi_def[simp]
        instruction_failure_result_def[simp]
        strict_if_def[simp]
        blocked_jump_def[simp]
        blockedInstructionContinue_def[simp]
        vctx_pop_stack_def[simp]
        stack_0_1_op_def[simp]
        general_dup_def[simp]
        dup_inst_numbers_def[simp]
        new_memory_consumption.simps[simp]
        inst_stack_numbers.simps[simp]
        arith_inst_numbers.simps[simp]
        program_sem.simps[simp]
        info_inst_numbers.simps[simp]
        stack_inst_numbers.simps[simp]
        pc_inst_numbers.simps[simp]
        storage_inst_numbers.simps[simp]
        subtract_gas.simps[simp]

lemmas removed_from_sft =
        meter_gas_def
        C_def Cmem_def
        Gmemory_def
        thirdComponentOfC_def
        Gbalance_def
        Gbase_def
        Gsreset_def


lemma emp_sep [simp] :
  "(emp ** rest) s = rest s"
apply(simp add: emp_def sep_basic_simps)
done

lemma memory_range_elms_index_aux[rule_format] :
"\<forall> i a begin_word. MemoryElm (i, a) \<in> memory_range_elms begin_word input \<longrightarrow>
    (\<exists>pos. \<not> length input \<le> pos \<and> begin_word + word_of_int (int pos) = i)"
apply(induction input)
 apply(simp)
apply(clarsimp)
apply(drule_tac x = i in spec)
apply(drule_tac x = aa in spec)
apply(drule_tac x = "begin_word + 1" in spec)
apply(auto)
apply(rule_tac x = "Suc pos" in exI)
apply(auto)
apply(simp add: Word.wi_hom_syms(1))
done

lemmas memory_range_elms_index_meta = memory_range_elms_index_aux

lemma memory_range_elms_index_contra[rule_format] :
"(\<forall> pos. pos \<ge> length input \<or> begin_word + (word_of_int (int pos)) \<noteq> i) \<longrightarrow>
 MemoryElm (i, a) \<notin> memory_range_elms begin_word input"
  by (fastforce dest: memory_range_elms_index_meta)

lemma memory_range_elms_index_contra_meta :
"(\<forall> pos. pos \<ge> length input \<or> begin_word + (word_of_int (int pos)) \<noteq> i) \<Longrightarrow>
 MemoryElm (i, a) \<notin> memory_range_elms begin_word input"
 by (auto simp add: memory_range_elms_index_contra)

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

lemma no_overwrap[simp]:
  "unat (len_word :: w256) = Suc (length input) \<Longrightarrow>
   MemoryElm (begin_word, a) \<notin> memory_range_elms (begin_word + 1) input"
apply(rule memory_range_elms_index_contra_meta)
apply(drule suc_is_word)
apply(auto dest: too_small_to_overwrap)
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
   apply (erule (1) impE)
   apply (subst memory_range.simps, simp)
   apply (sep_simp simp: memory8_sep)
   apply (auto simp add: no_overwrap)[1]
  apply unat_arith
 done


lemma memory_range_sep :
"   unat (len_word :: w256) = length input \<longrightarrow>
       (memory_range begin_word input ** rest) s =
       ((memory_range_elms begin_word input \<subseteq> s) \<and> rest (s - memory_range_elms begin_word input)) 
"
  apply(induction input arbitrary: begin_word s len_word rest)
   apply clarsimp
  apply (clarsimp simp del: sep_conj_assoc simp: sep_conj_ac)
  apply (drule_tac x="begin_word + 1" in meta_spec)
  apply (drule_tac x="s - {MemoryElm (begin_word, a)}" in meta_spec)
  apply (drule_tac x="len_word -1" in meta_spec)
  apply (drule_tac x=rest in meta_spec)
  apply (erule impE)
   apply (fastforce simp: unat_arith_simps)
  apply (sep_simp simp: memory8_sep)
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
   apply (fastforce simp: no_overwrap)
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

lemma continuging_not_memory_range:
  "\<forall> in_begin. ContinuingElm False \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma contractaction_not_memory_range :
  "\<forall> in_begin a. ContractActionElm a   \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma pc_not_memory_range :
  "\<forall> in_begin k. PcElm k \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma this_account_not_memory_range  :
  "\<forall> this in_begin. ThisAccountElm this \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma balance_not_memory_range :
  "\<forall> in_begin. BalanceElm p \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma code_not_memory_range:
  "\<forall> k in_begin. CodeElm pair \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma continuing_not_memory_range :
  "\<forall> b in_begin. ContinuingElm b \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma stack_not_memory_range :
  "\<forall> in_begin. StackElm e \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma stack_height_not_memory_range:
  "\<forall> in_begin. StackHeightElm h \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

lemma gas_not_memory_range :
  "\<forall> in_begin. GasElm g \<notin> memory_range_elms in_begin input"
apply(induction input; auto)
done

definition triple_alt ::
 "network \<Rightarrow> failure_reason set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> (int * inst) set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "triple_alt net allowed_failures pre insts post ==
    \<forall> co_ctx presult rest stopper.
       (code insts ** pre ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k.
         ((post ** code insts ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)))
         \<or> failed_for_reasons allowed_failures (program_sem stopper co_ctx k net presult))"

lemma triple_triple_alt :
  "triple net s pre c post = triple_alt net s pre c post"
apply(simp only: triple_def triple_alt_def sep_conj_commute[where P=pre] sep_conj_assoc)
done

fun stack_topmost_elms :: "nat \<Rightarrow> w256 list \<Rightarrow> state_element set"
where
  "stack_topmost_elms h [] = { StackHeightElm h }"
| "stack_topmost_elms h (f # rest) = { StackElm (h, f) } \<union> stack_topmost_elms (h + 1) rest"

definition stack_topmost :: "nat \<Rightarrow> w256 list \<Rightarrow> state_element set \<Rightarrow> bool"
where
  "stack_topmost h lst s = (s = stack_topmost_elms h lst)"

lemma stack_topmost_sep:
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

lemma fourth_stack_topmost :
  "(a ** b ** c ** stack_topmost h lst ** rest) s =
   (stack_topmost_elms h lst \<subseteq> s \<and> (a ** b ** c ** rest) (s - stack_topmost_elms h lst))"
  by (rule iffI ; sep_simp simp: stack_topmost_sep)

lemma this_account_not_stack_topmost :
  "\<forall> h. ThisAccountElm this
       \<notin> stack_topmost_elms h lst"
apply(induction lst; simp )
done

lemma gas_not_stack_topmost :
  "\<forall> h. GasElm g
       \<notin> stack_topmost_elms h lst"
apply(induction lst; simp)
done

lemma stack_topmost_empty:
 "x \<in> stack_topmost_elms h [] = (x = StackHeightElm h)"
by simp

lemma not_memory_range_elms_all:
  "P \<notin> range MemoryElm \<Longrightarrow> P \<notin> memory_range_elms in_begin input"
  by (induction input arbitrary: in_begin; auto)

lemma memory_range_elms_all:
  "P \<in> memory_range_elms in_begin input \<Longrightarrow> P \<in> range MemoryElm"
  by (induction input arbitrary: in_begin; auto)

lemma memory_range_elms_not_pc :
  "(memory_range_elms in_begin input \<subseteq> s - {PcElm k}) =
   (memory_range_elms in_begin input \<subseteq> s)"
by (auto dest: memory_range_elms_all)

lemma account_ex_is_not_memory_range :
  "AccountExistenceElm p \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma lognum_not_memory :
  " LogNumElm n \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma account_existence_not_memory:
  "AccountExistenceElm x \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)
  
lemma log_not_memory_range :
  "LogElm x5 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)


lemma caller_not_memory_range:
  "CallerElm x5 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)


lemma origin_not_memory_range:
  "OriginElm x5 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)


lemma sent_value_not_memory_range  :
  "SentValueElm x5 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)


lemma memory_usage_not_memory_range:
 "MemoryUsageElm x  \<notin> memory_range_elms in_begin  input"
 by (auto dest: memory_range_elms_all)

    
lemmas not_memory_range_simps =
  continuing_not_memory_range 
  contractaction_not_memory_range 
  pc_not_memory_range 
  this_account_not_memory_range  
  balance_not_memory_range   
  code_not_memory_range  
  stack_not_memory_range   
  stack_height_not_memory_range   
  gas_not_memory_range   
  account_ex_is_not_memory_range  
  lognum_not_memory  
  account_existence_not_memory 
  log_not_memory_range  
  caller_not_memory_range 
  origin_not_memory_range 
  sent_value_not_memory_range   
  memory_usage_not_memory_range 


lemma memory_range_elms_not_account_existence :
  "(memory_range_elms in_begin input \<subseteq> s - {AccountExistenceElm p}) =
   (memory_range_elms in_begin input \<subseteq> s)"
by (auto simp : account_ex_is_not_memory_range)

lemma memory_range_elms_not_code :
  "(memory_range_elms in_begin input
       \<subseteq> s - {CodeElm pair}) =
   (memory_range_elms in_begin input \<subseteq> s)
  "
  by (auto dest: memory_range_elms_all)

lemma memory_not_stack_topmost:
  "MemoryElm p \<notin> stack_topmost_elms h lst"
by (induction lst arbitrary: h, auto simp add: stack_topmost_elms.simps)

lemma memory_usage_not_stack_topmost:
  "MemoryUsageElm p \<notin> stack_topmost_elms h lst"
by (induction lst arbitrary: h, auto simp add: stack_topmost_elms.simps)

lemma stack_topmost_not_memory :
  "(stack_topmost_elms h lst
       \<subseteq> s - memory_range_elms in_begin input) =
   (stack_topmost_elms h lst \<subseteq> s)"
by (induction input arbitrary: in_begin; auto simp add: memory_not_stack_topmost memory_range_elms.simps)

lemma pc_not_stack_topmost  :
  "PcElm p \<notin> stack_topmost_elms h lst"
by (induction lst arbitrary:h; auto simp add: stack_topmost_elms.simps)

lemma stack_topmost_not_pc:
  "stack_topmost_elms h lst
       \<subseteq> s - {PcElm (vctx_pc x1)} =
     (stack_topmost_elms h lst \<subseteq> s)"
 by (auto simp: pc_not_stack_topmost)
    
lemma ae_not_stack_topmost :
 "AccountExistenceElm p \<notin> stack_topmost_elms h lst"
 by(induction lst arbitrary: h; auto simp add: stack_topmost_elms.simps)

lemma stack_topmost_not_account_existence :
  "stack_topmost_elms h lst
       \<subseteq> s - {AccountExistenceElm p} =
     (stack_topmost_elms h lst \<subseteq> s)"
 by (auto simp: ae_not_stack_topmost)

lemma stack_topmost_not_code:
  "stack_topmost_elms h lst
       \<subseteq> s - {CodeElm (vctx_pc x1, Misc CALL)} =
     (stack_topmost_elms h lst \<subseteq> s)"
by (induction lst arbitrary: h; auto)

lemma stack_height_after_call:
  includes simp_for_triples_bundle
  shows
       "vctx_balance x1 (cctx_this co_ctx) \<ge> vctx_stack x1 ! 2 \<Longrightarrow>
        (StackHeightElm (h + 7) \<in>
          instruction_result_as_set co_ctx (InstructionContinue x1)) \<Longrightarrow>
        (StackHeightElm h
          \<in> instruction_result_as_set co_ctx (subtract_gas g memu (call net x1 co_ctx)))
        "
  apply(simp add: call_def as_set_simps stateelm_basic_means_simps)
  apply(auto simp add: instruction_result_as_set_def as_set_simps split: list.splits)
done

lemma topmost_elms_means:
   "\<forall> h x1.
    stack_topmost_elms h lst
       \<subseteq> instruction_result_as_set co_ctx (InstructionContinue x1) =
    (length (vctx_stack x1) = h + (length lst) \<and>
     drop h (rev (vctx_stack x1)) = lst)
    "
apply(induction lst; simp)
 apply(simp add: instruction_result_as_set_def as_set_simps)
 apply blast
apply(rule allI)
  apply(rule allI)
  apply (simp (no_asm) add: instruction_result_as_set_def as_set_simps)
    apply (rule iffI )
   apply (clarify)
   apply (rule conjI)
    apply (simp (no_asm))
   apply (drule sym[where t="_#_"])
   apply (simp add: Cons_nth_drop_Suc)+
   apply (rule conjI)
   apply (clarsimp)
   apply (subst nth_via_drop)
    apply (erule HOL.trans[rotated])
    apply (subst drop_append)
    apply simp+
  apply clarsimp
  apply (drule arg_cong[where f="drop 1"])
  apply simp
done

lemma to_environment_not_continuing[simp]:
  "ContinuingElm True
       \<notin> instruction_result_as_set co_ctx (InstructionToEnvironment x31 x32 x33)"
apply(simp add: instruction_result_as_set_def as_set_simps)
  done
    
lemma topmost_all:
 "P \<in> stack_topmost_elms h lst \<Longrightarrow> P \<in> range StackElm \<union> range StackHeightElm"
  by (induction lst arbitrary:h ; auto)

lemma not_topmost_all:
 "P \<notin> range StackElm \<union> range StackHeightElm \<Longrightarrow> P \<notin> stack_topmost_elms h lst"
  by (induction lst arbitrary:h ; auto)

lemma balance_not_topmost :
  "BalanceElm pair \<notin> stack_topmost_elms h lst"
  by (auto dest: topmost_all)

lemma this_not_topmost :
  "ThisAccountElm pair \<notin> stack_topmost_elms h lst"
  by (auto dest: topmost_all)

lemma continue_not_topmost :
  "ContinuingElm b\<notin> stack_topmost_elms len lst"
  by (auto dest: topmost_all)

lemma this_account_i_means :
  "ThisAccountElm this \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
   (cctx_this co_ctx = this)"
  by (auto simp add: instruction_result_as_set_def as_set_simps)

lemma memory_usage_not_topmost:
  "MemoryUsageElm u  \<notin> stack_topmost_elms len lst"
  by (auto dest: topmost_all)

lemma gas_not_topmost:
  "GasElm pair \<notin> stack_topmost_elms h lst"
  by (auto dest: topmost_all)


lemma call_new_balance :
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
 apply(simp add: as_set_simps)
apply(simp add: strict_if_def subtract_gas.simps update_balance_def as_set_simps)
done


lemma advance_pc_call:
 includes simp_for_triples_bundle
  shows

      "program_content (cctx_program co_ctx) (vctx_pc x1) = Some (Misc CALL) \<Longrightarrow>
       k = vctx_pc x1 \<Longrightarrow>
       vctx_pc (vctx_advance_pc co_ctx x1) = vctx_pc x1 + 1"
  by (simp add: vctx_advance_pc_def inst_size_def inst_code.simps)


lemma memory_range_elms_not_continuing :
  "(memory_range_elms in_begin input
       \<subseteq> insert (ContinuingElm True) (contexts_as_set x1 co_ctx))
  = (memory_range_elms in_begin input
       \<subseteq> (contexts_as_set x1 co_ctx))
  "
by (auto dest: memory_range_elms_all)


lemma suc_unat :
"Suc n = unat (aa :: w256) \<Longrightarrow>
n = unat (aa - 1)
"
apply(rule HOL.sym)
apply(drule HOL.sym)
apply(rule unat_suc)
apply(simp)
done

lemma memory_range_elms_cut_memory :
       "\<forall> in_begin in_size.
        length lst = unat in_size \<longrightarrow> 
        memory_range_elms in_begin lst \<subseteq> variable_ctx_as_set x1 \<longrightarrow>
        cut_memory in_begin in_size (vctx_memory x1) = lst"
apply(induction lst)
   apply(simp add: unat_eq_0 )
apply(rule allI)
apply(rule allI)
apply(drule_tac x = "in_begin + 1" in spec)
apply(drule_tac x = "in_size - 1" in spec)
apply(clarsimp)
apply (erule impE)
 apply unat_arith
  apply (rule conjI)
   apply auto[1]
 apply (clarsimp simp add: as_set_simps)
done

lemma stack_height_in_topmost_means:
   "\<forall> h. StackHeightElm x1a \<in> stack_topmost_elms h lst = (x1a = h + length lst)"
apply(induction lst)
 apply(simp)
apply(auto simp add: )
done

lemma code_elm_not_stack_topmost :
 "\<forall> len. CodeElm x9
       \<notin> stack_topmost_elms len lst"
apply(induction lst)
 apply(auto)
done

lemma stack_elm_c_means :
  "StackElm x
       \<in> contexts_as_set v c =
   (
    rev (vctx_stack v) ! fst x = snd x \<and>
    fst x < length (vctx_stack v) )"
  by(force simp add: as_set_simps)

lemma stack_elm_in_topmost  :
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
 by(auto simp: nth_append) 

lemma code_elm_in_c :
  "CodeElm x9 \<in> contexts_as_set x1 co_ctx =
   (program_content (cctx_program co_ctx) (fst x9) = Some (snd x9) \<or>
    program_content (cctx_program co_ctx) (fst x9) = None \<and> snd x9 = Misc STOP)"
  by (case_tac x9, simp add: stateelm_equiv_simps)

    
    
lemma storage_not_stack_topmost:
   "StorageElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)

lemma log_not_topmost:
 "LogElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)

lemma caller_not_topmost:
  "CallerElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)

lemma origin_not_topmost :
  "OriginElm x13   \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)

lemma sent_value_not_topmost :
  "SentValueElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)

lemma sent_data_not_topmost:
 "SentDataElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)

lemma ext_program_size_not_topmost :
   "ExtProgramSizeElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)


lemma code_elm_c:
  "CodeElm x \<in> contexts_as_set y c = (CodeElm x \<in> constant_ctx_as_set c)"
apply(simp add: as_set_simps)
done

lemma ext_program_not_topmost_elms :
  " ExtProgramElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)



lemma block_hash_not_topmost:
  "BlockhashElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)


lemma block_number_not_topmost :
 "BlockNumberElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)


lemma coinbase_not_topmost:
  "CoinbaseElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)


lemma timestamp_not_topmost :
  "TimestampElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)


lemma difficulty_not_topmost:
  "DifficultyElm x \<notin> stack_topmost_elms len lst"
 by (auto dest: topmost_all)


lemma memory_range_gas_update :
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
   x \<in> variable_ctx_as_set
               (x1
                \<lparr>vctx_gas := g \<rparr>) =
   (x \<in> variable_ctx_as_set x1)"
   by (auto simp: as_set_simps dest: memory_range_elms_all)


lemma memory_range_stack :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (x1\<lparr>vctx_stack := sta\<rparr>)
      = (x \<in> variable_ctx_as_set x1)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)

lemma memory_range_memory_usage  :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (x1\<lparr>vctx_memory_usage := u\<rparr>)
      = (x \<in> variable_ctx_as_set x1)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)


lemma memory_range_balance :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (x1\<lparr>vctx_balance := u\<rparr>)
      = (x \<in> variable_ctx_as_set x1)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)

lemma memory_range_advance_pc :
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> variable_ctx_as_set (vctx_advance_pc co_ctx x1)
     = (x \<in> variable_ctx_as_set x1)
"
by (auto simp add: as_set_simps advance_pc_simps dest: memory_range_elms_all)

lemma memory_range_action :
      "x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> instruction_result_as_set co_ctx
             (InstructionToEnvironment
               act
               v
               cont) =
       (x \<in> variable_ctx_as_set v)"
by (auto simp add: instruction_result_as_set_def as_set_simps dest: memory_range_elms_all)

lemma storage_not_memory_range:
  "StorageElm x3 \<notin> memory_range_elms in_begin input"
  by (auto dest: memory_range_elms_all)

lemma memory_range_insert_cont :
   "memory_range_elms in_begin input
         \<subseteq> insert (ContinuingElm True) s =
    (memory_range_elms in_begin input
         \<subseteq> s)"
by (auto dest: memory_range_elms_all)

lemma memory_range_constant_union :
  "memory_range_elms in_begin input \<subseteq> constant_ctx_as_set co_ctx \<union> s =
   (memory_range_elms in_begin input \<subseteq> s)"
by (auto simp: as_set_simps dest: memory_range_elms_all)

lemma memory_range_elms_i :
      "memory_range_elms in_begin input
       \<subseteq> instruction_result_as_set co_ctx (InstructionContinue x1) =
       (memory_range_elms in_begin input \<subseteq>
        variable_ctx_as_set x1)"
by (auto simp: instruction_result_as_set_def as_set_simps dest: memory_range_elms_all)

lemma memory_range_continue:
"      x \<in> memory_range_elms in_begin input \<Longrightarrow>
       x \<in> instruction_result_as_set co_ctx (InstructionContinue x1) =
       (x \<in> variable_ctx_as_set x1)"
by (auto simp: instruction_result_as_set_def as_set_simps dest: memory_range_elms_all)
    
lemmas memory_range_simps = 
  memory_range_constant_union
  memory_range_insert_cont
  memory_range_elms_i
  memory_range_elms_not_account_existence
  memory_range_elms_not_code
  memory_range_elms_not_pc
  memory_range_elms_not_continuing
  memory_range_continue
  memory_range_advance_pc
  memory_range_balance
  memory_range_gas_update
  memory_range_memory_usage
  memory_range_stack
  memory_range_action

lemma call_memory_no_change:
  includes simp_for_triples_bundle
  shows
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
   x \<in> instruction_result_as_set co_ctx
         (subtract_gas (meter_gas (Misc CALL) x1 co_ctx net) memu (call net x1 co_ctx)) =
  (x \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
  apply (simp add: call_def)
  apply (auto simp: instruction_result_as_set_def dest: not_memory_range_elms_all split: list.splits)
    apply ((auto simp: as_set_simps advance_pc_simps dest: memory_range_elms_all)[1])+
done


lemma memory_call:
  includes simp_for_triples_bundle
  shows
  "x \<in> memory_range_elms in_begin input \<Longrightarrow>
    x \<in> instruction_result_as_set co_ctx (call net x1 co_ctx) =
    (x \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
  apply(simp add: call_def)
  apply (auto split: list.splits simp: memory_range_simps)
  done

lemma gas_limit_not_topmost:
  "GaslimitElm g  \<notin> stack_topmost_elms len lst"
by (auto dest: topmost_all)

lemma gas_price_not_topmost :
" GaspriceElm p \<notin> stack_topmost_elms len lst"
by (auto dest: topmost_all)

lemma fourth_last_pure :
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

lemma lookup_over_suc :
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
  

lemma lookup_over4 :
  "(rev listf @ a # b # c # d # e # rest) ! Suc (Suc (Suc (Suc (length listf))))
   = e"
  by (simp add: lookup_over_suc rev_nth_simps )

lemma lookup_over3 :
  "(rev listf @ a # b # c # d # lst) ! Suc (Suc (Suc (length listf))) = d"
  by (simp add: lookup_over_suc rev_nth_simps)


lemma memory_range_elms_in_minus_this:
  "memory_range_elms in_begin input
       \<subseteq> X - {ThisAccountElm t} =
   (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_minus_stackheight :
  "memory_range_elms in_begin input
       \<subseteq> X - {StackHeightElm h} =
   (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_minus_continuing :
  "memory_range_elms in_begin input
       \<subseteq> X - {ContinuingElm b} =
   (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_minus_gas  :
  "memory_range_elms in_begin input
       \<subseteq> X - {GasElm b} =
   (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_insert_continuing  :
  "(memory_range_elms in_begin input
   \<subseteq> insert (ContinuingElm b) X) =
  (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_insert_contract_action :
  "(memory_range_elms in_begin input
   \<subseteq> insert (ContractActionElm b) X) =
  (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)



lemma memory_range_elms_in_insert_gas :
  "(memory_range_elms in_begin input
   \<subseteq> insert (GasElm b) X) =
  (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_minus_stack:
  "memory_range_elms in_begin input
       \<subseteq> X -
          { StackElm pair } =
  (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto dest: memory_range_elms_all)

lemma minus_h :
  "x - {a, b, c, d, e, f, g, h} = 
   x - {a} - {b} - {c} - {d} - {e} - {f} - {g} - {h}"
apply auto
done

lemma stack_topmost_in_minus_balance :
  "stack_topmost_elms h lst \<subseteq> X - {BalanceElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma stack_topmost_in_minus_this:
  "stack_topmost_elms h lst \<subseteq> X - {ThisAccountElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)


lemma stack_topmost_in_minus_pc :
  "stack_topmost_elms h lst \<subseteq> X - {PcElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma stack_topmost_in_minus_memoryusage :
  "stack_topmost_elms h lst \<subseteq> X - {MemoryUsageElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma stack_topmost_in_minus_gas :
  "stack_topmost_elms h lst \<subseteq> X - {GasElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma stack_topmost_in_minus_continuing :
  "stack_topmost_elms h lst \<subseteq> X - {ContinuingElm b} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma stack_topmost_in_insert_cont :
  "stack_topmost_elms l lst \<subseteq> insert (ContinuingElm b) X =
   (stack_topmost_elms l lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma contract_action_not_stack_topmost :
  "ContractActionElm x19 \<notin> stack_topmost_elms l lst"
  by (auto dest: topmost_all)
    
lemma stack_topmost_in_insert_contractaction:
  "stack_topmost_elms l lst \<subseteq> insert (ContractActionElm a) X =
   (stack_topmost_elms l lst \<subseteq> X)"
  by (auto dest: topmost_all)

lemma stack_topmost_in_insert_gas  :
  "stack_topmost_elms l lst \<subseteq> insert (GasElm a) X =
   (stack_topmost_elms l lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma lognum_not_program:
 "LogNumElm x6 \<notin> program_as_set p"
apply(simp add: program_as_set_def)
done

lemma lognum_not_constant:
  "LogNumElm x6 \<notin> constant_ctx_as_set c"
apply(simp add: as_set_simps)
done

lemma stack_topmost_not_constant:
  "elm \<in> stack_topmost_elms h lst \<Longrightarrow> elm \<notin> constant_ctx_as_set c"
  by (auto dest!: topmost_all simp: as_set_simps )

lemma stack_topmost_in_c :
  "stack_topmost_elms h lst
       \<subseteq> contexts_as_set v c =
   (stack_topmost_elms h lst \<subseteq> variable_ctx_as_set v)"
by  (auto  dest: topmost_all simp: as_set_simps)

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

lemma drop_suc :
 "drop (Suc h) lst = drop 1 (drop h lst)"
  by simp

lemma drop_cons :
  "(drop h orig = a # lst) = 
   (orig ! h = a \<and> drop (Suc h) orig = lst \<and> length orig > h)"
apply(auto)
   apply (simp add: nth_via_drop)
  apply(simp only: drop_suc)
  apply(simp)
 using not_less apply fastforce
by (simp add: drop_eq_cons_when)

lemma topmost_elms_in_vctx_means:
  "\<forall> h v. stack_topmost_elms h lst
       \<subseteq> variable_ctx_as_set v =
  ((length (vctx_stack v) = h + length lst \<and> drop h (rev (vctx_stack v)) = lst))"
  apply(induction lst; simp add: as_set_simps)
   apply fastforce
apply(clarsimp simp add: drop_cons)
apply blast
done
  
lemma memory_range_not_stack_topmost:
  "x \<in> memory_range_elms in_begin input \<Longrightarrow> x \<notin> stack_topmost_elms h lst"
  by  (auto simp: as_set_simps dest: topmost_all memory_range_elms_all)
    
lemma memory_range_elms_in_minus_statck_topmost  :
  "memory_range_elms in_begin input
       \<subseteq> X -
          stack_topmost_elms h lst =
   (memory_range_elms in_begin input \<subseteq> X)"
  by  (auto simp: as_set_simps dest: topmost_all memory_range_elms_all)

lemma memory_range_elms_in_c :
  "memory_range_elms in_begin input
       \<subseteq> contexts_as_set v c =
  (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
by (auto simp: as_set_simps dest: topmost_all memory_range_elms_all)

lemma memory_usage_not_ext_program  :
  "MemoryUsageElm u \<notin> ext_program_as_set e"
 by  (auto simp: as_set_simps)
    
lemma memory_usage_not_balance  :
  "MemoryUsageElm u \<notin> balance_as_set b"
apply(simp add: balance_as_set_def)
done

lemma variable_ctx_as_set_updte_mu:
  "variable_ctx_as_set (v\<lparr>vctx_memory_usage := u\<rparr>) =
   variable_ctx_as_set v - {MemoryUsageElm (vctx_memory_usage v)} \<union> {MemoryUsageElm u}"
by (auto simp: as_set_simps dest: topmost_all memory_range_elms_all)


lemma memory_range_elms_in_mu :
  "memory_range_elms in_begin input \<subseteq> insert (MemoryUsageElm u) X =
   (memory_range_elms in_begin input \<subseteq> X)"
by (auto dest: memory_range_elms_all)


lemma sent_data_not_in_mr :
 "SentDataElm x16 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)


lemma ext_program_not_in_mr :
  "ExtProgramSizeElm x17 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)


lemma ext_pr_not_in_mr :
  "ExtProgramElm x18 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma blockhash_not_in_mr :
  "BlockhashElm x21 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma blocknumber_not_in_mr :
  "BlockNumberElm x22 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma coinbase_not_in_mr :
  "CoinbaseElm x23 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma timestamp_not_in_mr :
  "TimestampElm x24 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma difficulty_not_in_mr :
"DifficultyElm x25 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma gaslimit_not_in_mr :
"GaslimitElm x26 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma gasprice_not_in_mr  :
  "GaspriceElm x27 \<notin> memory_range_elms in_begin input"
by (auto dest: memory_range_elms_all)

lemma memory_range_elms_in_minus_mu :
  "memory_range_elms in_begin input \<subseteq> X - {MemoryUsageElm u} =
  (memory_range_elms in_begin input \<subseteq> X)"
 by  (auto  dest: memory_range_elms_all)


lemma memory_range_elms_update_memory_usage  :
  "memory_range_elms in_begin input \<subseteq>
    variable_ctx_as_set
           (v\<lparr>vctx_memory_usage := u\<rparr>) =
   (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)


lemma memory_range_in_caller  :
  "memory_range_elms in_begin input
     \<subseteq> insert (CallerElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)

lemma memory_range_in_sent_value  :
  "memory_range_elms in_begin input
     \<subseteq> insert (SentValueElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
 by (auto simp: as_set_simps dest: memory_range_elms_all)

lemma memory_range_in_origin  :
  "memory_range_elms in_begin input
     \<subseteq> insert (OriginElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)

lemma memory_range_in_pc  :
  "memory_range_elms in_begin input
     \<subseteq> insert (PcElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)

lemma memory_range_in_coinbase  :
  "memory_range_elms in_begin input
     \<subseteq> insert (CoinbaseElm c) X =
   (memory_range_elms in_begin input \<subseteq> X)"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)

lemma vset_update_balance  :
  "variable_ctx_as_set
           (v\<lparr>vctx_balance := u\<rparr>) =
   variable_ctx_as_set v - balance_as_set (vctx_balance v) \<union> balance_as_set u"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)

lemma memory_range_elms_update_balance  :
  "memory_range_elms in_begin input \<subseteq>
    variable_ctx_as_set
           (v\<lparr>vctx_balance := u\<rparr>) =
   (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
 by  (auto simp: as_set_simps dest: memory_range_elms_all)


lemma small_min :
  "Suc n < h \<Longrightarrow>
   min (h - Suc 0) n = n"
apply auto
done

lemma sucsuc_minus_two :
  "h > 1 \<Longrightarrow>
   Suc (Suc (h - 2)) = h"
apply auto
done

lemma minus_one_bigger:
  "h > 1 \<Longrightarrow>
   h - Suc (Suc n) \<noteq> h - Suc 0"
apply auto
done

lemma storage_elm_kept_by_gas_update :
  includes simp_for_triples_bundle
  shows
 "StorageElm x3
  \<in> instruction_result_as_set co_ctx (InstructionContinue
     (x1\<lparr>vctx_gas := g - Gverylow\<rparr>)) =
  (StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: instruction_result_as_set_def as_set_simps)
done

lemma storage_elm_kept_by_stack_updaate :
  "StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue (x1\<lparr>vctx_stack := s\<rparr>))
 = (StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: instruction_result_as_set_def as_set_simps)
done

lemma advance_pc_keeps_storage_elm:
  "StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue (vctx_advance_pc co_ctx x1)) =
  (StorageElm x3 \<in> instruction_result_as_set co_ctx (InstructionContinue x1))"
apply(simp add: instruction_result_as_set_def as_set_simps advance_pc_simps)
done

lemma rev_drop  :
"a < length lst - n \<Longrightarrow>
 rev (drop n lst) ! a = rev lst ! a"
	by (simp add: rev_drop)

lemma less_than_minus_two  :
  "1 < h \<Longrightarrow>
   a < h - Suc (Suc (unat n)) \<Longrightarrow> a < Suc (h - 2)"
apply auto
done

lemma suc_minus_two  :
  "1 < h \<Longrightarrow>
   Suc (h - 2) = h - Suc 0"
apply auto
done

lemma minus_one_two  :
 "1 < h \<Longrightarrow>
  h - Suc 0 \<noteq> h - Suc (Suc n)"
apply auto
done

lemma minus_two_or_less  :
  "a < h - Suc n \<Longrightarrow>  a < h - Suc 0"
apply auto
done

lemma min_right  :
 "(n :: nat) \<le> m \<Longrightarrow> min m n = n"
apply (simp add: min_def)
done


lemma rev_take_nth  :
  "n \<le> length lst \<Longrightarrow>
   k < n \<Longrightarrow>
   rev (take n lst) ! k =  lst ! (n - k - 1)"
  by(auto simp add: List.rev_nth min.absorb2)

lemma stack_topmost_in_insert_memory_usage :
  "stack_topmost_elms h lst
       \<subseteq> insert (MemoryUsageElm u) X =
  (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma memory_gane_elms_in_stack_update  :
  "memory_range_elms in_begin input \<subseteq> variable_ctx_as_set (v\<lparr>vctx_stack := tf\<rparr>) =
  (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set v)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)

lemma stack_topmost_in_minus_balance_as  :
  "stack_topmost_elms h lst
       \<subseteq> X - balance_as_set b =
  (stack_topmost_elms h lst \<subseteq> X)"
by (auto simp add: as_set_simps dest: topmost_all)

lemma stack_topmost_in_union_balance  :
  "stack_topmost_elms h lst
       \<subseteq> X \<union> balance_as_set b =
  (stack_topmost_elms h lst \<subseteq> X)"
by (auto simp add: as_set_simps dest: topmost_all)


lemma memory_range_in_minus_balance_as  :
  "memory_range_elms h lst
       \<subseteq> X - balance_as_set b =
  (memory_range_elms h lst \<subseteq> X)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)


lemma memory_range_in_union_balance  :
  "memory_range_elms h lst
       \<subseteq> X \<union> balance_as_set b =
  (memory_range_elms h lst \<subseteq> X)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)


lemma memory_range_in_minus_balance  :
  "memory_range_elms h lst
    \<subseteq> X - {BalanceElm pair} =
   (memory_range_elms h lst \<subseteq> X)"
by (auto simp add: as_set_simps dest: memory_range_elms_all )


lemma memory_range_advance  :
  "memory_range_elms in_begin input \<subseteq> variable_ctx_as_set (vctx_advance_pc co_ctx x1) =
  (memory_range_elms in_begin input \<subseteq> variable_ctx_as_set x1)"
by (auto simp add: as_set_simps advance_pc_simps dest: memory_range_elms_all)


lemma update_balance_match  :
  "update_balance a f b a = f (b a)"
apply(simp add: update_balance_def)
done 

lemma lookup_o[simp] :
  "a \<ge> length tf \<Longrightarrow>
   (rev tf @ lst) ! a
   = lst ! (a - length tf)"
	by (simp add: rev_append_eq)

lemma update_balance_no_change  :
  "update_balance changed f original a = original a =
   (changed \<noteq> a \<or> (changed = a \<and> f (original a) = original a))"
apply(auto simp add: update_balance_def)
done

lemma update_balance_changed  :
  "original a \<noteq> update_balance changed f original a =
  (changed = a \<and> f (original a) \<noteq> original a)"
apply(auto simp add: update_balance_def)
done


lemma pair_snd_eq[simp]: 
 "x3 \<noteq> (idx, snd x3) =
  (fst x3 \<noteq> idx)"
apply (case_tac x3; auto)
done


lemma log_num_memory_usage  :
  "LogNumElm x6
       \<in> contexts_as_set
           (v
            \<lparr> vctx_memory_usage := m \<rparr>) co_ctx =
   (LogNumElm x6 \<in> contexts_as_set v co_ctx)"
apply(simp add: as_set_simps)
done

lemma log_num_not_balance  :
  "LogNumElm x6 \<notin> balance_as_set b"
by (auto dest: balance_all)


lemma log_num_balance_update  :
  "LogNumElm x6
       \<in> contexts_as_set
           (v \<lparr>vctx_balance := b\<rparr>) co_ctx =
   (LogNumElm x6 \<in> contexts_as_set v co_ctx)"
apply(simp add: as_set_simps)
done

lemma log_num_not_stack_topmost  :
  "\<forall> n. LogNumElm x6 \<notin> stack_topmost_elms n lst"
apply(induction lst)
 apply(simp add: stack_topmost_elms.simps)
apply(simp add: stack_topmost_elms.simps)
done

lemma log_num_not_stack  :
  "LogNumElm x6 \<notin> stack_as_set tf"
apply(simp add: stack_as_set_def)
done

lemma contract_action_not_vctx  :
  "ContractActionElm x19 \<notin> variable_ctx_as_set x1"
by (auto simp add: as_set_simps)


lemma continuing_not_vctx  :
  "ContinuingElm b \<notin> variable_ctx_as_set v"
by (auto simp add: as_set_simps)

lemma log_num_not_ext_program  :
  "LogNumElm x6 \<notin> ext_program_as_set e"
by (auto simp add: as_set_simps)


lemma log_num_elm_means  :
  "LogNumElm x6 \<in> contexts_as_set x1 co_ctx =
   (length (vctx_logs x1) = x6)"
by (auto simp add: as_set_simps)


lemma log_num_in_v_means  :
 "LogNumElm x6 \<in> variable_ctx_as_set v =
  (length (vctx_logs v) = x6)"
by (auto simp add: as_set_simps)


lemma account_existence_means_v  :
  "AccountExistenceElm x29 \<in> variable_ctx_as_set v =
   (vctx_account_existence v (fst x29) = snd x29)"
by (simp add:account_existence_elm_means)

lemma account_existence_not_stack  :
  "AccountExistenceElm p \<notin> stack_as_set ta"
by (simp add: stack_as_set_def)

lemma vctx_gas_changed  :
   "variable_ctx_as_set
             (v \<lparr> vctx_gas := g \<rparr>) =
    variable_ctx_as_set v - { GasElm (vctx_gas v)} \<union> { GasElm g }"
apply(simp)
apply(rule Set.equalityI)
 apply(clarify)
 apply(simp)
 apply(rename_tac elm)
 apply(case_tac elm; simp add: as_set_simps)
apply(clarify)
apply(simp)
apply(rename_tac elm)
apply(case_tac elm; simp add:as_set_simps)
done

lemma lognum_not_stack_topmost :
  "LogNumElm n \<notin> stack_topmost_elms h lst"
by (auto dest: topmost_all)

lemma stack_topmost_minus_lognum  :
   "stack_topmost_elms h lst \<subseteq> X - {LogNumElm n} =
   (stack_topmost_elms h lst \<subseteq> X)"
by (auto dest: topmost_all)

lemma vctx_pc_log_advance  :
  includes simp_for_triples_bundle
  shows
  "program_content (cctx_program co_ctx) k = Some (Log LOGx) \<Longrightarrow>
   vctx_pc v = k \<Longrightarrow>
   vctx_pc
     (vctx_advance_pc co_ctx v) =
   vctx_pc v + 1"
by (simp add: vctx_advance_pc_def inst_size_def inst_code.simps)

lemma memory_range_elms_in_x_minus_lognum  :
  "memory_range_elms in_begin data \<subseteq> X - {LogNumElm n} =
   (memory_range_elms in_begin data \<subseteq> X)"
by (auto dest: memory_range_elms_all)

lemma memory_range_elms_logs_update  :
  "memory_range_elms in_begin data
             \<subseteq> variable_ctx_as_set (x1\<lparr>vctx_logs := ls\<rparr>) =
  (memory_range_elms in_begin data
             \<subseteq> variable_ctx_as_set x1)"
by (auto simp add: as_set_simps dest: memory_range_elms_all)


lemma log0_create_logs  :
   "vctx_stack x1 = logged_start # logged_size # ta  \<Longrightarrow>
    length data = unat logged_size \<Longrightarrow>
    memory_range_elms logged_start data \<subseteq> variable_ctx_as_set x1  \<Longrightarrow>
    create_log_entry 0 x1 co_ctx = \<lparr>log_addr = cctx_this co_ctx, log_topics = [], log_data = data\<rparr>"
apply(auto simp add: create_log_entry_def vctx_returned_bytes_def memory_range_elms_cut_memory)
done


lemma default_zero[simp]:
  "vctx_stack x1 = idx # ta \<Longrightarrow>
   vctx_stack_default 0 x1 = idx"
apply(simp add: vctx_stack_default_def)
done

lemma default_one[simp]:
  "vctx_stack x1 = idx # y # ta \<Longrightarrow>
   vctx_stack_default 1 x1 = y"
apply(simp add: vctx_stack_default_def)
done
    
lemma set_diff_expand:
  "x - {a,b,c} = x - {a} - {b} - {c}"
  "x - {a,b,c,d} = x - {a} - {b} - {c} - {d}"
  "x - {a,b,c,d,e} = x - {a} - {b} - {c} - {d} - {e}"
  "x - {a,b,c,d,e,f} = x - {a} - {b} - {c} - {d} - {e}- {f} "
  "x - {a,b,c,d,e,f,g} = x - {a} - {b} - {c} - {d} - {e} - {f} - {g}"
  "x - {a,b,c,d,e,f,g,h} = x - {a} - {b} - {c} - {d} - {e} - {f} - {g} - {h}"
  "x - {a,b,c,d,e,f,g,h,i} = x - {a} - {b} - {c} - {d} - {e} - {f} - {g} - {h} - {i}"
  "x - {a,b,c,d,e,f,g,h,i,j} = x - {a} - {b} - {c} - {d} - {e} - {f} - {g} - {h} - {i} - {j}"
  by blast+

lemma insert_minus_set:
 "x \<notin> t \<Longrightarrow> insert x s - t = insert x (s - t)"
  by blast

lemmas sep_tools_simps =
 emp_sep sep_true pure_sepD pure_sep 
 imp_sepL sep_impL

lemmas sep_fun_simps =
caller_sep  sep_caller sep_caller_sep
balance_sep sep_balance sep_balance_sep
not_continuing_sep sep_not_continuing_sep
this_account_sep sep_this_account sep_this_account_sep
action_sep sep_action sep_action_sep
memory8_sep
memory_usage_sep sep_memory_usage sep_memory_usage_sep
memory_range_sep sep_memory_range
continuing_sep sep_continuing_sep
gas_pred_sep sep_gas_pred
gas_any_sep sep_gas_any_sep
program_counter_sep sep_program_counter sep_program_counter_sep
stack_height_sep sep_stack_height sep_stack_height_sep
stack_sep sep_stack sep_stack_sep
block_number_pred_sep sep_block_number_pred_sep
sep_log_number_sep sep_logged
storage_sep sep_storage
code_sep sep_code sep_sep_code sep_code_sep
sent_data_sep
sent_value_sep

lemmas inst_numbers_simps =
dup_inst_numbers_def storage_inst_numbers.simps stack_inst_numbers.simps
pc_inst_numbers.simps info_inst_numbers.simps inst_stack_numbers.simps
arith_inst_numbers.simps misc_inst_numbers.simps swap_inst_numbers_def
memory_inst_numbers.simps log_inst_numbers.simps bits_stack_nums.simps
sarith_inst_nums.simps

lemmas inst_size_simps =
inst_size_def inst_code.simps stack_inst_code.simps

lemmas stack_nb_simps=
stack_0_0_op_def stack_0_1_op_def stack_1_1_op_def
stack_2_1_op_def stack_3_1_op_def

lemmas gas_value_simps =
Gjumpdest_def Gzero_def Gbase_def Gcodedeposit_def Gcopy_def
Gmemory_def Gverylow_def Glow_def Gsha3word_def Gcall_def
Gtxcreate_def Gtxdatanonzero_def Gtxdatazero_def Gexp_def
Ghigh_def Glogdata_def Gmid_def Gblockhash_def Gsha3_def
Gsreset_def Glog_def Glogtopic_def  Gcallstipend_def Gcallvalue_def
Gcreate_def Gnewaccount_def Gtransaction_def Gexpbyte_def
Gsset_def Gsuicide_def Gbalance_def Gsload_def Gextcode_def

lemmas instruction_sem_simps =
instruction_sem_def constant_mark_def
stack_0_0_op_def stack_0_1_op_def stack_1_1_op_def
stack_2_1_op_def stack_3_1_op_def
subtract_gas.simps
new_memory_consumption.simps
check_resources_def
meter_gas_def C_def Cmem_def
thirdComponentOfC_def
vctx_next_instruction_default_def vctx_next_instruction_def
blockedInstructionContinue_def vctx_pop_stack_def
blocked_jump_def strict_if_def 

lemmas advance_simps =
vctx_advance_pc_def vctx_next_instruction_def

bundle sep_crunch_bundle =
  caller_sep[simp]
  sep_caller[simp]
  sep_caller_sep[simp]
  balance_sep[simp]
  sep_balance[simp]
  sep_balance_sep[simp]
  not_continuing_sep[simp]
  sep_not_continuing_sep[simp]
  this_account_sep[simp]
  sep_this_account[simp]
  sep_this_account_sep[simp]
  action_sep[simp]
  sep_action[simp]
  sep_action_sep[simp]
  sep_stack_topmost[simp]
  sep_account_existence_sep[simp]
  sep_account_existence[simp]
  account_existence_sep[simp]
  sep_sep_account_existence_sep[simp]
  sep_conj_assoc[simp]

lemmas not_context_simps = 
   continuing_not_context
   action_not_context

lemmas evm_simps = (* general category of EVM simp rules *)
  advance_pc_advance

lemmas constant_diff =
  constant_diff_gas
  constant_diff_pc
  constant_diff_stack
  constant_diff_stack_height
  
lemma stateelm_constant_all:
  "P \<in> constant_ctx_as_set ctx \<Longrightarrow> P \<in> range CodeElm \<union> range ThisAccountElm"
by (auto simp add: as_set_simps)

lemma stateelm_not_constant_all:
  "P \<notin> range CodeElm \<union> range ThisAccountElm \<Longrightarrow> P \<notin> constant_ctx_as_set ctx"
  by (auto simp add: as_set_simps)
    
lemma not_variable_all:
  "ThisAccountElm t  \<notin> variable_ctx_as_set v"
  "CodeElm e \<notin> variable_ctx_as_set v"
  by (auto simp: as_set_simps)
    
lemma ext_all:
  "P \<in> ext_program_as_set x \<Longrightarrow> P \<in> range ExtProgramSizeElm \<union> range ExtProgramElm"
 by (auto simp add: as_set_simps)

lemma not_ext_all:
  "P \<notin> range ExtProgramSizeElm \<union> range ExtProgramElm \<Longrightarrow> P \<notin> ext_program_as_set x"
  by (auto simp add: as_set_simps)

lemmas as_set_plus_simps = 
  gas_change_as_set
  advance_pc_as_set
  stack_change_as_set
  variable_ctx_as_set_updte_mu
  
lemmas stateelm_dest = 
  stateelm_constant_all
  stateelm_not_constant_all
  stateelm_program_all
  stateelm_not_program_all
  balance_all
  not_balance_all
  memory_range_elms_all
  not_memory_range_elms_all
  stack_all
  not_stack_all
  topmost_all
  not_topmost_all
  ext_all
  not_ext_all

lemma gasprice_advance_pc [simp]:
 "vctx_gasprice
        (vctx_advance_pc co_ctx x) = vctx_gasprice x"
by(simp add: vctx_advance_pc_def)

lemmas stateelm_subset_diff_elim =
  memory_range_in_minus_balance
  memory_range_elms_in_x_minus_lognum
  memory_range_elms_in_minus_continuing
  memory_range_elms_in_minus_gas
  memory_range_elms_in_minus_mu
  memory_range_elms_in_minus_stack
  memory_range_elms_in_minus_stackheight
  memory_range_elms_in_minus_this
  memory_range_elms_not_account_existence
  memory_range_elms_not_code
  memory_range_elms_not_pc
  stack_topmost_in_minus_balance
  stack_topmost_in_minus_continuing
  stack_topmost_in_minus_gas
  stack_topmost_minus_lognum
  stack_topmost_in_minus_memoryusage
  stack_topmost_in_minus_pc
  stack_topmost_in_minus_this
  stack_topmost_not_account_existence
  stack_topmost_not_pc
  stack_topmost_not_code
  
lemmas extra_sep=
  block_number_pred_sep
  sep_block_number_pred_sep

lemmas stateelm_means_simps =
pc_not_balance
caller_elm_means
gas_element_means
origin_element_means
pc_element_means
sent_value_means
block_number_elm_in_v_means
coinbase_elm_means
difficulty_elm_means
gaslimit_elm_means
gasprice_elm_means
log_num_in_v_means
stack_height_element_means
timestamp_elm_means
caller_elm_means_c
orogin_elm_c_means
sent_value_c_means
this_account_means
block_number_elm_c_means
coinbase_c_means
difficulty_c_means
gasprice_c_means
log_num_elm_means
timestamp_c_means
gas_elm_i_means
pc_elm_means
this_account_i_means
account_existence_elm_means
account_existence_means_v
balance_elm_means
memory_element_means
memory_usage_element_means
storage_element_means
block_number_elm_means
stack_heigh_elm_means
blockhash_elm_means
ext_program_size_elm_means
account_existence_elm_means_c
balance_elm_c_means
memory_elm_means
memory_usage_elm_means
memory_usage_elm_c_means
storage_elm_means
stack_height_in_topmost_means
blockhash_c_means
ext_program_size_c_means
balance_elm_i_means
ext_program_elm_means
ext_program_c_means
sent_data_means
log_element_means
stack_element_means
sent_data_elm_c_means
log_elm_means
stack_elm_c_means
stack_element_notin_means
stack_elm_means
topmost_elms_in_vctx_means
topmost_elms_means
code_element_means
code_elm_means
stack_as_set_cons_means
gaslimit_elm_c
code_elm_c

lemmas evm_sep =
pure_sep
continuing_sep
not_continuing_sep
action_sep
block_number_pred_sep
caller_sep
gas_pred_sep
memory_usage_sep
program_counter_sep
stack_height_sep
this_account_sep
gas_any_sep
stack_topmost_sep
account_existence_sep
balance_sep
memory8_sep
stack_sep
storage_sep
memory_range_sep
code_sep
sent_data_sep
sent_value_sep

lemmas constant_diff_simps =
  constant_diff_gas
  constant_diff_pc
  constant_diff_stack
  constant_diff_stack_height

bundle hoare_inst_bundle =
continuing_not_context[simp]
caller_elm_means[simp]
advance_pc_advance[simp]
advance_pc_no_gas_change[simp]
constant_diff_stack_height[simp]
constant_diff_stack[simp]
constant_diff_pc[simp]
constant_diff_gas[simp]
stack_height_element_means[simp]
stack_element_means[simp]
stack_element_notin_means[simp]
storage_element_means[simp]
memory_element_means[simp]
pc_not_balance[simp]
pc_element_means[simp]
gas_element_means[simp]
log_element_means[simp]
memory_usage_element_means[simp]
code_element_means[simp]
origin_element_means[simp]
sent_value_means[simp]
sent_data_means[simp]
inst_size_nonzero[simp]
advance_pc_different[simp]
stack_elm_not_program[simp]
stack_elm_not_constant[simp]
storage_elm_not_constant[simp]
stack_height_elm_not_constant[simp]
memory_elm_not_constant[simp]
pc_elm_not_constant[simp]
gas_elm_not_constant[simp]
contract_action_elm_not_constant[simp]
code_elm_not_variable[simp]
this_account_elm_not_variable[simp]
rev_append[simp]
rev_append_inv[simp]
rev_rev_append[simp]
over_one[simp]
over_one_rev[simp]
over_one_rev'[simp]
over_two[simp]
over_two_rev[simp]
advance_pc_preserves_storage[simp]
advance_pc_preserves_memory[simp]
advance_pc_preserves_logs[simp]
advance_pc_preserves_memory_usage[simp]
advance_pc_preserves_balance[simp]
advance_pc_preserves_caller[simp]
advance_pc_preserves_value_sent[simp]
advance_pc_preserves_origin[simp]
advance_pc_preserves_block[simp]
balance_elm_means[simp]
advance_pc_keeps_stack[simp]
advance_pc_change[simp]
sep_caller_sep[simp]
Gverylow_positive[simp]
saying_zero[simp]
inst_size_pop[simp]
pop_advance[simp]
advance_pc_as_set[simp]
gas_change_as_set[simp]
stack_change_as_set[simp]
stack_height_in[simp]
pc_not_stack[simp]
code_not_stack[simp]
action_not_context[simp]
failed_is_failed[simp]
stack_height_increment[simp]
stack_inc_element[simp]
caller_elm_means_c[simp]
continue_not_failed[simp]
info_single_advance[simp]
caller_not_stack[simp]
advance_keeps_storage_elm[simp]
advance_keeps_memory_elm[simp]
advance_keeps_log_elm[simp]
advance_keeps_memory_usage_elm[simp]
advance_keeps_this_account_elm[simp]
advance_keeps_balance_elm[simp]
advance_keeps_origin_elm[simp]
advance_keeps_sent_value_elm[simp]
data_sent_advance_pc[simp]
advance_keeps_sent_data_elm[simp]
ext_program_size_not_constant[simp]
ext_program_size_elm_means[simp]
ext_program_size_c_means[simp]
ext_program_advance_pc[simp]
advance_keeps_ext_program_size_elm[simp]
ext_program_elm_not_constant[simp]
ext_program_elm_means[simp]
ext_program_c_means[simp]
advance_keeps_ext_program_elm[simp]
blockhash_not_constant[simp]
blockhash_elm_means[simp]
blockhash_c_means[simp]
advance_keeps_blockhash_elm[simp]
coinbase_elm_not_constant[simp]
coinbase_elm_means[simp]
coinbase_c_means[simp]
advance_keeps_conbase_elm[simp]
timestamp_not_constant[simp]
timestamp_elm_means[simp]
timestamp_c_means[simp]
advance_keeps_timestamp_elm[simp]
difficulty_not_constant[simp]
difficulty_elm_means[simp]
difficulty_c_means[simp]
advance_keeps_difficulty_elm[simp]
gaslimit_not_constant[simp]
gaslimit_elm_means[simp]
gaslimit_elm_c[simp]
advance_keeps_gaslimit_elm[simp]
gasprice_not_constant[simp]
gasprice_elm_means[simp]
gasprice_c_means[simp]
advance_keeps_gasprice_elm[simp]
stackheight_different[simp]
stack_element_in_stack[simp]
storage_not_stack[simp]
memory_not_stack[simp]
log_not_stack[simp]
gas_not_stack[simp]
memory_usage_not_stack[simp]
this_account_not_stack[simp]
balance_not_stack[simp]
code_elm_means[simp]
pc_elm_means[simp]
block_number_pred_sep[simp]
sep_block_number_pred_sep[simp]
block_number_elm_not_constant[simp]
block_number_elm_in_v_means[simp]
block_number_elm_means[simp]
stack_heigh_elm_means[simp]
stack_elm_means[simp]
balance_not_constant[simp]
balance_elm_i_means[simp]
gas_elm_i_means[simp]
continuing_continuing[simp]
origin_not_stack[simp]
sent_value_not_stack[simp]
ext_program_not_stack[simp]
sent_data_not_stack[simp]
contract_action_elm_not_stack[simp]
block_number_elm_c_means[simp]
log_num_v_advance[simp]
log_num_advance[simp]
account_existence_not_in_constant[simp]
account_existence_not_in_stack[simp]
account_existence_not_in_balance[simp]
account_existence_not_ext[simp]
account_existence_elm_means[simp]
account_existence_elm_means_c[simp]
account_existence_advance[simp]
account_existence_advance_v[simp]
balance0[simp]
ext_program_size_elm_not_stack[simp]
continuing_not_stack[simp]
block_hash_not_stack[simp]
block_number_not_stack[simp]
coinbase_not_stack[simp]
timestamp_not_stack[simp]
difficulty_not_stack[simp]
gaslimit_not_stack[simp]
gasprice_not_stack[simp]
ext_program_size_not_stack[simp]
advance_keeps_stack_elm[simp]
advance_keeps_code_elm[simp]
storage_elm_means[simp]
memory_elm_means[simp]
log_not_constant[simp]
log_elm_means[simp]
this_account_means[simp]
balance_elm_c_means[simp]
origin_not_constant[simp]
orogin_elm_c_means[simp]
sent_value_not_constant[simp]
sent_value_c_means[simp]
sent_data_not_constant[simp]
sent_data_elm_c_means[simp]
short_rev_append[simp]
memory_usage_not_constant[simp]
code_elms[simp]
memory_usage_elm_means[simp]
pc_update_v[simp]
pc_update[simp]
stack_as_set_cons_means[simp]
cut_memory_zero[simp]
cut_memory_aux_cons[simp]
cut_memory_cons[simp]
Hoare.memory8_sep[simp]
meter_gas_def[simp]
C_def[simp]
Cmem_def[simp]
Gmemory_def[simp]
new_memory_consumption.simps[simp]
thirdComponentOfC_def[simp]
subtract_gas.simps[simp]
vctx_next_instruction_default_def[simp]
stack_2_1_op_def[simp]
stack_1_1_op_def[simp]
stack_0_0_op_def[simp]
inst_stack_numbers.simps[simp]
arith_inst_numbers.simps[simp]
program_sem.simps[simp]
vctx_next_instruction_def[simp]
instruction_sem_def[simp]
check_resources_def[simp]
info_inst_numbers.simps[simp]
Gbalance_def[simp]
stack_inst_numbers.simps[simp]
pc_inst_numbers.simps[simp]
pop_def[simp]
jump_def[simp]
jumpi_def[simp]
instruction_failure_result_def[simp]
strict_if_def[simp]
blocked_jump_def[simp]
blockedInstructionContinue_def[simp]
vctx_pop_stack_def[simp]
stack_0_1_op_def[simp]
general_dup_def[simp]
dup_inst_numbers_def[simp]
storage_inst_numbers.simps[simp]
Gbase_def[simp]
Gsreset_def[simp]
emp_sep[simp]
no_overwrap[simp]
continuing_not_memory_range[simp]
contractaction_not_memory_range[simp]
pc_not_memory_range[simp]
this_account_not_memory_range[simp]
balance_not_memory_range[simp]
code_not_memory_range[simp]
continuing_not_memory_range[simp]
stack_not_memory_range[simp]
stack_height_not_memory_range[simp]
gas_not_memory_range[simp]
misc_inst_numbers.simps[simp]
stack_topmost_sep[simp]
fourth_stack_topmost[simp]
this_account_not_stack_topmost[simp]
gas_not_stack_topmost[simp]
stack_topmost_empty[simp]
memory_range_elms_not_pc[simp]
account_ex_is_not_memory_range[simp]
memory_range_elms_not_account_existence[simp]
memory_range_elms_not_code[simp]
memory_not_stack_topmost[simp]
stack_topmost_not_memory[simp]
pc_not_stack_topmost[simp]
stack_topmost_not_pc[simp]
ae_not_stack_topmost[simp]
stack_topmost_not_account_existence[simp]
stack_topmost_not_code[simp]
memory_usage_not_memory_range[simp]
stack_height_after_call[simp]
topmost_elms_means[simp]
to_environment_not_continuing[simp]
balance_not_topmost[simp]
continue_not_topmost[simp]
this_account_i_means[simp]
memory_usage_not_memory_range[simp]
memory_usage_not_topmost[simp]
call_new_balance[simp]
advance_pc_call[simp]
memory_range_elms_not_continuing[simp]
memory_range_elms_cut_memory[simp]
stack_height_in_topmost_means[simp]
code_elm_not_stack_topmost[simp]
stack_elm_c_means[simp]
stack_elm_in_topmost[simp]
storage_not_stack_topmost[simp]
log_not_topmost[simp]
caller_not_topmost[simp]
origin_not_topmost[simp]
sent_value_not_topmost[simp]
sent_data_not_topmost[simp]
ext_program_size_not_topmost[simp]
code_elm_c[simp]
ext_program_not_topmost_elms[simp]
block_hash_not_topmost[simp]
block_number_not_topmost[simp]
coinbase_not_topmost[simp]
timestamp_not_topmost[simp]
difficulty_not_topmost[simp]
memory_range_gas_update[simp]
lognum_not_memory[simp]
account_existence_not_memory[simp]
memory_range_stack[simp]
memory_range_memory_usage[simp]
memory_range_balance[simp]
memory_range_advance_pc[simp]
memory_range_action[simp]
storage_not_memory_range[simp]
memory_range_insert_cont[simp]
memory_range_constant_union[simp]
memory_range_elms_i[simp]
memory_range_continue[simp]
call_memory_no_change[simp]
memory_call[simp]
gas_limit_not_topmost[simp]
gas_price_not_topmost[simp]
fourth_last_pure[simp]
lookup_over_suc[simp]
lookup_over4[simp]
lookup_over3[simp]
memory_range_elms_in_minus_this[simp]
memory_range_elms_in_minus_stackheight[simp]
memory_range_elms_in_minus_continuing[simp]
memory_range_elms_in_minus_gas[simp]
log_not_memory_range[simp]
caller_not_memory_range[simp]
origin_not_memory_range[simp]
sent_value_not_memory_range[simp]
memory_range_elms_in_insert_continuing[simp]
memory_range_elms_in_insert_contract_action[simp]
memory_range_elms_in_insert_gas[simp]
memory_range_elms_in_minus_stack[simp]
minus_h[simp]
stack_topmost_in_minus_balance[simp]
stack_topmost_in_minus_this[simp]
stack_topmost_in_minus_pc[simp]
stack_topmost_in_minus_memoryusage[simp]
stack_topmost_in_minus_gas[simp]
stack_topmost_in_minus_continuing[simp]
stack_topmost_in_insert_cont[simp]
contract_action_not_stack_topmost[simp]
stack_topmost_in_insert_contractaction[simp]
stack_topmost_in_insert_gas[simp]
lognum_not_program[simp]
lognum_not_constant[simp]
stack_topmost_not_constant[simp]
stack_topmost_in_c[simp]
topmost_elms_in_vctx_means[simp]
memory_range_not_stack_topmost[simp]
memory_range_elms_in_minus_statck_topmost[simp]
memory_range_elms_in_c[simp]
memory_usage_not_ext_program[simp]
memory_usage_not_balance[simp]
variable_ctx_as_set_updte_mu[simp]
memory_range_elms_in_mu[simp]
sent_data_not_in_mr[simp]
ext_program_not_in_mr[simp]
ext_pr_not_in_mr[simp]
blockhash_not_in_mr[simp]
blocknumber_not_in_mr[simp]
coinbase_not_in_mr[simp]
timestamp_not_in_mr[simp]
difficulty_not_in_mr[simp]
gaslimit_not_in_mr[simp]
gasprice_not_in_mr[simp]
memory_range_elms_in_minus_mu[simp]
memory_range_elms_update_memory_usage[simp]
memory_range_in_caller[simp]
memory_range_in_sent_value[simp]
memory_range_in_origin[simp]
memory_range_in_pc[simp]
memory_range_in_coinbase[simp]
vset_update_balance[simp]
memory_range_elms_update_balance[simp]
small_min[simp]
sucsuc_minus_two[simp]
advance_pc_inc_but_stack[simp]
minus_one_bigger[simp]
storage_elm_kept_by_gas_update[simp]
storage_elm_kept_by_stack_updaate[simp]
advance_pc_keeps_storage_elm[simp]
rev_drop[simp]
less_than_minus_two[simp]
suc_minus_two[simp]
minus_one_two[simp]
minus_two_or_less[simp]
min_right[simp]
rev_take_nth[simp]
stack_topmost_in_insert_memory_usage[simp]
memory_gane_elms_in_stack_update[simp]
stack_topmost_in_minus_balance_as[simp]
stack_topmost_in_union_balance[simp]
memory_range_in_minus_balance_as[simp]
memory_range_in_union_balance[simp]
memory_range_in_minus_balance[simp]
memory_range_advance[simp]
update_balance_match[simp]
lookup_o[simp]
update_balance_no_change[simp]
update_balance_changed[simp]
rev_append_look_up[simp]
pair_snd_eq[simp]
log_num_memory_usage[simp]
log_num_not_balance[simp]
log_num_balance_update[simp]
log_num_not_stack_topmost[simp]
log_num_not_stack[simp]
contract_action_not_vctx[simp]
continuing_not_vctx[simp]
log_num_not_ext_program[simp]
log_num_elm_means[simp]
log_num_in_v_means[simp]
account_existence_means_v[simp]
account_existence_not_stack[simp]
vctx_gas_changed[simp]
lognum_not_stack_topmost[simp]
stack_topmost_minus_lognum[simp]
vctx_pc_log_advance[simp]
memory_range_elms_in_x_minus_lognum[simp]
memory_range_elms_logs_update[simp]
log0_create_logs[simp]
default_zero[simp]
default_one[simp]
caller_sep[simp]
sep_caller[simp]
sep_caller_sep[simp]
balance_sep[simp]
sep_balance[simp]
sep_balance_sep[simp]
not_continuing_sep[simp]
sep_not_continuing_sep[simp]
this_account_sep[simp]
sep_this_account[simp]
sep_this_account_sep[simp]
action_sep[simp]
sep_action[simp]
sep_action_sep[simp]
sep_stack_topmost[simp]
sep_account_existence_sep[simp]
sep_account_existence[simp]
account_existence_sep[simp]
sep_sep_account_existence_sep[simp]

end
