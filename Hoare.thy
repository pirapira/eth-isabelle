theory Hoare

imports Main "./lem/Evm"

begin

(* Following Magnus Myreen's thesis "Formal verification of machine-code programs" 3.2.4 *)  

datatype state_element =
    StackHeightElm "nat"  (* considering making it int *)
  | StackElm "nat * w256" (* position, value *)
    (* The position is counted from the bottom *)
    (* StackElement (0, 300) says the oldest element on the stack is 300 *)
  | StorageElm "w256 * w256" (* index, value *)
  | MemoryElm "w256 * byte" (* address, value *)
  | LogElm "nat * log_entry" (* position, log *)
    (* Log (0, entry) says that the first recorded log entry is 0 *)
  | PcElm "int" (* program counter *)
  | GasElm "int" (* remaining gas *)
  | MemoryUsageElm "int" (* current memory usage *)
  | CodeElm "int * inst" (* a position containing an instruction *)
  | ThisAccountElm "address" (* The address of this account *)
  | BalanceElm "address * w256" (* address, amount *)
  | BlockInfoElm "block_info" (* the current block.  This might be broken down to more elements. *)
  | CallerElm "address"
  | OriginElm "address"
  | SentValueElm "w256"
  | SentDataLengthElm "nat" (* considering making it int *)
  | SentDataElm "nat * byte" (* position, content.  Considering making position an int *)
  | ExtProgramSizeElm "address * int" (* address, size.  Considering making size an int *)
  | ExtProgramElm "address * nat * byte" (* address, position, byte.  Considering making position an int *)
  | ContractActionElm "contract_action" (* None indicates continued execution *)

definition contract_action_as_set :: "contract_action \<Rightarrow> state_element set"
  where "contract_action_as_set act == { ContractActionElm act }"

definition memory_as_set :: "memory \<Rightarrow> state_element set"
  where
    "memory_as_set m == { MemoryElm (a, v) | a v. m a = v }"

definition storage_as_set :: "storage \<Rightarrow> state_element set"
  where
    "storage_as_set s == { StorageElm (i, v) | i v. s i = v}"

definition balance_as_set :: "(address \<Rightarrow> w256) \<Rightarrow> state_element set"
  where
    "balance_as_set b == { BalanceElm (a, v) | a v. b a = v }"

definition stack_as_set :: "w256 list \<Rightarrow> state_element set"
  where
    "stack_as_set s == { StackHeightElm (length s) } \<union>
                       { StackElm (idx, v) | idx v. idx < length s \<and> (rev s) ! idx = v }"

definition data_sent_as_set :: "byte list \<Rightarrow> state_element set"
  where
    "data_sent_as_set lst == { SentDataLengthElm (length lst) } \<union>
                             { SentDataElm (idx, v) | idx v. lst ! idx = v }"

definition ext_program_as_set :: "(address \<Rightarrow> program) \<Rightarrow> state_element set"
  where
    "ext_program_as_set ext ==
      { ExtProgramSizeElm (adr, s) | adr s. program_length (ext adr) = s } \<union>
      { ExtProgramElm (adr, pos, b) | adr pos b. program_as_natural_map (ext adr) pos = b }
    "

definition log_as_set :: "log_entry list \<Rightarrow> state_element set"
  where
    "log_as_set logs ==
      { LogElm (pos, l) | pos l. logs ! pos = l}
    "

definition program_as_set :: "program \<Rightarrow> state_element set"
  where
    "program_as_set prg ==
      { CodeElm (pos, i) | pos i. program_content prg pos = Some i  } \<union>
      { CodeElm (pos, Misc STOP) | pos. program_content prg pos = None }
    "

definition constant_ctx_as_set :: "constant_ctx \<Rightarrow> state_element set"
  where
    "constant_ctx_as_set c == program_as_set (cctx_program c) \<union> { ThisAccountElm (cctx_this c) }"

definition variable_ctx_as_set :: "variable_ctx \<Rightarrow> state_element set"
  where
    "variable_ctx_as_set v ==
       stack_as_set (vctx_stack v)
    \<union> memory_as_set (vctx_memory v)
    \<union> storage_as_set (vctx_storage v)
    \<union> balance_as_set (vctx_balance v)
    \<union> log_as_set (vctx_logs v)
    \<union> { MemoryUsageElm (vctx_memory_usage v)
      , CallerElm (vctx_caller v)
      , SentValueElm (vctx_value_sent v)
      , OriginElm (vctx_origin v)
      , BlockInfoElm (vctx_block v)
      , GasElm (vctx_gas v)
      , PcElm (vctx_pc v)
      }"

definition contexts_as_set :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> state_element set"
  where
    "contexts_as_set v c ==
       constant_ctx_as_set c \<union> variable_ctx_as_set v"

(* From Magnus Myreen's thesis, Section 3.3 *)
definition sep :: "(state_element set \<Rightarrow> bool) \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "sep p q == (\<lambda> s. \<exists> u v. p u \<and> q v \<and> u \<union> v = s \<and> u \<inter> v = {})"

notation sep (infixr "**" 60)

lemma sep_assoc [simp] : "((p ** q) ** r) s = (p ** q ** r) s"
  apply(auto simp add: sep_def)
  apply(rule_tac x = "ua" in exI; auto)
done

(** equivalence of predicates **)

definition pred_equiv :: "(state_element set \<Rightarrow> bool) \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
"pred_equiv a b = (\<forall> s. a s = b s)"

(** equivalence is reflexivie **)
lemma pred_equiv_refl : "pred_equiv a a"
apply(simp add: pred_equiv_def)
done

(** congruence of equivalence over sep **)
lemma pred_equiv_sep : "pred_equiv a b \<Longrightarrow> pred_equiv c d \<Longrightarrow> pred_equiv (a ** c) (b ** d)"
apply(simp add: pred_equiv_def sep_def)
done

lemma pred_equiv_sep_comm : "pred_equiv (a ** b) (b ** a)"
apply(simp add: pred_equiv_def sep_def)
by blast

lemma pred_equiv_addL [intro]: "pred_equiv b c \<Longrightarrow> pred_equiv (a ** b) (a ** c)"
apply(simp add: pred_equiv_def sep_def)
done



definition emp :: "state_element set \<Rightarrow> bool"
  where
    "emp s == (s = {})"

definition pure :: "bool \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "pure b s == emp s \<and> b"

notation pure ("\<langle> _ \<rangle>")
  
definition stack_height :: "nat \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "stack_height h s == (s = {StackHeightElm h})"

definition stack :: "nat \<Rightarrow> w256 \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "stack pos v s == (s = {StackElm (pos, v)})"

definition program_counter :: "int \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "program_counter pos s == s = {PcElm pos}"

definition gas_pred :: "int \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "gas_pred g s == s = {GasElm g}"

(* memory8, memory, calldata, and storage should be added here *)

lemma stack_sound0 :
  "(stack pos w ** p) s \<Longrightarrow> StackElm (pos, w) \<in> s"
apply(auto simp add: sep_def stack_def)
done

lemma stack_sound1 :
  "StackElm (pos, w) \<in> contexts_as_set var con \<Longrightarrow> rev (vctx_stack var) ! pos = w"
  apply(simp add: contexts_as_set_def variable_ctx_as_set_def constant_ctx_as_set_def
      stack_as_set_def memory_as_set_def
      balance_as_set_def storage_as_set_def log_as_set_def program_as_set_def)
  done

lemma stack_sem :
  "(stack pos w ** p) (contexts_as_set var con) \<Longrightarrow> rev (vctx_stack var) ! pos = w"
  apply(drule stack_sound0)
  apply(drule stack_sound1)
  apply(simp)
  done

definition program_result_as_set :: "constant_ctx \<Rightarrow> program_result \<Rightarrow> state_element set"
  where
    "program_result_as_set c rslt =
        ( case rslt of
          ProgramStepRunOut v \<Rightarrow> contexts_as_set v c
        | ProgramToEnvironment act st bal _ logs _ \<Rightarrow> {} (* for now *)
        | ProgramInvalid \<Rightarrow> {}
        | ProgramAnnotationFailure \<Rightarrow> {} (* need to assume no annotation failure somewhere *)
        | ProgramInit _ \<Rightarrow> {}
        )"

definition code :: "(int * inst) set \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "code f s == s = { CodeElm(pos, i) | pos i. (pos, i) \<in> f }"

(* code and set separation *)
lemma code_diff_union : "pred_equiv (code (a \<union> b)) (code a ** (code (b - a)))"
apply(auto simp add: pred_equiv_def code_def sep_def)
done

definition no_assertion :: "constant_ctx \<Rightarrow> bool"
  where "no_assertion c == (\<forall> pos. program_annotation (cctx_program c) pos = [])"

definition triple ::
 "(state_element set \<Rightarrow> bool) \<Rightarrow> (int * inst) set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "triple pre insts post ==
    \<forall> co_ctx presult rest stopper. no_assertion co_ctx \<longrightarrow>
       (pre ** code insts ** rest) (program_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k. (post ** code insts ** rest) (program_result_as_set co_ctx (program_sem stopper co_ctx k presult)))"

lemma no_assertion_pass [simp] : "no_assertion co_ctx \<Longrightarrow> check_annotations v co_ctx"
apply(simp add: no_assertion_def check_annotations_def)
done
    
lemma pure_sep [simp] : "(\<langle> b \<rangle> ** rest) s = (b \<and> rest s)"
apply(simp add: sep_def pure_def emp_def)
done

lemma stack_height_sep [simp] : "(stack_height h ** rest) s =
  (StackHeightElm h \<in> s \<and> rest (s - {StackHeightElm h})) "
apply(auto simp add: sep_def stack_height_def)
done

lemma stack_sep [simp] : "(stack p w ** rest) s =
  (StackElm (p, w) \<in> s \<and> rest (s - {StackElm (p, w)}))"
apply(auto simp add: sep_def stack_def)
done

lemma program_counter_sep [simp] : "(program_counter w ** rest) s =
  (PcElm w \<in> s \<and> rest (s - {PcElm w}))"
apply(auto simp add: sep_def program_counter_def)
done

lemma code_sep [simp] : "(code pairs ** rest) s =
  ({ CodeElm(pos, i) | pos i. (pos, i) \<in> pairs } \<subseteq> s \<and> (rest (s - { CodeElm(pos, i) | pos i. (pos, i) \<in> pairs })))"
  apply(auto simp add: sep_def code_def)
  apply(simp add: Set.Un_Diff)
  by (simp add: Diff_triv inf_commute)

lemma gas_pred_sep [simp] : "(gas_pred g ** rest) s =
  ( GasElm g \<in> s \<and> rest (s - { GasElm g }) )"
  apply(auto simp add: sep_def gas_pred_def)
done

lemma stackHeightElmEquiv [simp] : "StackHeightElm h \<in> contexts_as_set v c =
  (length (vctx_stack v) = h)
  "
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def)
  done

lemma stackElmEquiv [simp] : "StackElm (pos, w) \<in> contexts_as_set v c =
  (pos < length (vctx_stack v) \<and> rev (vctx_stack v) ! pos = w)"
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def)
done

lemma pcElmEquiv [simp] : "PcElm k \<in> contexts_as_set va_ctx co_ctx =
  (vctx_pc va_ctx = k)"
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def)
done

lemma gasElmEquiv [simp] : "GasElm g \<in> contexts_as_set va_ctx co_ctx =
  (vctx_gas va_ctx = g)"
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def)
done

lemma codeElmEquiv [simp] :
  "CodeElm (pos, i) \<in> contexts_as_set va_ctx co_ctx =
   ((program_content (cctx_program co_ctx) pos = Some i) \<or>
   (program_content (cctx_program co_ctx) pos = None) \<and> i = Misc STOP)"
apply(auto simp add: contexts_as_set_def constant_ctx_as_set_def variable_ctx_as_set_def
      program_as_set_def stack_as_set_def memory_as_set_def storage_as_set_def
      balance_as_set_def log_as_set_def)
done

lemma insert_minus : "a \<noteq> b \<Longrightarrow> insert a s - { b } = insert a (s - {b})"
  apply(simp add: insert_Diff_if)
  done

lemma pred_functional : "p (s :: state_element set) \<Longrightarrow> s = t \<Longrightarrow> p t"
apply(auto)
done

lemma insert_functional : "e = f \<Longrightarrow> s = t \<Longrightarrow> insert e s = insert f t"
  apply(auto)
  done

lemma lookup_over [simp] : "(rev lista @ (aa # l)) ! length lista = aa"
	by (metis length_rev nth_append_length)

lemma lookup_over1 [simp] : "(rev lista @ (w # a # l)) ! Suc (length lista) = a"
(* sledgehammer *)
	by (metis add.left_neutral append.assoc append_Nil2 length_append length_rev list.size(3) list.size(4) nth_append_length plus_nat.simps(2) rev.simps(2) rev_append rev_rev_ident)

lemma short_match [simp] :
  "idx < length lista \<Longrightarrow> (rev lista @ l) ! idx = (rev lista @ m) ! idx"
(* sledgehammer *)
	by (simp add: nth_append)
		
declare memory_as_set_def [simp]
  storage_as_set_def [simp]
  log_as_set_def [simp]
  balance_as_set_def [simp]
  program_result_as_set_def [simp]
  next_state.simps [simp]

 
(**
 ** Hoare Triple for each instruction
 **)
 
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
apply(simp add: program_sem.simps vctx_next_instruction_def instruction_sem_def check_resources_def
      inst_stack_numbers.simps arith_inst_numbers.simps predict_gas_def C_def Cmem_def
      Gmemory_def new_memory_consumption.simps thirdComponentOfC.simps
      vctx_next_instruction_default_def stack_2_1_op_def)
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

(**
 ** Inference rules about Hoare triples
 ** Following Magnus Myreen's thesis, 3.5
 **)



(** Composition **)
lemma pred_equiv_sound : "pred_equiv p0 p1 \<Longrightarrow> p0 s = p1 s"
apply(simp add: pred_equiv_def)
done

lemma pred_equiv_trans : "pred_equiv a b \<Longrightarrow> pred_equiv b c \<Longrightarrow> pred_equiv a c"
apply(simp add: pred_equiv_def)
done

lemma equiv_middle :
"pred_equiv p0 p1 \<Longrightarrow> (p ** p0 ** rest) s = (p ** p1 ** rest) s"
apply(rule pred_equiv_sound)
apply(simp add: pred_equiv_sep pred_equiv_refl)
done

lemma code_middle :
"(p ** code (c_1 \<union> c_2) ** rest) s =
 (p ** (code c_1 ** (code (c_2 - c_1))) ** rest) s"
apply(rule equiv_middle)
by (simp add: code_diff_union)

lemma pred_equiv_sep_assoc:
  "pred_equiv ((a ** b) ** c) (a ** b ** c)"
apply(simp add: pred_equiv_def)
done

lemma shuffle3 :
"(p ** (code c_1 ** code (c_2 - c_1)) ** rest) s =
 (p ** code c_1 ** (code (c_2 - c_1) ** rest)) s"
apply(rule pred_equiv_sound)
apply(rule pred_equiv_sep)
 apply(rule pred_equiv_refl)
apply(rule pred_equiv_sep_assoc)
done

lemma execution_continue [simp]:
  "\<forall> presult. (program_sem co_ctx a (program_sem co_ctx b presult) = program_sem co_ctx (b + a) presult)"
apply(induction b)
 apply(simp add: program_sem.simps)
apply(simp add: program_sem.simps)
done

(* Maybe it's better to organize program_sem as a function from program_result to program_result *)
lemma triple_continue:
"triple q c r \<Longrightarrow>
 no_assertion co_ctx \<Longrightarrow>
 (q ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx k presult)) \<Longrightarrow>
 \<exists> l. (r ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx (k + l) presult))"
apply(simp add: triple_def)
apply(drule_tac x = co_ctx in spec)
apply(simp)
apply(drule_tac x = "program_sem co_ctx k presult" in spec)
apply(drule_tac x = rest in spec)
apply(simp)
done

lemma code_back:
  "(q ** code c_1 ** code (c_2 - c_1) ** rest) s = (q ** code (c_1 \<union> c_2) ** rest) s"
apply(simp add: code_middle shuffle3)
done

lemma code_union_s:
  "(q ** code (c_2 \<union> c_1) ** rest) s \<Longrightarrow> (q ** code (c_1 \<union> c_2) ** rest) s"
(* sledgehammer *)
	by (simp add: sup_commute)

lemma composition : "triple p c_1 q \<Longrightarrow> triple q c_2 r \<Longrightarrow> triple p (c_1 \<union> c_2) r"
apply(auto simp add: triple_def code_middle shuffle3)
apply(drule_tac x = "co_ctx" in spec; simp)
apply(drule_tac x = "presult" in spec)
apply(drule_tac x = co_ctx in spec; simp)
apply(drule_tac x = "code (c_2 - c_1) ** rest" in spec; simp)
apply(erule exE)
apply(drule_tac x = "program_sem co_ctx k presult" in spec; simp)
apply(drule_tac x = "code (c_1 - c_2) ** rest" in spec)
apply(simp add: code_back)
apply(drule code_union_s; simp)
apply(erule exE)
apply(rule_tac x = "k + ka" in exI)
apply(rule code_union_s; simp)
done

(** Frame **)

lemma commute_in_four :
  "(a ** b ** c ** d) s \<Longrightarrow> (a ** c ** b ** d) s"
proof -
 have "pred_equiv (b ** c) (c ** b)" by (simp add: pred_equiv_sep_comm)
 hence "pred_equiv (a ** b ** c) (a ** c ** b)" by(rule  pred_equiv_addL)
 hence "pred_equiv ((a ** b ** c) ** d) ((a ** c ** b) ** d)"
	by (simp add: pred_equiv_refl pred_equiv_sep)
 hence "pred_equiv (a ** ((b ** c) ** d)) ((a ** c ** b) ** d)"
  (* sledgehammer *)
	by (meson pred_equiv_sep_assoc pred_equiv_sep_comm pred_equiv_trans)
 hence "pred_equiv (a ** b ** c ** d) ((a ** c ** b) ** d)"
	using pred_equiv_def pred_equiv_sep_assoc sep_def by auto
 hence "pred_equiv (a ** b ** c ** d) (a ** c ** b ** d)"
	using pred_equiv_def pred_equiv_sep_assoc sep_def by auto
 thus "(a ** b ** c ** d) s \<Longrightarrow> (a ** c ** b ** d) s"
  (* sledgehammer *)
  using pred_equiv_sound by blast
qed


lemma frame : "triple p c q \<Longrightarrow> \<forall> r. triple (p ** r) c (q ** r)"
apply(simp add: triple_def)
apply(rule allI)
apply(rule allI)
apply(rule impI)
apply(drule_tac x = co_ctx in spec)
apply(erule impE)
 apply(simp)
apply(rule allI)
apply(rule allI)
apply(rule impI)
apply(drule_tac x = presult in spec)
apply(drule_tac x = "r ** rest" in spec)
apply(erule impE)
 apply(rule commute_in_four; blast)
apply(erule exE)
using commute_in_four by blast

lemma imp_sepL :
  "(\<forall> s. a s \<longrightarrow> b s) \<Longrightarrow>
   (\<forall> s. (a ** c) s \<longrightarrow> (b ** c) s)"
apply(auto simp add: sep_def)
done




lemma postW : "triple p c q \<Longrightarrow> (\<forall> s. q s \<longrightarrow> r s) \<Longrightarrow> triple p c r"
proof -
 assume "triple p c q" "\<forall> s. q s \<longrightarrow> r s"
 then have "(\<forall> co_ctx presult rest. no_assertion co_ctx \<longrightarrow>
       (p ** code c ** rest) (program_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k. (r ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx k presult))))"
   (is ?longer)
  proof (clarify)
   fix co_ctx presult rest
   assume "triple p c q" "(p ** code c ** rest) (program_result_as_set co_ctx presult)" "no_assertion co_ctx"
   then have "\<exists>k. (q ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx k presult))"
    by (auto simp add: triple_def)
   then show "\<exists>k. (r ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx k presult))"
    (* sledghammer *)
    using \<open>\<forall>s. q s \<longrightarrow> r s\<close> imp_sepL by blast
  qed
 moreover have "triple p c r = ?longer"
  using triple_def by blast
 ultimately show "triple p c r"
  by blast
qed


lemma preS : "triple p c q \<Longrightarrow> (\<forall> s. r s \<longrightarrow> p s) \<Longrightarrow> triple r c q"
proof -
 assume "triple p c q" "\<forall> s. r s \<longrightarrow> p s"
 then have "(\<forall> co_ctx presult rest. no_assertion co_ctx \<longrightarrow>
       (r ** code c ** rest) (program_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k. (q ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx k presult))))" (is ?longer)
  proof(clarify)
   fix co_ctx presult rest
   assume "triple p c q" "no_assertion co_ctx" "\<forall> s. r s \<longrightarrow> p s" "(r ** code c ** rest) (program_result_as_set co_ctx presult)"
   then moreover have "(p ** code c ** rest) (program_result_as_set co_ctx presult)"
     using sep_def by auto
   ultimately show "\<exists>k. (q ** code c ** rest) (program_result_as_set co_ctx (program_sem co_ctx k presult))"
    by(simp add: triple_def)
  qed
 moreover have "triple r c q = ?longer"
  by(simp add: triple_def)
 ultimately show "triple r c q" by blast
qed

(** More rules to come **)

(* Some rules about this if-then-else should be derivable. *)

definition if_then_else :: "int \<Rightarrow> inst list \<Rightarrow> inst list \<Rightarrow> inst list \<Rightarrow> inst list"
where
"if_then_else beginning cond then_case else_case =
 cond
 @ (* beginning + length cond *)
 [Stack (PUSH_N (word_rsplit (word_of_int (beginning + int (length cond) + 8 + int (length else_case)) :: 16 word))), Pc JUMPI] 
 @ (* beginning + length cond + 4 *)
 else_case
 @ (* beginning + length cond + length else_case + 4 *)
 [Stack (PUSH_N (word_rsplit (word_of_int (beginning + int (length cond) + int (length else_case) + 9 + int (length then_case)) :: 16 word))), Pc JUMP]
 @ (* beginning + length cond + length else_case + 8 *)
 [Pc JUMPDEST]
 @ (* beginning + length cond + length else_case + 9 *)
 then_case
 @ (* beginning + length cond + length else_case + 9 + length then_case *)
 [Pc JUMPDEST]
"

(* example of if_then_else *)

(* loop *)

  
(* precondition / post condition pair *)

(* What would be the type of precondition? *)
(* instruction_result \<Rightarrow> bool
 * In the precondition, the program counter is overwritten.
 *)

(* validity of pre, program, post triples.
 * Failures are considered as success.
 *)

end
