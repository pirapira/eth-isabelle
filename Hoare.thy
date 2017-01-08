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
        | ProgramToEnvironment act st bal _ logs None \<Rightarrow>
          constant_ctx_as_set c \<union>
          contract_action_as_set act \<union> storage_as_set st \<union> balance_as_set bal \<union> log_as_set logs
        | ProgramToEnvironment act st bal _ logs (Some (v, _, _)) \<Rightarrow>
          (* I omit the variable_env.  This result initializes some
           * synchronous external communication.  Maybe I have to add some special
           * transformation on the state_element set
           *)
          constant_ctx_as_set c \<union>
          contract_action_as_set act \<union> storage_as_set st \<union> balance_as_set bal \<union> log_as_set logs
        | ProgramInvalid \<Rightarrow> {}
        | ProgramAnnotationFailure \<Rightarrow> {} (* need to assume no annotation failure somewhere *)
        | ProgramInit _ \<Rightarrow> {}
        )"

definition code :: "(int * inst) set \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "code f s == s = { CodeElm(pos, i) | pos i. (pos, i) \<in> f }"

definition no_assertion :: "constant_ctx \<Rightarrow> bool"
  where "no_assertion c == (\<forall> pos. program_annotation (cctx_program c) pos = [])"

definition recent_protocol :: "variable_ctx \<Rightarrow> bool"
  where "recent_protocol v == block_number (vctx_block v) \<ge> 2463000"

definition triple ::
 "(state_element set \<Rightarrow> bool) \<Rightarrow> (int * inst) set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "triple pre insts post ==
    \<forall> va_ctx co_ctx rest. no_assertion co_ctx \<longrightarrow> recent_protocol va_ctx \<longrightarrow>
       (pre ** code insts ** rest) (contexts_as_set va_ctx co_ctx) \<longrightarrow>
       (\<exists> k. (post ** code insts ** rest) (program_result_as_set co_ctx (program_sem va_ctx co_ctx k)))"

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
apply(simp add: program_sem.simps vctx_next_instruction_def instruction_sem_def check_resources_def
      inst_stack_numbers.simps arith_inst_numbers.simps predict_gas_def C_def Cmem_def
      Gmemory_def new_memory_consumption.simps thirdComponentOfC.simps
      vctx_next_instruction_default_def stack_2_1_op_def)
apply(case_tac "vctx_stack va_ctx"; simp)
apply(case_tac list; simp)
apply(auto simp add: subtract_gas.simps strict_if_def program_sem.simps program_result_as_set_def
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
