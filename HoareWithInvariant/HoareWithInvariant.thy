theory HoareWithInvariant

imports Main
 "../lem/Evm"
 "../sep_algebra/EvmSep"
 "../sep_algebra/Sep_Tactics"
 "~~/src/HOL/Eisbach/Eisbach"
begin

lemma not_at_least_one :
  "\<not> 1 \<le> (aa :: 256 word) \<Longrightarrow> aa = 0"
apply(simp add:linorder_class.not_le)
done

lemma unat_suc : "unat (aa :: w256) = Suc n \<Longrightarrow> unat (aa - 1) = n"
apply(case_tac "aa \<ge> 1")
 apply(simp add: uint_minus_simple_alt unat_def)
apply(drule not_at_least_one)
apply(simp)
done


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
  | LogNumElm "nat" (* Number of recorded logs *)
  | PcElm "int" (* program counter *)
  | GasElm "int" (* remaining gas *)
  | MemoryUsageElm "int" (* current memory usage *)
  | CodeElm "int * inst" (* a position containing an instruction *)
  | ThisAccountElm "address" (* The address of this account *)
  | BalanceElm "address * w256" (* address, amount *)
  | CallerElm "address"
  | OriginElm "address"
  | SentValueElm "w256"
  | SentDataLengthElm "nat" (* considering making it int *)
  | SentDataElm "nat * byte" (* position, content.  Considering making position an int *)
  | ExtProgramSizeElm "address * int" (* address, size.  Considering making size an int *)
  | ExtProgramElm "address * nat * byte" (* address, position, byte.  Considering making position an int *)
  | ContractActionElm "contract_action" (* None indicates continued execution *)
  | ContinuingElm "bool" (* True if the execution is still continuing *)
  | BlockhashElm "w256 * w256"
  | BlockNumberElm w256
  | CoinbaseElm "address"
  | TimestampElm "w256"
  | DifficultyElm "w256"
  | GaslimitElm "w256"
  | GaspriceElm "w256"
  | AccountExistenceElm "address * bool"

abbreviation blockhash_as_elm :: "(w256 \<Rightarrow> w256) \<Rightarrow> state_element set"
where "blockhash_as_elm f == { BlockhashElm (n, h) | n h. f n = h}"

abbreviation block_info_as_set :: "block_info \<Rightarrow> state_element set"
where "block_info_as_set b ==
  blockhash_as_elm (block_blockhash b) \<union> { CoinbaseElm (block_coinbase b),
  TimestampElm (block_timestamp b), DifficultyElm (block_difficulty b),
  GaslimitElm (block_gaslimit b), BlockNumberElm (block_number b) }"

definition account_existence_as_set :: "(address \<Rightarrow> bool) \<Rightarrow> state_element set"
where
"account_existence_as_set f ==
  { AccountExistenceElm (a, e) | a e. f a = e }"

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
                             { SentDataElm (idx, v) | idx v. idx < length lst \<and> lst ! idx = v }"

definition ext_program_as_set :: "(address \<Rightarrow> program) \<Rightarrow> state_element set"
  where
    "ext_program_as_set ext ==
      { ExtProgramSizeElm (adr, s) | adr s. program_length (ext adr) = s } \<union>
      { ExtProgramElm (adr, pos, b) | adr pos b. program_as_natural_map (ext adr) pos = b }
    "

definition log_as_set :: "log_entry list \<Rightarrow> state_element set"
  where
    "log_as_set logs ==
      { LogNumElm (length logs) } \<union>
      { LogElm (pos, l) | pos l. (rev logs) ! pos = l \<and> pos < length logs}
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
    \<union> block_info_as_set (vctx_block v)
    \<union> data_sent_as_set (vctx_data_sent v)
    \<union> ext_program_as_set (vctx_ext_program v)
    \<union> account_existence_as_set (vctx_account_existence v)
    \<union> { MemoryUsageElm (vctx_memory_usage v)
      , CallerElm (vctx_caller v)
      , SentValueElm (vctx_value_sent v)
      , OriginElm (vctx_origin v)
      , GaspriceElm (vctx_gasprice v)
      , GasElm (vctx_gas v)
      , PcElm (vctx_pc v)
      , SentDataLengthElm (length (vctx_data_sent v))
      }"

definition contexts_as_set :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> state_element set"
  where
    "contexts_as_set v c ==
       constant_ctx_as_set c \<union> variable_ctx_as_set v"

type_synonym 'a set_pred = "'a set \<Rightarrow> bool"

text \<open>The old sep_commute and sep_assoc are now in sep_conj_ac and
   sep_def should be replaced by the following sep_basic_simps \<close>
  
lemmas sep_basic_simps =  sep_conj_def sep_set_conv

lemma sep_eq_alts [sep_select]:
  "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s \<and> A \<Longrightarrow> (P \<and>* R) s \<and> A"
  "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T = B \<Longrightarrow> (P \<and>* R) = B"
  "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T = D \<Longrightarrow> D = (P \<and>* R)"
  by auto+
    
lemma sep_select_ext[sep_select]:
   "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s = B s \<Longrightarrow> (P \<and>* R) s = B s"
  "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s = D s \<Longrightarrow> D s = (P \<and>* R) s"
  by auto+

lemma sep_conj_first:
  "(A \<and> (P \<and>* R) s) = ((P \<and>* R) s \<and> A)"
  by (simp add: conj_commute)

text \<open>Use the method sep_sep_iff to solve simple sep-logic
  lemmas of the following form:
  @{term "(some_sep_prop n \<and>* R) s = (SomeSepPropConst n \<in> s \<and> R (s - {SomeSepPropConst n}))"}\<close>

lemma ex_conj_commute:
  "(\<exists>v. P v \<and> Q v) = (\<exists>v. Q v \<and> P v) "
  by (simp only: conj_commute)
    
method exI_pick_last_conj =
  --\<open>Group all conjs on the left and then commute to get the
     last conjunction element in first position.\<close>
  (simp (no_asm) only: conj_assoc[symmetric],
   subst ex_conj_commute)?,
  ((rule exI, erule conjI, ((rule conjI[rotated])+; blast))|
   (rule exI, rule exI, erule (1) conjI, ((rule conjI[rotated])+; blast)))

method solve_sep_iff uses simp =
  solves \<open>(rule iffI;  clarsimp simp add: sep_basic_simps simp),
  exI_pick_last_conj\<close>

text \<open>The sep_subst method takes rule of the form "(some_sep_prop \<and>* R) = _"  and
 substitute the LHS with the RHS without having to put some_sep_prop in first pos in
the goal

This method should probably be rewritten in ML with a loop for
performance and to remove the current limitation of maximum 11
nested conjunctions.\<close>

method sep_subst uses simp =
 ((sep_select 1, subst simp) |
  (sep_select 2, subst simp) |
  (sep_select 3, subst simp) |
  (sep_select 4, subst simp) |
  (sep_select 5, subst simp) |
  (sep_select 6, subst simp) |
  (sep_select 7, subst simp) |
  (sep_select 8, subst simp) |
  (sep_select 9, subst simp) |
  (sep_select 10, subst simp))

method sep_simp_aux =
  simp only: sep_conj_first sep_conj_assoc conj_assoc

text \<open>sep_simp_no_asm simplifies a sep logic formula in the conclusion of a goal.
The conclusion can contain normal conjunctions (e.g. @{term "P \<and> (a \<and>* b) s \<and> Q"}),
if so, sep_simp_no_asm will move the element with a sep-conjunction in first
position and apply all the simp rules pass as argument to it.
The simp rules passed as argument must be of the form @{term "(some_sep_prop n \<and>* R) s = (SomeSepPropConst n \<in> s \<and> R (s - {SomeSepPropConst n}))"}
\<close>
method sep_simp_no_asm uses simp =
  ((sep_simp_aux,  (sep_subst simp: simp)?)+)[1] |
  (sep_subst simp: simp, (solves \<open>sep_simp_aux\<close> (* e.g. solves with refl *))?)

text \<open>Same as sep_simp_no_asm but for assumptions. sep_simp_asm can take several
rules to simplify, it rule attempt to apply all of them, multiple times.\<close>

method sep_simp_asm uses simp =
 (simp only: sep_conj_assoc)?,
 ((sep_select_asm 1, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 2, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 3, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 4, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 5, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 6, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 7, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 8, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 9, subst (asm) simp, (erule conjE)+) |
  (sep_select_asm 10, subst (asm) simp, (erule conjE)+))+

method sep_simp uses simp =
  ((sep_simp_asm simp: simp, (sep_simp_no_asm simp: simp)?) |
  (sep_simp_no_asm simp: simp, (sep_simp_asm simp: simp)?))[1]

lemma sep_lc: "(a ** b ** c) = (b ** a ** c)"
 by (simp add: sep_conj_ac)

lemma sep_three : "(c ** a ** b) = (a ** b ** c)"
 by (simp add: sep_conj_ac)

definition emp :: "'a set_pred"
  where
    "emp s == (s = 0)"

lemma emp_sep [simp] :
  "(emp \<and>* r) = r"
  apply(simp add: emp_def  sep_conj_def)
 done

definition pure :: "bool \<Rightarrow> 'a set_pred"
  where
    "pure b s == emp s \<and> b"

notation pure ("\<langle> _ \<rangle>")

definition memory_usage :: "int \<Rightarrow> state_element set \<Rightarrow> bool"
where
"memory_usage u s == (s = {MemoryUsageElm u})"
  
definition stack_height :: "nat \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "stack_height h s == (s = {StackHeightElm h})"

definition stack :: "nat \<Rightarrow> w256 \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "stack pos v s == (s = {StackElm (pos, v)})"

definition program_counter :: "int \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "program_counter pos s == s = {PcElm pos}"

definition log_number :: "nat \<Rightarrow> state_element set \<Rightarrow> bool"
where
"log_number n s == s = {LogNumElm n}"

definition logged :: "nat \<Rightarrow> log_entry \<Rightarrow> state_element set \<Rightarrow> bool"
where
"logged n l s == s = {LogElm (n, l)}"

definition account_existence :: "address \<Rightarrow> bool \<Rightarrow> state_element set \<Rightarrow> bool"
where
"account_existence a b s == s = {AccountExistenceElm (a, b)}"

lemma sep_logged:
  "(a ** logged n l) s =
   (LogElm (n, l) \<in> s \<and> a (s - {LogElm (n, l)}))"
  by (solve_sep_iff simp: logged_def)

definition gas_pred :: "int \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "gas_pred g s == s = {GasElm g}"

definition gas_any :: "state_element set \<Rightarrow> bool"
  where
    "gas_any s == (\<exists> g. s = {GasElm g})"

lemma gas_any_sep :
  "(gas_any ** rest) s =
   (\<exists> g. GasElm g \<in> s \<and> rest (s - {GasElm g}))"
  apply (rule iffI)
   apply (fastforce simp: gas_any_def sep_basic_simps)
  apply (clarsimp simp add: sep_basic_simps gas_any_def)
  apply (rule_tac x="{GasElm g}" in exI)
  apply (exI_pick_last_conj)
 done    

lemma sep_gas_any_sep:
  "(a ** gas_any ** rest) s =
   (\<exists> g. GasElm g \<in> s \<and> (a ** rest) (s - {GasElm g}))"
 by (sep_simp simp: gas_any_sep)

lemma sep_log_number_sep:
  "(log_number n \<and>* R) s =
   (LogNumElm n \<in> s \<and> R (s - {LogNumElm n}))
  "
  by (solve_sep_iff simp: log_number_def)

definition caller :: "address \<Rightarrow> state_element set \<Rightarrow> bool"
where
"caller c s == s = {CallerElm c}"

definition storage :: "w256 \<Rightarrow> w256 \<Rightarrow> state_element set \<Rightarrow> bool"
where
"storage idx w s == s = {StorageElm (idx, w)}"


definition this_account :: "address \<Rightarrow> state_element set \<Rightarrow> bool"
where
"this_account t s == s = {ThisAccountElm t}"

definition balance :: "address \<Rightarrow> w256 \<Rightarrow> state_element set \<Rightarrow> bool"
where
"balance adr v s == s = {BalanceElm (adr, v)}"

definition block_number_pred :: "w256 \<Rightarrow> state_element set \<Rightarrow> bool"
where
"block_number_pred w s == s = {BlockNumberElm w}"

definition continuing :: "state_element set \<Rightarrow> bool"
where
"continuing s == s = { ContinuingElm True }"

definition not_continuing :: "state_element set \<Rightarrow> bool"
where
"not_continuing s == s = {ContinuingElm False}"

definition action :: "contract_action \<Rightarrow> state_element set \<Rightarrow> bool"
where
"action act s == s = {ContractActionElm act}"

(* memory8, memory, calldata, and storage should be added here *)

definition memory8 :: "w256 \<Rightarrow> byte \<Rightarrow> state_element set \<Rightarrow> bool"
where
"memory8 idx v s == s = {MemoryElm (idx ,v)}"

lemma memory8_sep :
 "(memory8 idx v ** rest) s = (MemoryElm (idx, v) \<in> s \<and> rest (s - {MemoryElm (idx, v)}))"
 by (solve_sep_iff simp: memory8_def)

lemma sep_memory8_sep :
"(a ** memory8 idx v ** rest) s = (MemoryElm (idx, v) \<in> s \<and> (a ** rest) (s - {MemoryElm (idx, v)}))"
proof -
  have "(a ** memory8 idx v ** rest) s = (memory8 idx v ** a ** rest) s"
    by (metis sep_conj_assoc sep_conj_commute)
  moreover have "(memory8 idx v ** a ** rest) s = (MemoryElm (idx, v) \<in> s \<and> (a ** rest) (s - {MemoryElm (idx, v)}))"
    by (rule memory8_sep)
  ultimately show ?thesis
    by auto
qed
    
fun memory_range :: "w256 \<Rightarrow> byte list \<Rightarrow> state_element set \<Rightarrow> bool"
where
  "memory_range begin [] = emp"
| "memory_range begin (h # t) = (memory8 begin h ** memory_range (begin + 1) t)"

fun memory_range_elms :: "w256 \<Rightarrow> byte list \<Rightarrow> state_element set"
where
  "memory_range_elms begin [] = {}"
| "memory_range_elms begin (a # lst) = {MemoryElm (begin, a)} \<union> memory_range_elms (begin + 1) lst"

lemma memory_range_elms_nil :
  "x \<notin> memory_range_elms b []"
apply(simp)
done

lemma memory_range_elms_cons :
  "memory_range_elms b (a # lst) = {MemoryElm (b, a)} \<union> memory_range_elms (b + 1) lst"
apply(auto)
done

(* prove a lemma about the above two definitions *)


lemma stack_sound0 :
  "(stack pos w ** p) s \<Longrightarrow> StackElm (pos, w) \<in> s"
by (clarsimp simp add: sep_basic_simps stack_def)

lemmas context_rw = contexts_as_set_def variable_ctx_as_set_def constant_ctx_as_set_def
      stack_as_set_def memory_as_set_def
      balance_as_set_def storage_as_set_def log_as_set_def program_as_set_def data_sent_as_set_def
      ext_program_as_set_def account_existence_as_set_def

lemma stack_sound1 :
  "StackElm (pos, w) \<in> contexts_as_set var con \<Longrightarrow> rev (vctx_stack var) ! pos = w"
  apply(simp add: context_rw)
  done

lemma stack_sem :
  "(stack pos w ** p) (contexts_as_set var con) \<Longrightarrow> rev (vctx_stack var) ! pos = w"
  apply(drule stack_sound0)
  apply(drule stack_sound1)
  apply(simp)
  done

definition instruction_result_as_set :: "constant_ctx \<Rightarrow> instruction_result \<Rightarrow> state_element set"
  where
    "instruction_result_as_set c rslt =
        ( case rslt of
          InstructionContinue v \<Rightarrow> {ContinuingElm True} \<union> contexts_as_set v c
        | InstructionToEnvironment act v _ \<Rightarrow> {ContinuingElm False, ContractActionElm act} \<union> contexts_as_set v c
        )"

definition code :: "(int * inst) set \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "code f s == s = { CodeElm(pos, i) | pos i. (pos, i) \<in> f }"

axiomatization hash2 :: "w256 \<Rightarrow> w256 \<Rightarrow> w256" where
hash_inj :
    "hash2 b v1 = hash2 c v2 \<Longrightarrow> b = c \<or> hash2 b v1 = 0"
and hash_inj2 :
   "hash2 b v1 = hash2 c v2 \<Longrightarrow> v1 = v2  \<or> hash2 b v1 = 0"
and hash_compat :
   "hash2 a b \<noteq> 0 \<Longrightarrow> hash2 a b = keccak (word_rsplit a@ word_rsplit b)"

definition magic_filter :: "8 word list \<Rightarrow> bool" where
"magic_filter lst = (\<forall> a b.
   (lst = word_rsplit a @ word_rsplit b) \<longrightarrow>
   hash2 a b \<noteq> 0)"

definition failed_for_reasons :: "failure_reason set \<Rightarrow> instruction_result \<Rightarrow> bool"
where
"failed_for_reasons allowed r =
 (allowed \<noteq> {} \<and>
 (\<exists> reasons a b.
              r = InstructionToEnvironment (ContractFail reasons) a b
              \<and> set reasons \<subseteq> allowed))"


definition triple ::
 "network \<Rightarrow> failure_reason set \<Rightarrow> (state_element set \<Rightarrow> state_element set \<Rightarrow> bool)
          \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> (int * inst) set \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "triple net allowed_failures reentrancy pre insts post ==
    \<forall> co_ctx presult rest stopper.
       (pre ** code insts ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       (\<exists> k.
         ((post ** code insts ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult)))
         \<or> failed_for_reasons allowed_failures (program_sem stopper co_ctx k net presult))"

lemma pure_sep : "(((\<langle> b \<rangle>) ** rest) s) = (b \<and> rest s)"
  by ( simp add: sep_conj_def pure_def emp_def )

lemma continuing_sep:
  "(continuing ** rest) s = ((ContinuingElm True) \<in> s \<and> rest (s - {ContinuingElm True}))"
   by (solve_sep_iff simp: continuing_def)


lemma sep_continuing_sep:
  "(a ** continuing ** b) s = ((ContinuingElm True) \<in> s \<and> (a ** b) (s - {ContinuingElm True}))"
 by (rule iffI) (sep_simp simp: continuing_sep)+


lemma storage_sep:
  "(storage idx w ** rest) s =
   (StorageElm (idx, w) \<in> s \<and> rest (s - {StorageElm (idx, w)}))"
   by (solve_sep_iff simp: storage_def)

lemma sep_storage:
  "(rest ** storage idx w) s =
   (StorageElm (idx, w) \<in> s \<and> rest (s - {StorageElm (idx, w)}))"
  by (solve_sep_iff simp: storage_def)


lemma stack_height_sep : "(stack_height h ** rest) s =
  (StackHeightElm h \<in> s \<and> rest (s - {StackHeightElm h})) "
  by (solve_sep_iff simp: stack_height_def)

lemma sep_stack_height : "(rest ** stack_height h) s =
  (StackHeightElm h \<in> s \<and> rest (s - {StackHeightElm h})) "
  by (solve_sep_iff simp: stack_height_def)

lemma sep_stack_height_sep: "(a ** stack_height h ** rest) s =
  (StackHeightElm h \<in> s \<and> (a ** rest) (s - {StackHeightElm h})) "
  by (sep_simp simp: stack_height_sep)

lemma stack_sep : "(stack p w ** rest) s =
  (StackElm (p, w) \<in> s \<and> rest (s - {StackElm (p, w)}))"
  by (solve_sep_iff simp: stack_def)

lemma sep_stack : "(rest ** stack p w) s =
  (StackElm (p, w) \<in> s \<and> rest (s - {StackElm (p, w)}))"
  by (solve_sep_iff simp: stack_def)

lemma sep_stack_sep  : "(a ** stack p w ** rest) s =
  (StackElm (p, w) \<in> s \<and> (a ** rest) (s - {StackElm (p, w)}))"
  by (sep_simp simp: stack_sep)


lemma program_counter_sep : "(program_counter w ** rest) s =
  (PcElm w \<in> s \<and> rest (s - {PcElm w}))"
  by (solve_sep_iff simp: program_counter_def)

lemma sep_program_counter : "(rest ** program_counter w) s =
  (PcElm w \<in> s \<and> rest (s - {PcElm w}))"
  by (solve_sep_iff simp: program_counter_def)


lemma sep_program_counter_sep : "(a ** program_counter w ** rest) s =
  (PcElm w \<in> s \<and> (a ** rest) (s - {PcElm w}))"
  by (sep_simp simp: program_counter_sep)

lemma code_sep: "(code pairs ** rest) s =
  ({ CodeElm(pos, i) | pos i. (pos, i) \<in> pairs } \<subseteq> s \<and> (rest (s - { CodeElm(pos, i) | pos i. (pos, i) \<in> pairs })))"
  apply (rule iffI)
    apply (rule conjI)
  apply (clarsimp simp: code_def sep_basic_simps)
   apply (clarsimp simp:  sep_basic_simps)
    apply (erule back_subst[where P=rest])
    apply(fastforce simp add: code_def)
  apply (clarsimp simp: code_def sep_basic_simps)
  apply exI_pick_last_conj
 done

lemma sep_code : "(rest ** code pairs) s =
  ({ CodeElm(pos, i) | pos i. (pos, i) \<in> pairs } \<subseteq> s \<and> (rest (s - { CodeElm(pos, i) | pos i. (pos, i) \<in> pairs })))"
  by (sep_simp simp: code_sep)

lemma sep_code_sep: "(a ** code pairs ** rest) s =
  ({ CodeElm(pos, i) | pos i. (pos, i) \<in> pairs } \<subseteq> s \<and> ((a ** rest) (s - { CodeElm(pos, i) | pos i. (pos, i) \<in> pairs })))"
  by (sep_simp simp: code_sep)

lemma sep_sep_code : "(a ** b ** code pairs) s =
  ({ CodeElm(pos, i) | pos i. (pos, i) \<in> pairs } \<subseteq> s \<and> ((a ** b) (s - { CodeElm(pos, i) | pos i. (pos, i) \<in> pairs })))"
  by (sep_simp simp: code_sep)


lemma gas_pred_sep : "(gas_pred g ** rest) s =
  ( GasElm g \<in> s \<and> rest (s - { GasElm g }) )"
  by (solve_sep_iff simp: gas_pred_def)


lemma sep_gas_pred : "(rest ** gas_pred g) s =
  ( GasElm g \<in> s \<and> rest (s - { GasElm g }) )"
  by (solve_sep_iff simp: gas_pred_def)

lemma sep_gas_pred_sep:
  "(a ** gas_pred g ** b) s =
   ( GasElm g \<in> s \<and> (a ** b) (s - { GasElm g } ) )"
 by (sep_simp simp: gas_pred_sep)


lemma memory_usage_sep: 
  "(memory_usage u ** rest) s =
   (MemoryUsageElm u \<in> s \<and> rest (s - {MemoryUsageElm u}))"
  by (solve_sep_iff simp: memory_usage_def)

lemma sep_memory_usage: 
  "(rest ** memory_usage u) s =
   (MemoryUsageElm u \<in> s \<and> rest (s - {MemoryUsageElm u}))"
 by (solve_sep_iff simp: memory_usage_def)

lemma sep_memory_usage_sep:
  "(a ** memory_usage u ** rest) s =
   (MemoryUsageElm u \<in> s \<and> (a ** rest) (s - {MemoryUsageElm u}))"
	by (sep_simp simp:  memory_usage_sep)


lemma stackHeightElmEquiv: "StackHeightElm h \<in> contexts_as_set v c =
  (length (vctx_stack v) = h)
  "
by (auto simp add:context_rw)

lemma stackElmEquiv: "StackElm (pos, w) \<in> contexts_as_set v c =
  (pos < length (vctx_stack v) \<and> rev (vctx_stack v) ! pos = w)"
by (auto simp add:context_rw)

lemma pcElmEquiv : "PcElm k \<in> contexts_as_set va_ctx co_ctx =
  (vctx_pc va_ctx = k)"
by (auto simp add:context_rw)

lemma gasElmEquiv: "GasElm g \<in> contexts_as_set va_ctx co_ctx =
  (vctx_gas va_ctx = g)"
by (auto simp add:context_rw)

lemma codeElmEquiv:
  "CodeElm (pos, i) \<in> contexts_as_set va_ctx co_ctx =
   ((program_content (cctx_program co_ctx) pos = Some i) \<or>
   (program_content (cctx_program co_ctx) pos = None) \<and> i = Misc STOP)"
by (auto simp add:context_rw)

lemmas stateelm_equiv_simps = 
  stackHeightElmEquiv
  stackElmEquiv
  pcElmEquiv
  gasElmEquiv
  codeElmEquiv

lemma insert_minus : "a \<noteq> b \<Longrightarrow> insert a s - { b } = insert a (s - {b})"
  apply(simp add: insert_Diff_if)
  done

lemma pred_functional : "p (s :: state_element set) \<Longrightarrow> s = t \<Longrightarrow> p t"
apply(auto)
done

lemma insert_functional : "e = f \<Longrightarrow> s = t \<Longrightarrow> insert e s = insert f t"
  apply(auto)
  done

lemma lookup_over[simp] : "(rev lista @ (aa # l)) ! length lista = aa"
	by (metis length_rev nth_append_length)

lemma lookup_over1[simp] : "(rev lista @ (w # a # l)) ! Suc (length lista) = a"
(* sledgehammer *)
	by (metis add.left_neutral append.assoc append_Nil2 length_append length_rev list.size(3) list.size(4) nth_append_length plus_nat.simps(2) rev.simps(2) rev_append rev_rev_ident)

lemma short_match[simp] :
  "idx < length lista \<Longrightarrow> (rev lista @ l) ! idx = (rev lista @ m) ! idx"
(* sledgehammer *)
	by (simp add: nth_append)
		
(**
 ** Inference rules about Hoare triples
 ** Following Magnus Myreen's thesis, 3.5
 **)
lemma code_diff_union : "(code (a \<union> b)) = (code a ** (code (b - a)))"
  by (rule ext) 
     (auto simp: sep_basic_simps code_def)

lemma code_diff_union' : "(code (a \<union> b)) = (code b ** (code (a - b)))"
  by (rule ext) 
     (auto simp: sep_basic_simps code_def)

     
lemma code_middle:
  "(p ** code (c_1 \<union> c_2) ** rest) =
   (p ** (code c_1 ** (code (c_2 - c_1))) ** rest)"
 by (simp add: code_diff_union)

lemma code_middle':
  "(p ** rest ** code (c_1 \<union> c_2)) =
   (p ** rest ** (code c_1 ** (code (c_2 - c_1))))"
 by (simp add: code_diff_union)

lemma shuffle3:
  "(p ** (code c_1 ** code (c_2 - c_1)) ** rest) =
   (p ** code c_1 ** (code (c_2 - c_1) ** rest))"
 by (metis sep_conj_assoc)

lemma execution_continue:
  "(program_sem s co_ctx a net (program_sem s co_ctx b net presult) = program_sem s co_ctx (b + a) net presult)"
apply(induction b arbitrary: presult)
 apply(simp add: program_sem.simps)
apply(simp add: program_sem.simps)
done

(* Maybe it's better to organize program_sem as a function from program_result to program_result *)
lemma triple_continue:
"triple net allowed ind q c r \<Longrightarrow>
 no_assertion co_ctx \<Longrightarrow>
 (q ** code c ** rest) (instruction_result_as_set co_ctx (program_sem s co_ctx k net presult)) \<Longrightarrow>
 \<exists> l. ((r ** code c ** rest) (instruction_result_as_set co_ctx (program_sem s co_ctx (k + l) net presult))
      \<or> failed_for_reasons allowed (program_sem s co_ctx (k + l) net presult))"
apply(simp add: triple_def)
apply(drule_tac x = co_ctx in spec)
apply(drule_tac x = "program_sem s co_ctx k net presult" in spec)
apply(drule_tac x = rest in spec)
apply(simp)
apply(drule_tac x = s in spec)
apply (simp add:  sep_code_sep   execution_continue)
done

lemma code_back:
  "(q ** code c_1 ** code (c_2 - c_1) ** rest) s = (q ** code (c_1 \<union> c_2) ** rest) s"
apply(simp only: code_middle shuffle3)
done

lemma code_more:
  "(rest ** p ** code cL ** code (cR - cL)) s = (rest ** p ** code (cL \<union> cR)) s"
apply(simp add: code_middle')
done

lemma code_union_comm :
 "code (cR \<union> cL) = code (cL \<union> cR)"
  by (simp add: sup_commute)

lemma code_union_s:
  "(q ** code (c_2 \<union> c_1) ** rest) s \<Longrightarrow> (q ** code (c_1 \<union> c_2) ** rest) s"
(* sledgehammer *)
	by (simp add: sup_commute)

lemma composition:
  "c = cL \<union> cR \<Longrightarrow> triple net F ind P cL Q \<Longrightarrow> triple net F ind Q cR R \<Longrightarrow> triple net F ind P c R"
  apply (simp (no_asm) add: triple_def)
  apply clarsimp
  apply (subst (asm) triple_def[where pre=P])
  apply clarsimp
  apply (rename_tac co_ctx presult rest stopper)
  apply(drule_tac x = "co_ctx" in spec)
  apply(drule_tac x = "presult" in spec)
  apply(drule_tac x = "code (cR - cL) ** rest" in spec)
  apply (erule impE)
   apply(subgoal_tac "(instruction_result_as_set co_ctx presult - {CodeElm (pos, i) |pos i. (pos, i) \<in> cL \<or> (pos, i) \<in> cR})
    = (instruction_result_as_set co_ctx presult - {CodeElm (pos, i) |pos i. (pos, i) \<in> cL} -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cR \<and> (pos, i) \<notin> cL})")
    apply (simp add: code_back)
   apply blast
  apply(drule_tac x = stopper in spec)
  apply(erule exE)
  apply (subst (asm) triple_def[where pre=Q])
  apply(drule_tac x = "co_ctx" in spec)
  apply(drule_tac x = "(program_sem stopper co_ctx k net presult)" in spec)
  apply(drule_tac x = "code (cL - cR) ** rest" in spec)
  apply(erule disjE)
   apply(drule_tac x = stopper in spec)
   apply (erule impE)
    apply(subgoal_tac "(instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult) -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cL} -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cR \<and> (pos, i) \<notin> cL}) =
         (instruction_result_as_set co_ctx (program_sem stopper co_ctx k net presult) -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cR} -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cL \<and> (pos, i) \<notin> cR})")
     apply (metis code_diff_union code_union_comm sep_three)
    apply blast
   apply(erule exE)
   apply(rename_tac k l)
   apply(rule_tac x = "k + l" in exI)
   apply(erule disjE)
   apply(rule disjI1)
   apply(subgoal_tac "
   (instruction_result_as_set co_ctx (program_sem stopper co_ctx (k + l) net presult) -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cR} -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cL \<and> (pos, i) \<notin> cR}) =
   (instruction_result_as_set co_ctx (program_sem stopper co_ctx (k + l) net presult) -
         {CodeElm (pos, i) |pos i. (pos, i) \<in> cL \<or> (pos, i) \<in> cR})")
    apply (simp add: code_back code_union_s execution_continue)
   apply blast
  apply auto
 using execution_continue by auto


(** Frame **)

lemma frame:
 "triple net F ind P c Q \<Longrightarrow> triple net F ind (P ** R) c (Q ** R)"
  apply (simp add: triple_def)
  apply clarsimp
  subgoal for co_ctx presult rest stopper
  apply (drule spec[where x=co_ctx])
  apply (drule spec2[where x=presult and y="R ** rest"])
  apply (simp del: sep_conj_assoc add: sep_conj_ac)
  done
 done


lemma imp_sepL:
  "(\<forall>s. a s \<longrightarrow> b s) \<Longrightarrow>
   (\<forall>s. (a ** c) s \<longrightarrow> (b ** c) s)"
  by (auto simp add: sep_basic_simps)

lemma weaken_post:
  "triple net F ind P c Q \<Longrightarrow> (\<forall>s. Q s \<longrightarrow> R s) \<Longrightarrow> triple net F ind P c R"
  apply (simp add: triple_def)
  apply clarsimp
  subgoal for co_ctx presult rest stopper
  apply (drule spec[where x=co_ctx])
  apply (drule spec2[where x=presult and y=rest])
  apply clarsimp
  apply (drule spec[where x=stopper])
  apply clarsimp
  apply (drule imp_sepL[where c="code c ** rest"])
  apply (rule_tac x=k in exI)
  apply (fastforce)
  done
 done

lemma strengthen_pre:
  assumes  "triple net F ind P c Q"
  and      "(\<forall>s. R s \<longrightarrow> P s)"
  shows" triple net F ind R c Q"
  using assms(1)
  apply (simp add: triple_def)
  apply(clarify)
  apply(drule_tac x = co_ctx in spec)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply (erule impE)
   apply (sep_drule assms(2)[rule_format])
   apply assumption
  apply simp
 done

lemma frame_backward:
  "triple net F ind P c Q \<Longrightarrow> P' = (P ** R) \<Longrightarrow> Q' = (Q ** R) \<Longrightarrow>
   triple net F ind P' c Q'"
  by (simp add: frame)

lemma remove_true:
 "(p ** \<langle>True\<rangle> ** rest) = (p ** rest)"
 by (simp add: pure_def sep_conj_def emp_def)
    
lemma true_sep [simp] :
  "(p ** \<langle>True\<rangle>) = p"
 by (simp add: pure_def sep_conj_def emp_def)

lemma sep_true [simp] :
  "(\<langle>True\<rangle> ** p) = p"
 by (simp add: pure_def sep_conj_def emp_def)

lemma move_pure0 :
  "triple net reasons ind (p ** \<langle> True \<rangle>) c q \<Longrightarrow>  triple net reasons ind p c q"
apply(simp add: triple_def remove_true)
done

lemma false_triple :
  "triple net reasons ind (p ** \<langle> False \<rangle>) c q"
apply(simp add: triple_def sep_basic_simps pure_def)
done

lemma get_pure:
  "((p ** \<langle> b \<rangle> ** rest) s) = (b \<and> (p ** rest) s)"
apply(auto simp add: sep_basic_simps pure_def emp_def)
done

lemma move_pure: "triple net reaons ind (p ** \<langle> b \<rangle>) c q = (b \<longrightarrow> triple net reaons ind p c q)"
apply(auto simp add: move_pure0 false_triple)
apply(case_tac b; auto simp: false_triple)
  done

lemma pure_sepD:
  "(\<langle>P\<rangle> ** R) s \<Longrightarrow> R s"
  by (simp add: pure_def emp_def sep_basic_simps)
    
lemma move_pureL: "triple net reaons ind (\<langle> b \<rangle> ** p) c q = (b \<longrightarrow> triple net reaons ind p c q)"
 by (metis move_pure sep_conj_commute)

lemma tmp01:
    "(rest ** code c ** p x) (case presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {}) \<Longrightarrow>
    (rest ** code c ** (\<lambda>s. \<exists>x. p x s)) (case presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {})"
  apply (sep_cancel)+
  apply blast
  done

lemma tmp0:
       "\<forall>co_ctx. no_assertion co_ctx \<longrightarrow>
                (\<forall>presult rest.
                    ((\<lambda>s. \<exists>x. p x s) ** code c ** rest) (case presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {}) \<longrightarrow>
                    (\<forall>stopper. \<exists>k. (q ** code c ** rest) (case program_sem stopper co_ctx k net presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {}))) \<Longrightarrow>
       no_assertion co_ctx \<Longrightarrow>
       (p x ** code c ** rest) (case presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {}) \<Longrightarrow>
       \<exists>k. (q ** code c ** rest) (case program_sem stopper co_ctx k net presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {})"
apply(drule_tac x = co_ctx in spec)
apply(simp)
apply(drule_tac x = presult in spec)
apply(drule_tac x = rest in spec)
apply(subgoal_tac "(rest ** code c ** (\<lambda>s. \<exists>x. p x s))
     (case presult of InstructionContinue v \<Rightarrow> contexts_as_set v co_ctx | _ \<Rightarrow> {})")
    (*
apply(rule tmp01)
apply(simp)
done*)
    oops


lemma preE0:
  "((\<lambda>s. \<exists>x. p x s) ** code c ** rest) s \<Longrightarrow>
   \<exists> x. (p x ** code c ** rest) s"
apply(auto simp only: sep_basic_simps)
	by blast

lemma sep_impL :
 "\<forall> s. b s \<longrightarrow> a s \<Longrightarrow> 
 (c ** b ** d) s \<longrightarrow>
 (c ** a ** d) s"
  by (metis sep_basic_simps)


lemma pre_imp:
 assumes "\<forall> s. (b s \<longrightarrow> a s)"
 and " triple net reasons ind a c q"
shows" triple net reasons ind b c q"
using assms(2)
  apply(auto simp add: triple_def)
  apply(drule_tac x = co_ctx in spec)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply (erule impE)
   apply (sep_drule  assms(1)[rule_format])
   apply blast
  apply(subgoal_tac "(rest ** a ** code c) (instruction_result_as_set co_ctx presult)")
   apply(simp )
  apply (sep_rule sep_impL[OF assms(1), rule_format])
  apply(simp add: code_sep sep_code_sep)
 done

lemma preE1:
"((\<lambda>s. \<exists>x. p x s) ** rest) u
=
(\<exists> x. (p x ** rest) u)
"
apply(auto simp add: sep_basic_simps)
done

lemma preE00:
  "(rest ** code c ** p x) s \<Longrightarrow>
   (rest ** code c ** (\<lambda>s. \<exists>x. p x s)) s"
  apply (sep_cancel)+
  apply blast
 done

lemma preE : "triple net reasons ind (\<lambda> s. \<exists> x. p x s) c q = (\<forall> x. triple net reasons ind (p x) c q)"
apply(auto simp add: triple_def preE1)
 apply(erule_tac x = co_ctx in allE)
 apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply (erule impE)
   apply blast
 apply(subgoal_tac "(rest ** code c ** (\<lambda>s. \<exists>x. p x s)) (instruction_result_as_set co_ctx presult)")
   apply(simp)
  apply(rule_tac x=x in preE00)
  apply(simp)
  apply (sep_simp simp: code_sep )
  apply (simp add: sep_conj_commute)
done


(** More rules to come **)

lemma triple_tauto: "triple net failures ind q e q"
apply(simp add: triple_def; auto)
apply(rule_tac x = 0 in exI)
apply(simp add: program_sem.simps)
done


lemma code_extension0: "triple net failures ind p c_1 q \<Longrightarrow> triple net failures ind q c_2 q \<Longrightarrow>
                        triple net failures ind p (c_1 \<union> c_2) q"
apply(rule_tac cL = c_1 and cR = c_2 in composition; auto)
done

lemma code_extension : "triple net failures ind p c q \<Longrightarrow> triple net failures ind p (c \<union> e) q"
	by (simp add: composition triple_tauto)

lemma code_extension_backward :
  "triple net failures ind p c' q \<Longrightarrow> c' \<subseteq> c \<Longrightarrow> triple net failures ind p c q" 
proof -
 assume "triple net failures ind p c' q"
 then have "triple net failures ind p (c' \<union> c) q"
  using code_extension by blast
 moreover assume "c' \<subseteq> c"
 then have "c = c' \<union> c"
  by (auto)
 ultimately show "triple net failures ind p c q"
  by auto
qed



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

bundle hoare_bundle = 
sep_logged[simp]
gas_any_sep[simp]
sep_gas_any_sep[simp]
sep_log_number_sep[simp]
memory8_sep[simp]
pure_sep[simp]
continuing_sep[simp]
sep_continuing_sep[simp]
storage_sep[simp]
sep_storage[simp]
stack_height_sep[simp]
sep_stack_height[simp]
sep_stack_height_sep[simp]
stack_sep[simp]
sep_stack[simp]
sep_stack_sep[simp]
program_counter_sep[simp]
sep_program_counter[simp]
sep_program_counter_sep[simp]
code_sep[simp]
sep_code[simp]
sep_code_sep[simp]
sep_sep_code[simp]
gas_pred_sep[simp]
sep_gas_pred[simp]
sep_gas_pred_sep[simp]
memory_usage_sep[simp]
sep_memory_usage[simp]
sep_memory_usage_sep[simp]
stackHeightElmEquiv[simp]
stackElmEquiv[simp]
pcElmEquiv[simp]
gasElmEquiv[simp]
codeElmEquiv[simp]
lookup_over[simp]
lookup_over1[simp]
short_match[simp]
memory_as_set_def[simp]
storage_as_set_def[simp]
log_as_set_def[simp]
balance_as_set_def[simp]
next_state_def[simp]
execution_continue[simp]
sep_true[simp]
false_triple[simp]
get_pure[simp]
move_pure[simp]
move_pureL[simp]
sep_code_sep[simp]
preE1[simp]
sep_code_sep[simp]
sep_sep_code[simp]
  

end
