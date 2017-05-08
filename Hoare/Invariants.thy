theory Invariants
imports "TrTermination"
begin

definition basic_inv :: "global0 \<Rightarrow> bool" where
"basic_inv g = (memu_invariant g \<and> gas_invariant g \<and>
   total_balance (g_orig g) < 2^256 \<and> balance_inv g)"

lemma orig_balance :
  "total_balance (g_orig g) < 2^256 \<Longrightarrow>
   balance_inv g \<Longrightarrow>
   total_balance (g_current g) < 2^256"
  using inv_orig_current by fastforce


lemma basic_invariant :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   basic_inv st1 \<Longrightarrow>
   basic_inv st2"
  by (metis basic_inv_def gas_next memu_next orig_balance tr_balance_continue tr_orig)

definition re_invariant ::
   "global0 \<Rightarrow> address \<Rightarrow> (w256 \<Rightarrow> storage \<Rightarrow> bool) \<Rightarrow> bool" where
"re_invariant g addr iv = (
  iv (account_balance0 (g_current g addr))
     (account_storage0 (g_current g addr)) \<and>
  (\<forall>x y s. iv x s \<longrightarrow> x < y \<longrightarrow> iv y s))"

definition pop_action :: "contract_action \<Rightarrow> bool" where
"pop_action act =
   (act \<in> range ContractFail \<union> range ContractSuicide
            \<union> range ContractReturn)"

definition re_assumption ::
  "network \<Rightarrow> address \<Rightarrow> program \<Rightarrow> (w256 \<Rightarrow> storage \<Rightarrow> bool) \<Rightarrow> bool" where
"re_assumption net addr prog iv =
  (\<forall>g args v1 h1.
      g_vmstate g = InstructionToEnvironment (ContractCall args) v1 h1 \<longrightarrow>
      callarg_recipient args = addr \<longrightarrow>
      account_code0 (g_current g addr) = prog \<longrightarrow>
  (\<exists>k g1 g2 g3 act2 v2 h2.
      Unimplemented = iter_next net (Continue g) k \<or>
      Continue g1 = next0 net (Continue g) \<and>
      Continue g2 = iter_next net (Continue g) k \<and>
      Continue g3 = iter_next net (Continue g) (Suc k) \<and>
      g_vmstate g2 = InstructionToEnvironment act2 v2 h2 \<and>
      pop_action act2 \<and>
      g_stack g2 = g_stack g1 \<and>
      re_invariant g3 addr iv))"

(* call stack changes *)

lemma stack_changes :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = g_stack st1 \<or>
   g_stack st2 = tl (g_stack st1) \<or>
   tl (g_stack st2) = g_stack st1"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(* storage changes *)

(* code changes *)

(* balance changes *)

end


