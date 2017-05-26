theory Invariants
imports "TrTermination" "PathInvariant"
begin

definition basic_inv :: "global0 \<Rightarrow> bool" where
"basic_inv g = (memu_invariant g \<and> gas_invariant g \<and>
   total_balance (g_orig g) < 2^256 \<and> balance_inv g)"

lemma orig_balance :
  "total_balance (g_orig g) < 2^256 \<Longrightarrow>
   balance_inv g \<Longrightarrow>
   total_balance (g_current g) < 2^256"
  using inv_orig_current by fastforce

type_synonym 'a rel = "'a Relation.rel"

definition tr :: "network \<Rightarrow> global0 rel" where
"tr net = {(a,b) | a b. Continue b = next0 net (Continue a) }"

lemma basic_invariant :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   basic_inv st1 \<Longrightarrow>
   basic_inv st2"
apply (simp add:tr_def)
  by (metis basic_inv_def gas_next memu_next orig_balance tr_balance_continue tr_orig)


(* call stack changes *)

lemma stack_changes :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st1, g_stack st2) \<in> push_pop"
by (auto simp add:next0_def tr_def tlR_def push_pop_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(* account existence *)

lemma exist_return :
  "account_exists (update_return st1 addr2 x32 addr) =
   account_exists (st1 addr)"
by (auto simp add:update_return_def update_world_def)

lemma exist_call :
  "account_exists (update_call st1 addr2 x32 addr) =
   account_exists (st1 addr)"
by (auto simp add:update_call_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma exist_transfer :
  "account_exists (transfer_balance st1 addr2 x32 v addr) =
   account_exists (st1 addr)"
by (auto simp add:update_call_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma exist_update :
  "account_exists (update_world st1 addr2 acc addr) =
   ( if addr2 = addr then account_exists acc
     else account_exists (st1 addr))"
by (auto simp add:update_call_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma exist_nonce :
  "account_exists (update_nonce st1 addr2 addr) =
   account_exists (st1 addr)"
by (auto simp add:update_nonce_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma exist_same :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = g_stack st1 \<Longrightarrow>
   account_exists (g_current st1 addr) =
   account_exists (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def
  exist_return
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(*
lemma tl_wf : "(tl x22 = a # x22) = False"
by (auto simp add:tl_def split:list.splits)
*)

lemma exist_push :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_exists (g_current st2 addr)"
by (auto simp add:tr_def tlR_def next0_def Let_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce 
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma exist_pop :
  "(st1, st2) \<in> tr net \<Longrightarrow>
(*   (g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow> *)
   hd (g_stack st1) = (a,b,c,d)  \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_exists (a addr) \<Longrightarrow>
   account_exists (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def tlR_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce (* weird_weird weird_weird2 *)
  create_account_def
  set_account_code_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


lemma exist_push2 :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = (a,b,c,d) # g_stack st1 \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_exists (a addr)"
by (auto simp add:next0_def Let_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce tr_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma exist_push3 :
   "(st1, st2) \<in> tr net \<Longrightarrow>
       g_stack st2 =
       (a, aa, ab, b) # g_stack st1 \<Longrightarrow>
       account_exists (a addr) \<Longrightarrow>
       account_exists (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce tr_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

fun stack_hint :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> stack_hint" where
"stack_hint (a,b,c,d) = d"

fun stack_state :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> world_state" where
"stack_state (a,b,c,d) = a"

definition states_t :: "global0 \<Rightarrow> world_state * world_state list" where
"states_t g = (g_current g, map stack_state (g_stack g))"

lemma exist_mono :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (states_t st1, states_t st2) \<in> mono_rules
      (\<lambda>st. account_exists (st addr))"
apply (cases "g_stack st1 = g_stack st2")
apply (subgoal_tac "(states_t st1, states_t st2)
    \<in> mono_same (\<lambda>st. account_exists (st addr))")
apply (simp add:mono_rules_def)
apply (clarsimp simp add:mono_same_def states_t_def)
  apply (simp add: exist_same)
apply (cases "(g_stack st1,g_stack st2) \<in> tlR")
apply (subgoal_tac "(states_t st1, states_t st2)
    \<in> mono_pop (\<lambda>st. account_exists (st addr))")
apply (simp add:mono_rules_def)
apply (clarsimp simp add:mono_pop_def states_t_def tlR_def)
  apply (simp add: exist_pop)
apply (cases "(g_stack st2,g_stack st1) \<in> tlR")
apply (subgoal_tac "(states_t st1, states_t st2)
    \<in> mono_push (\<lambda>st. account_exists (st addr))")
apply (simp add:mono_rules_def)
apply (auto simp add:mono_push_def states_t_def tlR_def)
  using exist_push2 apply blast
  using exist_push3 apply blast
using stack_changes [of st1 st2 net]
apply (simp add:push_pop_def tlR_def)
done


lemma can_exit :
  "Finished st2 = next0 net (Continue st1) \<Longrightarrow>
   length (g_stack st1) = 0 \<or>
   length (g_stack st1) = 1 \<and> g_create st1"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma create_const :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_create st1 = g_create st2"
by (auto simp add:next0_def Let_def tr_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


(* code changes *)
lemma code_return :
  "account_code0 (update_return st1 addr2 x32 addr) =
   account_code0 (st1 addr)"
by (auto simp add:update_return_def update_world_def)

lemma code_call :
  "account_code0 (update_call st1 addr2 x32 addr) =
   account_code0 (st1 addr)"
by (auto simp add:update_call_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma code_transfer :
  "account_code0 (transfer_balance st1 addr2 x32 v addr) =
   account_code0 (st1 addr)"
by (auto simp add:update_call_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma code_update :
  "account_code0 (update_world st1 addr2 acc addr) =
   ( if addr2 = addr then account_code0 acc
     else account_code0 (st1 addr))"
by (auto simp add:update_call_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma code_nonce :
  "account_code0 (update_nonce st1 addr2 addr) =
   account_code0 (st1 addr)"
by (auto simp add:update_nonce_def transfer_balance_def
   add_balance_def sub_balance_def Let_def update_world_def)

lemma code_stay :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = g_stack st1 \<Longrightarrow>
   account_code0 (g_current st1 addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def
  code_return
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(* separate cases for fail etc. *)
lemma code_fail :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 = InstructionToEnvironment (ContractFail lst) v1 hint \<Longrightarrow>
   hd (g_stack st1) = (a,b,c,d) \<Longrightarrow>
   account_code0 (a addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def
  code_return
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma code_suicide :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 = InstructionToEnvironment (ContractSuicide lst) v1 hint \<Longrightarrow>
   stack_hint (hd (g_stack st1)) \<noteq> CreateAddress addr \<Longrightarrow>
   account_code0 (g_current st1 addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def
  code_return code_update create_account_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma code_ret :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 = InstructionToEnvironment (ContractReturn lst) v1 hint \<Longrightarrow>
   stack_hint (hd (g_stack st1)) \<noteq> CreateAddress addr \<Longrightarrow>
   account_code0 (g_current st2 addr) =
   account_code0 (g_current st1 addr) \<or>
   account_code0 (g_current st2 addr) =
   account_code0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def tr_def
  code_return code_update create_account_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


(* in the hypotheses, matters a lot if it is a=b or b=a *)
lemma code_push :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_code0 (g_current st1 addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def tlR_def
  code_return code_call code_transfer code_update
  code_nonce
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma push_create_hint :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = abcd # g_stack st1 \<Longrightarrow>
   stack_hint abcd = CreateAddress addr \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   False"
by (auto simp add:next0_def Let_def tr_def
  code_return code_call
  code_transfer code_update 
  code_nonce get_hint_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(* how to apply this with mono invariants? *)

definition create_exist_inv :: "address \<Rightarrow> global0 \<Rightarrow> bool" where
"create_exist_inv addr g =
   (\<forall>el \<in> set (g_stack g).
          account_exists (stack_state el addr) \<longrightarrow>
          stack_hint el \<noteq> CreateAddress addr)"

lemma create_exist_inv_stay :
  "g_stack st2 = g_stack st1 \<Longrightarrow>
   create_exist_inv addr st1 \<Longrightarrow>
   create_exist_inv addr st2"
by (simp add:create_exist_inv_def)

lemma create_exist_inv_pop :
  "(g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow>
   create_exist_inv addr st1 \<Longrightarrow>
   create_exist_inv addr st2"
by (auto simp add:create_exist_inv_def tlR_def)

lemma create_exist_inv_push :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = abcd # g_stack st1 \<Longrightarrow>
   create_exist_inv addr st1 \<Longrightarrow>
   create_exist_inv addr st2"
by (auto simp add:next0_def Let_def tr_def
  code_return code_call create_exist_inv_def
  code_transfer code_update 
  code_nonce get_hint_def exist_nonce
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


(* storage changes *)
(* storage changes are first the same as code changes, but also from
   calls out *)
lemma storage_continue :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> range InstructionContinue \<Longrightarrow>
   account_storage0 (g_current st1 addr) =
   account_storage0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def tr_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(* balance changes *)

end


