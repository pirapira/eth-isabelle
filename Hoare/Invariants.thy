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

fun stack_cctx :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> constant_ctx" where
"stack_cctx (a,b,c,d) = c"

fun stack_vctx :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> variable_ctx" where
"stack_vctx (a,b,c,d) = b"


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

lemma code_push2 :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = (a,b,c,d) # g_stack st1 \<Longrightarrow>
   account_code0 (g_current st1 addr) = account_code0 (a addr)"
by (auto simp add:next0_def Let_def tr_def tlR_def
  code_return code_call code_transfer code_update
  code_nonce
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma code_push3 :
   "(st1, st2) \<in> tr net \<Longrightarrow>
    g_stack st2 =
    (a, aa, ab, b) # g_stack st1 \<Longrightarrow>
    account_exists (g_current st1 addr) \<Longrightarrow>
    account_code0 (a addr) = account_code0 (g_current st2 addr)"
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

lemma create_exist_inv :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   create_exist_inv addr st1 \<Longrightarrow>
   create_exist_inv addr st2"
by (auto simp add:next0_def Let_def tr_def
  code_return code_call create_exist_inv_def
  code_transfer code_update 
  code_nonce get_hint_def exist_nonce
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma pop_alt :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow>
   g_vmstate st1 \<in>
    {InstructionToEnvironment (ContractReturn a) v h|
     a v h. True} \<union>
    {InstructionToEnvironment (ContractFail a) v h|
     a v h. True} \<union>
    {InstructionToEnvironment (ContractSuicide a) v h|
     a v h. True}"
by (auto simp add:next0_def Let_def tr_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma check_hint :
 "create_exist_inv addr st1 \<Longrightarrow>
  (g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow>
  account_exists
     (stack_state (hd (g_stack st1)) addr) \<Longrightarrow>
  stack_hint (hd (g_stack st1)) \<noteq> CreateAddress addr"
by (cases "g_stack st1"; auto simp add:tlR_def create_exist_inv_def)

lemma code_pop :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow>
   account_code0 (g_current st1 addr) = cd \<Longrightarrow>
   account_code0 (stack_state (hd (g_stack st1)) addr) = cd \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   create_exist_inv addr st1 \<Longrightarrow>
   account_exists (stack_state (hd (g_stack st1)) addr) \<Longrightarrow>
   account_code0 (g_current st2 addr) = cd"
using pop_alt [of st1 st2 net]
apply auto
subgoal for a v h
using code_ret [of st1 st2 net a v h addr]
   check_hint [of addr st1 st2]
apply force
done
using code_fail [of st1 st2 net]
  apply (metis stack_state.elims)
subgoal for a v h
using code_suicide [of st1 st2 net a v h addr]
   check_hint [of addr st1 st2]
apply force
done
done

definition code_inv :: "address \<Rightarrow> program \<Rightarrow> world_state \<Rightarrow> bool" where
"code_inv addr cd st = (
  account_exists (st addr) \<and> account_code0 (st addr) = cd)"

lemma monoI_head :
   "monoI iv st \<Longrightarrow>
    snd st = a#rest \<Longrightarrow>
    iv a \<Longrightarrow>
    iv (fst st)" 
by (auto simp add:monoI_def)

lemma exist_push4 :
   "(st1, st2) \<in> tr net \<Longrightarrow>
       g_stack st2 =
       (a, aa, ab, b) # g_stack st1 \<Longrightarrow>
       account_exists (a addr) \<Longrightarrow>
       account_exists (g_current st1 addr)"
by (auto simp add:next0_def Let_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce tr_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


lemma code_mono :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   create_exist_inv addr st1 \<Longrightarrow>
   (states_t st1, states_t st2) \<in> mono_rules (code_inv addr cd)"
apply (cases "g_stack st1 = g_stack st2")
apply (subgoal_tac "(states_t st1, states_t st2)
    \<in> mono_same (code_inv addr cd)")
apply (simp add:mono_rules_def)
apply (clarsimp simp add:mono_same_def states_t_def)
  apply (simp add: exist_same code_inv_def mono_pop_def
      code_stay)

apply (cases "(g_stack st1,g_stack st2) \<in> tlR")
apply (subgoal_tac "(states_t st1, states_t st2)
    \<in> mono_pop (code_inv addr cd)")
apply (simp add:mono_rules_def)
apply (clarsimp simp add:mono_pop_def states_t_def tlR_def)
  apply (auto simp add: exist_pop code_inv_def)
using code_pop [of st1 st2 net addr cd]
apply (simp add:tlR_def)

apply (cases "(g_stack st2,g_stack st1) \<in> tlR")
apply (subgoal_tac "(states_t st1, states_t st2)
    \<in> mono_push (code_inv addr cd)")
apply (simp add:mono_rules_def)
apply (auto simp add:mono_push_def states_t_def tlR_def
      code_inv_def)
  using exist_push2 apply blast
  apply (simp add: code_push2)

  
  using exist_push3 apply blast
subgoal for a b c d
using code_push3 [of st1 st2 net a b c d addr]
  exist_push4 [of st1 st2 net a b c d addr]
apply force
done

using stack_changes [of st1 st2 net]
apply (simp add:push_pop_def tlR_def)
done

definition cctx :: "global0 \<Rightarrow> constant_ctx list" where
"cctx g = g_cctx g # map stack_cctx (g_stack g)"

lemma cctx_changes :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (cctx st1, cctx st2) \<in> push_pop"
by (auto simp add:next0_def tr_def tlR_def cctx_def
    push_pop_def Let_def
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

lemma storage_pop :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (g_current st1 addr) \<or>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def
  create_account_def set_account_code_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


lemma storage_push :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma storage_push2 :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   account_storage0 (stack_state (hd (g_stack st2)) addr) = 
   account_storage0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma storage_failed_call :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = g_stack st1 \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


(* balance changes *)

lemma state_continue :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> range InstructionContinue \<Longrightarrow>
   g_current st1 = g_current st2"
by (auto simp add:next0_def Let_def tr_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma balance_failed_call :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st2 = g_stack st1 \<Longrightarrow>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma balance_push2 :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   account_balance0 (stack_state (hd (g_stack st2)) addr) = 
   account_balance0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition return_state :: "instruction_result set" where
"return_state = {InstructionToEnvironment (ContractReturn a) v h|
     a v h. True}"

lemma balance_ret :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> return_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (g_current st1 addr) \<or>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def return_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition fail_state :: "instruction_result set" where
"fail_state = {InstructionToEnvironment (ContractFail a) v h|
     a v h. True}"

lemma balance_fail :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> fail_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def
  update_call_def fail_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition suicide_state :: "instruction_result set" where
"suicide_state = {InstructionToEnvironment (ContractSuicide a) v h|
     a v h. True}"

lemma balance_add_aux :
 "total_balance bal < 2^256 \<Longrightarrow>
  a \<noteq> b \<Longrightarrow>
  account_balance0 (bal a) \<le>
  account_balance0 (bal a) + account_balance0 (bal b)"
  by (metis order_refl overflow)

lemma balance_add :
 "balance_inv st \<Longrightarrow>
  total_balance (g_orig st) < 2^256 \<Longrightarrow>
  sender \<noteq> recv \<Longrightarrow>
  account_balance0 (g_current st recv) \<le>
  account_balance0 (g_current st recv) +
  account_balance0 (g_current st sender)"
  using orig_balance  balance_add_aux by fastforce

lemma balance_suicide :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   balance_inv st1 \<Longrightarrow>
   total_balance (g_orig st1) < 2^256 \<Longrightarrow>
   g_vmstate st1 \<in> suicide_state \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_balance0 (g_current st2 addr) \<ge>
   account_balance0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def
  sub_balance_def balance_add
  update_call_def suicide_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition create_state :: "instruction_result set" where
"create_state = {InstructionToEnvironment (ContractCreate a) v h|
     a v h. True}"

lemma balance_create :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> create_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def sub_balance_def
  update_call_def create_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition call_state :: "instruction_result set" where
"call_state = {InstructionToEnvironment (ContractCall a) v h|
     a v h. True} \<union>
{InstructionToEnvironment (ContractDelegateCall a) v h|
     a v h. True}"

lemma balance_add2 :
 "balance_inv st \<Longrightarrow>
  total_balance (g_orig st) < 2^256 \<Longrightarrow>
  sender \<noteq> recv \<Longrightarrow>
  x \<le> account_balance0 (g_current st sender) \<Longrightarrow>
  account_balance0 (g_current st recv) \<le>
  account_balance0 (g_current st recv) + x"
  using orig_balance overflow by blast

lemma balance_call :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   balance_inv st1 \<Longrightarrow>
   total_balance (g_orig st1) < 2^256 \<Longrightarrow>
   g_vmstate st1 \<in> call_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_balance0 (g_current st2 addr) \<ge>
   account_balance0 (g_current st1 addr)"
apply (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def sub_balance_def
  update_call_def call_state_def
  create_account_def set_account_code_def tlR_def
  balance_add2
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)
(* *)
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
using balance_add2 [of st1 "cctx_this (g_cctx st1)" addr]
apply fastforce
done

lemma balance_storage_ret :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> return_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (g_current st1 addr) \<and>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (g_current st1 addr) \<or>
   account_balance0 (g_current st2 addr) = 
   account_balance0 (stack_state (hd (g_stack st1)) addr) \<and>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def sub_balance_def
  update_call_def return_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma storage_fail :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> fail_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def sub_balance_def
  update_call_def fail_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma storage_suicide :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_vmstate st1 \<in> suicide_state \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   account_storage0 (g_current st2 addr) = 
   account_storage0 (g_current st1 addr)"
by (auto simp add:next0_def Let_def tr_def
  update_return_def update_world_def
  transfer_balance_def update_nonce_def
  add_balance_def sub_balance_def
  update_call_def suicide_state_def
  create_account_def set_account_code_def tlR_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition good_inv :: "(account \<Rightarrow> bool) \<Rightarrow> bool" where
"good_inv iv = (\<forall>a b.
   account_storage0 a = account_storage0 b \<longrightarrow>
   account_balance0 a \<le> account_balance0 b \<longrightarrow>
   iv a \<longrightarrow> iv b)"

lemma pop_alt2 :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow>
   g_vmstate st1 \<in> return_state \<union> fail_state \<union> suicide_state"
unfolding return_state_def fail_state_def
  suicide_state_def
using pop_alt by simp

lemma good_iv_helper :
  "good_inv iv \<Longrightarrow>
   account_balance0 a2 =  account_balance0 a1 \<and>
   account_storage0 a2 = account_storage0 a1 \<or>
   account_balance0 a2 = account_balance0 a0 \<and>
   account_storage0 a2 = account_storage0 a0 \<Longrightarrow>
   iv a1 \<Longrightarrow>
   iv a0 \<Longrightarrow>
   iv a2"
unfolding good_inv_def
  by (metis order_refl)

lemma iv_pop :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st1, g_stack st2) \<in> tlR \<Longrightarrow>
   balance_inv st1 \<Longrightarrow>
   total_balance (g_orig st1) < 2 ^ 256 \<Longrightarrow>
   good_inv iv \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   iv (g_current st1 addr) \<Longrightarrow>
   iv (stack_state (hd (g_stack st1)) addr) \<Longrightarrow>
   iv (g_current st2 addr)"
using pop_alt2 [of st1 st2 net]
apply auto
  using balance_storage_ret good_iv_helper apply blast
apply (auto simp add:good_inv_def)
  apply (metis (no_types, hide_lams) balance_fail order_refl storage_fail)
using storage_suicide [of st1 st2 net addr]
apply simp
using balance_suicide [of st1 st2 net addr]
apply simp
done

lemma push_alt :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   g_vmstate st1 \<in> call_state \<union> create_state"
by (auto simp add:next0_def Let_def tr_def tlR_def
  create_state_def call_state_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma iv_same :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   g_stack st1 = g_stack st2 \<Longrightarrow>
   good_inv iv \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   iv (g_current st1 addr) \<Longrightarrow>
   iv (g_current st2 addr)"
unfolding good_inv_def
by (metis balance_failed_call good_inv_def good_iv_helper storage_failed_call)


lemma iv_push2 :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   good_inv iv \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   iv (g_current st1 addr) \<Longrightarrow>
   iv (stack_state (hd (g_stack st2)) addr)"
  by (simp add: good_inv_def balance_push2 storage_push2)

lemma iv_push :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   (g_stack st2, g_stack st1) \<in> tlR \<Longrightarrow>
   balance_inv st1 \<Longrightarrow>
   total_balance (g_orig st1) < 2 ^ 256 \<Longrightarrow>
   good_inv iv \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   iv (g_current st1 addr) \<Longrightarrow>
   iv (g_current st2 addr)"
using push_alt [of st1 st2 net]
apply auto
using storage_push [of st1 st2 net addr]
using balance_call [of st1 st2 net addr]
apply (simp add:good_inv_def)
using storage_push [of st1 st2 net addr]
using balance_create [of st1 st2 net addr]
  using good_iv_helper by blast

lemma iv_mono :
  "(st1, st2) \<in> tr net \<Longrightarrow>
   balance_inv st1 \<Longrightarrow>
   total_balance (g_orig st1) < 2 ^ 256 \<Longrightarrow>
   good_inv iv \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   cctx_this (g_cctx st1) \<noteq> addr \<Longrightarrow>
   \<forall>s1 \<in> set (states st1). iv (s1 addr) \<Longrightarrow>
   s2 \<in> set (states st2) \<Longrightarrow>
   iv (s2 addr)"
using stack_changes [of st1 st2 net]
apply (auto simp add:push_pop_def states_def tlR_def)
  using iv_same apply blast
subgoal
using iv_pop [of st1 st2 net iv addr]
apply (auto simp add:tlR_def)
done
subgoal
using iv_push [of st1 st2 net iv addr]
apply (auto simp add:tlR_def)
done
using iv_push2 [of st1 st2 net iv addr]
apply (auto simp add:tlR_def)
done

end


