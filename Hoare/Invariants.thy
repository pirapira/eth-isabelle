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
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = g_stack st1 \<Longrightarrow>
   account_exists (g_current st1 addr) =
   account_exists (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  exist_return
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma tl_wf : "(tl x22 = a # x22) = False"
by (auto simp add:tl_def split:list.splits)

lemma exist_push :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   tl (g_stack st2) = g_stack st1 \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_exists (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce tl_wf
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma exist_pop :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = (a,b,c,d) # g_stack st1 \<Longrightarrow>
   account_exists (a addr) \<Longrightarrow>
   account_exists (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  exist_return exist_call exist_transfer
  exist_update exist_nonce
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma can_exit :
  "Finished st2 = next0 net (Continue st1) \<Longrightarrow>
   length (g_stack st1) = 0 \<or>
   length (g_stack st1) = 1 \<and> g_create st1"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma create_const :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_create st1 = g_create st2"
by (auto simp add:next0_def Let_def
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
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = g_stack st1 \<Longrightarrow>
   account_code0 (g_current st1 addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  code_return
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma weird : 
   "g_current st2 = a \<Longrightarrow>
    account_code0 (a addr) = account_code0 (g_current st2 addr)"
by auto

lemma weird2 :
 "st2 = st1
    \<lparr>g_stack := d, g_current := a,
       g_cctx := c,
       g_vmstate := e \<rparr> \<Longrightarrow>
  g_current st2 = a"
by auto

(* separate cases for fail etc. *)
lemma code_fail :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_vmstate st1 = InstructionToEnvironment (ContractFail lst) v1 hint \<Longrightarrow>
   (a,b,c,d) # g_stack st2 = g_stack st1 \<Longrightarrow>
   account_code0 (a addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  code_return
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

fun stack_hint :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> stack_hint" where
"stack_hint (a,b,c,d) = d"

fun stack_state :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> world_state" where
"stack_state (a,b,c,d) = a"

lemma code_suicide :
  "next0 net (Continue st1) = Continue st2 \<Longrightarrow>
   g_vmstate st1 = InstructionToEnvironment (ContractSuicide lst) v1 hint \<Longrightarrow>
   stack_hint (hd (g_stack st1)) \<noteq> CreateAddress addr \<Longrightarrow>
   account_code0 (g_current st1 addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  code_return code_update create_account_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma code_ret :
  "next0 net (Continue st1) = Continue st2 \<Longrightarrow>
   g_vmstate st1 = InstructionToEnvironment (ContractReturn lst) v1 hint \<Longrightarrow>
   stack_hint (hd (g_stack st1)) \<noteq> CreateAddress addr \<Longrightarrow>
   account_code0 (g_current st2 addr) =
   account_code0 (g_current st1 addr) \<or>
   account_code0 (g_current st2 addr) =
   account_code0 (stack_state (hd (g_stack st1)) addr)"
by (auto simp add:next0_def Let_def
  code_return code_update create_account_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)


(* in the hypotheses, matters a lot if it is a=b or b=a *)
lemma code_push :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   tl (g_stack st2) = g_stack st1 \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   account_code0 (g_current st1 addr) =
   account_code0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  code_return code_call code_transfer code_update tl_wf
  code_nonce
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma push_create_hint :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = abcd # g_stack st1 \<Longrightarrow>
   stack_hint abcd = CreateAddress addr \<Longrightarrow>
   account_exists (g_current st1 addr) \<Longrightarrow>
   False"
by (auto simp add:next0_def Let_def
  code_return code_call
  code_transfer code_update tl_wf
  code_nonce get_hint_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

definition first_return :: "network \<Rightarrow> global0 \<Rightarrow> nat \<Rightarrow> bool" where
"first_return net st k = (
   iter_next net (Continue st) k = Unimplemented \<or>
   (\<exists>st2. Continue st2 = iter_next net (Continue st) k \<and>
          tl (g_stack st) = g_stack st2 \<and>
    (\<forall>l<k. \<forall>st3. Continue st3 = iter_next net (Continue st) l \<longrightarrow>
                 tl (g_stack st) \<noteq> g_stack st3)))"

(* account existence continues until first return *)

lemma exist_until_return :
  "account_exists (g_current st1 addr) \<Longrightarrow>
   first_return net st1 k \<Longrightarrow>
   l < k \<Longrightarrow>
   Continue st3 = iter_next net (Continue st) l \<Longrightarrow>
   account_exists (g_current st3 addr)"

(* storage changes *)
(* storage changes are first the same as code changes, but also from
   calls out *)
lemma storage_continue :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_vmstate st1 \<in> range InstructionContinue \<Longrightarrow>
   account_storage0 (g_current st1 addr) =
   account_storage0 (g_current st2 addr)"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

(* balance changes *)

end


