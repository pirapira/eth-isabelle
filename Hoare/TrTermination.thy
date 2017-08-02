theory TrTermination

imports Balance

begin

definition vm_gas :: "instruction_result \<Rightarrow> int" where
"vm_gas vm = (case vm of
   InstructionContinue v \<Rightarrow> vctx_gas v
 | InstructionToEnvironment (ContractCall args) v hint \<Rightarrow>
    vctx_gas v + uint (callarg_gas args)
 | InstructionToEnvironment (ContractDelegateCall args) v hint \<Rightarrow>
    vctx_gas v + uint (callarg_gas args)
 | InstructionToEnvironment _ v hint \<Rightarrow>
    vctx_gas v)"

definition stack_gas2 ::
   "(world_state * variable_ctx * constant_ctx * stack_hint) list \<Rightarrow> nat \<Rightarrow> int" where
"stack_gas2 lst i = (let (_,v,_,_) = lst!i in vctx_gas v)"

definition stack_gas ::
   "(world_state * variable_ctx * constant_ctx * stack_hint) \<Rightarrow> int" where
"stack_gas lst = (let (_,v,_,_) = lst in vctx_gas v)"

definition system_gas :: "global0 \<Rightarrow> int" where
"system_gas g =
   vm_gas (g_vmstate g) + sum_list (map stack_gas (g_stack g))"

lemma change_vmstate :
  "g_stack st1 = g_stack st2 \<Longrightarrow>
   vm_gas (g_vmstate st1) > vm_gas (g_vmstate st2) \<Longrightarrow>
   system_gas st1 > system_gas st2"
by (auto simp add:system_gas_def)

lemma change_continue :
  "vctx_gas v1 > vctx_gas v2 \<Longrightarrow>
   vm_gas (InstructionContinue v1) > vm_gas (InstructionContinue v2)"
by (auto simp add:vm_gas_def)

(* basic case: simple instructions *)
lemma basic_aux :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some inst = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   inst \<noteq> Misc STOP \<Longrightarrow>
   inst \<noteq> Misc SUICIDE \<Longrightarrow>
   inst \<noteq> Misc RETURN \<Longrightarrow>
   inst \<noteq> Misc CALL \<Longrightarrow>
   inst \<noteq> Misc CALLCODE \<Longrightarrow>
   inst \<noteq> Misc DELEGATECALL \<Longrightarrow>
   inst \<notin> range Unknown \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   vctx_gas v1 > vctx_gas v2"
by (simp add:next0_def next_state_def Let_def
  continue_meter_gas meter_gas_gt_0
  split:if_split_asm option.split_asm)

lemma continue_stack :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = g_stack st1"
by (auto simp add:next0_def next_state_def Let_def
  continue_meter_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma basic :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some inst = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   inst \<noteq> Misc STOP \<Longrightarrow>
   inst \<noteq> Misc SUICIDE \<Longrightarrow>
   inst \<noteq> Misc RETURN \<Longrightarrow>
   inst \<noteq> Misc CALL \<Longrightarrow>
   inst \<noteq> Misc CALLCODE \<Longrightarrow>
   inst \<noteq> Misc DELEGATECALL \<Longrightarrow>
   inst \<notin> range Unknown \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
using basic_aux change_continue change_vmstate continue_stack
by force

(* environment becomes a continue *)
lemma env_continue :
  "g_vmstate st1 = InstructionToEnvironment act v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   \<exists>v2. g_vmstate st2 = InstructionContinue v2"
by (auto simp add:next0_def next_state_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma continue_meter :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some inst = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_gas v2 = vctx_gas v1 - meter_gas inst v1 (g_cctx st1) net"
by (auto simp add:next0_def next_state_def Let_def
  continue_meter_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)



lemma env_meter :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment act v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   act \<notin> range ContractFail \<Longrightarrow>
   Some inst = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_gas v2 = vctx_gas v1 - meter_gas inst v1 (g_cctx st1) net"
by (auto simp add:next0_def next_state_def Let_def
  env_meter_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma call_to_env :
"inst \<in> {Misc CALL, Misc STOP, Misc RETURN, Misc SUICIDE, Misc CALLCODE, Misc DELEGATECALL} \<Longrightarrow>
 \<exists>act v2 x33. instruction_sem v1 c inst net =
 InstructionToEnvironment act v2 x33"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x13 ; clarsimp simp: rw
           split:list.splits)
done

lemmas split_inst = arith_inst.split_asm bits_inst.split_asm 
  sarith_inst.split_asm
  info_inst.split_asm
  memory_inst.split_asm
  storage_inst.split_asm
  pc_inst.splits
  stack_inst.split_asm
  bits_inst.split_asm
  log_inst.split_asm
  bits_inst.split_asm
  misc_inst.split_asm
  inst.splits
 list.splits option.splits if_splits

lemma did_not_call :
"inst \<notin> {Misc CALL, Misc CALLCODE} \<Longrightarrow>
 instruction_sem v1 c inst net =
 InstructionToEnvironment (ContractCall args) v2 x33 \<Longrightarrow>
 False"
by (auto simp:instruction_sem_simps Let_def split:split_inst)

lemma did_not_delegate :
"inst \<noteq> Misc DELEGATECALL \<Longrightarrow>
 instruction_sem v1 c inst net =
 InstructionToEnvironment (ContractDelegateCall args) v2 x33 \<Longrightarrow>
 False"
by (auto simp:instruction_sem_simps Let_def split:split_inst)

lemma word_convert_compare :
   "x \<ge> 0 \<Longrightarrow> uint (word_of_int x :: w256) \<le> x"
  by (simp add: int_word_uint zmod_le_nonneg_dividend)

lemma cmem_new :
 "memu \<ge> 0 \<Longrightarrow>
  Cmem (new_memory_consumption
    inst memu x21 x21a z x21c x21d x21e x21f)
   \<ge> Cmem memu"
  by (simp add: Cmem_lift vctx_memory_usage_never_decreases)

lemma cmem_new_helper :
 "memu \<ge> 0 \<Longrightarrow> k > 0 \<Longrightarrow>
  0 < Cmem (new_memory_consumption
    inst memu x21 x21a z x21c x21d x21e x21f) +
   (k - Cmem memu)"
using cmem_new
proof -
  assume a1: "0 \<le> memu"
  assume "0 < k"
  then have "\<not> k \<le> 0"
    by (metis not_less)
  then have "\<not> k \<le> Cmem memu - Cmem (new_memory_consumption inst memu x21 x21a z x21c x21d x21e x21f)"
    using a1 by (meson cmem_new le_iff_diff_le_0 order.trans)
  then show ?thesis
    by linarith
qed

lemma cmem_new_helper2 :
 "memu \<ge> 0 \<Longrightarrow> k > 0 \<Longrightarrow>
  0 < k + (Cmem (new_memory_consumption
    inst memu x21 x21a z x21c x21d x21e x21f) - Cmem memu)"
  by (simp add: add_pos_nonneg cmem_new)

lemma min_L :
   "v1 < v2 \<Longrightarrow>
    v1 > 0 \<Longrightarrow>
     min (L (gs-v1)) x < min (L (gs-v2)) x + v2"
by (auto simp add:L_def)

lemma min_L_helper :
   "v1 < v2 \<Longrightarrow>
    v1 > 0 \<Longrightarrow>
    memu \<ge> 0 \<Longrightarrow>
     min (L (gs-v1-z)) x <
    Cmem (new_memory_consumption
    inst memu x21 x21a z12 x21c x21d x21e x21f) - Cmem memu
    + (min (L (gs-v2-z)) x + v2)"
using cmem_new [of memu inst x21 x21a z12 x21c x21d x21e x21f]
  L_def
by force

lemma min_L_helper2 :
   "v1 < v2 \<Longrightarrow>
    v1 > 0 \<Longrightarrow>
    memu \<ge> 0 \<Longrightarrow>
    min (L (gs-v1-z)) x <
    v2 + (Cmem (new_memory_consumption
    inst memu x21 x21a z12 x21c x21d x21e x21f)
    + (min (L (gs-v2-z)) x  - Cmem memu))"
using cmem_new [of memu inst x21 x21a z12 x21c x21d x21e x21f]
  L_def
by force

lemma call_gas_compare :
"vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_stack v1 = x21 # x21a # x21b # x21c # x21d # x21e # x21f # x22f \<Longrightarrow>
 Ccallgas x21 x21a x21b (\<not> vctx_account_existence v1 (vctx_recipient v1 c))
                (vctx_gas v1) net
                (calc_memu_extra (vctx_memory_usage v1) x21 x21a x21b x21c x21d x21e
                  x21f)
       < meter_gas (Misc CALL) v1 c net"
by (simp add:gas_simps  Ccallgas_def meter_gas_def C_def
  thirdComponentOfC_def Gcallstipend_def vctx_stack_default_def
  uint_nat cmem_new_helper  cmem_new_helper2
calc_memu_extra_def min_L_helper min_L_helper2)

lemma memu_extra_ge0 :
"memu \<ge> 0 \<Longrightarrow>
 calc_memu_extra memu x21 x21a x21b x21c x21d x21e x21f \<ge> 0"
by (simp add:calc_memu_extra_def cmem_new)

lemma memu_extra2_ge0 :
"vctx_memory_usage v \<ge> 0 \<Longrightarrow>
 calc_memu_extra2 v a b c x21c x21d x21e x21f \<ge> 0"
by (simp add:calc_memu_extra2_def cmem_new)

lemma callgas_ge0 :
  "memu \<ge> 0 \<Longrightarrow>
   Ccallgas x21 x21a x21b aex gas1 net memu \<ge> 0"
by (auto simp add:gas_simps  Ccallgas_def meter_gas_def C_def
  thirdComponentOfC_def Gcallstipend_def vctx_stack_default_def
  cmem_new_helper  cmem_new_helper2
calc_memu_extra_def min_L_helper min_L_helper2 L_def)

lemma aux :
 "x < y \<Longrightarrow> x \<ge> 0 \<Longrightarrow> uint (word_of_int x :: w256) < y"
using word_convert_compare [of x]
by auto

lemma call_system_gas :
"instruction_sem v1 c (Misc CALL) net =
 InstructionToEnvironment (ContractCall args) v2 x33 \<Longrightarrow>
  vctx_next_instruction v1 c = Some (Misc CALL) \<Longrightarrow>
 vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_gas v1 > vctx_gas v2 + uint (callarg_gas args)"
apply (auto simp:instruction_sem_simps Let_def split:split_inst)
apply (rule aux)
apply (rule call_gas_compare, auto)
apply (simp add:vctx_recipient_def vctx_next_instruction_default_def
  vctx_stack_default_def)
using callgas_ge0 memu_extra_ge0 apply force
done

lemma memu_code :
"new_memory_consumption (Misc CALLCODE)
         memu x21 x21a x21b x21c
         x21d x21e x21f =
new_memory_consumption (Misc CALL)
         memu x21 x21a x21b x21c
         x21d x21e x21f"
by (simp add:new_memory_consumption.simps)

lemma callcode_gas_compare :
"vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_stack v1 = x21 # x21a # x21b # x21c # x21d # x21e # x21f # x22f \<Longrightarrow>
 Ccallgas x21 x21a x21b (\<not> vctx_account_existence v1 (vctx_recipient v1 c))
        (vctx_gas v1) net
        (calc_memu_extra (vctx_memory_usage v1) x21 x21a x21b x21c x21d x21e x21f)
       < meter_gas (Misc CALLCODE) v1 c net"
by (simp add:gas_simps  Ccallgas_def meter_gas_def C_def
  thirdComponentOfC_def Gcallstipend_def vctx_stack_default_def
  uint_nat cmem_new_helper  cmem_new_helper2
calc_memu_extra_def min_L_helper min_L_helper2 memu_code)

lemma callcode_system_gas :
"instruction_sem v1 c (Misc CALLCODE) net =
 InstructionToEnvironment (ContractCall args) v2 x33 \<Longrightarrow>
 vctx_next_instruction v1 c = Some (Misc CALLCODE) \<Longrightarrow>
 vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_gas v1 > vctx_gas v2 + uint (callarg_gas args)"
apply (auto simp:instruction_sem_simps Let_def split:split_inst)
apply (rule aux)
apply (rule callcode_gas_compare, auto)
apply (simp add:vctx_recipient_def vctx_next_instruction_default_def
  vctx_stack_default_def)
using callgas_ge0 memu_extra_ge0 apply force
done

lemma memory_weird :
"new_memory_consumption (Misc DELEGATECALL)
        (vctx_memory_usage v1) x21 x21a x21b x21c
        x21d x21e (x22e ! k) = 
 new_memory_consumption (Misc DELEGATECALL)
        (vctx_memory_usage v1) x21 x21a x21b x21c
        x21d x21e 0"
by (simp add:new_memory_consumption.simps)

lemma delegate_gas_compare :
 "\<not> before_homestead net \<Longrightarrow>
  vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
  vctx_stack v1 = x21 # x21a # x21b # x21c # x21d # x21e # x22e \<Longrightarrow>
  Ccallgas x21 x21a 0
        (\<not> vctx_account_existence v1 (vctx_recipient v1 c))
        (vctx_gas v1) net
        (calc_memu_extra2 v1 x21 x21a x21b x21c
          x21d x21e (vctx_stack_default 6 v))
       < meter_gas (Misc DELEGATECALL) v1 c net"
by (auto simp add:gas_simps  Ccallgas_def meter_gas_def C_def
  thirdComponentOfC_def Gcallstipend_def vctx_stack_default_def
  uint_nat cmem_new_helper  cmem_new_helper2
calc_memu_extra2_def min_L_helper min_L_helper2
memory_weird
split:option.splits)

lemma delegate_system_gas :
"instruction_sem v1 c (Misc DELEGATECALL) net =
 InstructionToEnvironment (ContractDelegateCall args) v2 x33 \<Longrightarrow>
 vctx_next_instruction v1 c = Some (Misc DELEGATECALL) \<Longrightarrow>
 vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_gas v1 > vctx_gas v2 + uint (callarg_gas args)"
apply (auto simp:instruction_sem_simps Let_def split:split_inst)
apply (rule aux)
apply (rule delegate_gas_compare, auto)
apply (simp add:vctx_recipient_def vctx_next_instruction_default_def
  vctx_stack_default_def)
using callgas_ge0 memu_extra2_ge0 apply force
done

fun system_vms_vm :: "instruction_result \<Rightarrow> variable_ctx list" where
"system_vms_vm (InstructionContinue v) = [v]"
| "system_vms_vm (InstructionToEnvironment act v hint) = [v]"

fun tuple_4_2 :: "world_state * variable_ctx * constant_ctx * stack_hint \<Rightarrow> variable_ctx" where
"tuple_4_2 (_,v,_,_) = v"

definition system_vms :: "global0 \<Rightarrow> variable_ctx list" where
"system_vms g = system_vms_vm (g_vmstate g) @ map tuple_4_2 (g_stack g)"

definition memu_invariant :: "global0 \<Rightarrow> bool" where
"memu_invariant g = (\<forall>v \<in> set (system_vms g). vctx_memory_usage v \<ge> 0)"

lemma memu_next_state :
  "vctx_memory_usage v \<ge> 0 \<Longrightarrow>
   v2 \<in> set (system_vms_vm (next_state stopper c net (InstructionContinue v))) \<Longrightarrow>
   vctx_memory_usage v2 \<ge> 0"
apply (auto simp add:next_state_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)
apply (case_tac "instruction_sem v c x2 net", auto)
  using memu_good apply force
  using memu_good_env by fastforce

lemma memu_next_aux1 :
 "memu_invariant st1 \<Longrightarrow>
  g_vmstate st1 = InstructionContinue x1 \<Longrightarrow>
  memu_invariant
        (st1 \<lparr>g_vmstate := next_state stopper
             c net
             (InstructionContinue x1)\<rparr>)"
apply (auto simp add: memu_invariant_def system_vms_def)
using memu_next_state by metis

lemma memu_next_aux2 :
 "memu_invariant st1 \<Longrightarrow>
  g_vmstate st1 = InstructionToEnvironment act v1 hint \<Longrightarrow>
  memu_invariant (st1 \<lparr>g_vmstate :=
     InstructionContinue
             (v1 \<lparr>vctx_stack := st, vctx_gas := gs \<rparr>)\<rparr>)"
by (auto simp add: memu_invariant_def system_vms_def)

lemma memu_simp1 :
 "memu_invariant (st1
         \<lparr>g_current := st, g_vmstate := x\<rparr>) =
  memu_invariant (st1 \<lparr>g_vmstate := x\<rparr>)"
by (auto simp add: memu_invariant_def system_vms_def)


lemma memu_start :
 "0 \<le> vctx_memory_usage (start_env a b c d e f x)"
by (simp add: start_env_def)

lemma memu_create :
"0 \<le> vctx_memory_usage (create_env a b c d e f g h x)"
by (simp add: create_env_def)

lemma memu_update_world :
 "vctx_memory_usage (vctx_update_from_world v w x y) =
  vctx_memory_usage v"
by (simp add: vctx_update_from_world_def)

lemma memu_next :
  "memu_invariant st1 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   memu_invariant st2"
apply (auto simp add:next0_def Let_def  memu_next_aux1
  memu_simp1
  memu_invariant_def system_vms_def
  memu_start memu_create memu_update_world
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)
using memu_next_state apply metis
using memu_next_state apply metis
done

lemma delegate_failure_sem :
"before_homestead net \<Longrightarrow>
 instruction_sem v1 c (Misc DELEGATECALL) net =
 InstructionToEnvironment act v2 x33 \<Longrightarrow>
 act \<in> range ContractFail"
by (auto simp:instruction_sem_simps Let_def split:split_inst)

lemma delegate_failure_next_state :
"before_homestead net \<Longrightarrow>
 vctx_next_instruction v c = Some (Misc DELEGATECALL) \<Longrightarrow>
 next_state stopper c net (InstructionContinue v) =
    InstructionToEnvironment act v2 x33 \<Longrightarrow>
 act \<in> range ContractFail"
by (auto simp:next_state_def delegate_failure_sem Let_def split:split_inst)

lemma stop_return :
"vctx_next_instruction v c = Some (Misc STOP) \<Longrightarrow>
 next_state stopper c net (InstructionContinue v) =
    InstructionToEnvironment act v2 x33 \<Longrightarrow>
 act \<in> range ContractFail \<union> range ContractReturn"
by (auto simp:next_state_def instruction_sem_simps Let_def split:split_inst)

lemma return_return :
"vctx_next_instruction v c = Some (Misc RETURN) \<Longrightarrow>
 next_state stopper c net (InstructionContinue v) =
    InstructionToEnvironment act v2 x33 \<Longrightarrow>
 act \<in> range ContractFail \<union> range ContractReturn"
by (auto simp:next_state_def instruction_sem_simps Let_def split:split_inst)

lemma suicide_return :
"vctx_next_instruction v c = Some (Misc SUICIDE) \<Longrightarrow>
 next_state stopper c net (InstructionContinue v) =
    InstructionToEnvironment act v2 x33 \<Longrightarrow>
 act \<in> range ContractFail \<union> range ContractSuicide"
by (auto simp:next_state_def instruction_sem_simps Let_def split:split_inst)

lemma fail_stack :
"next0 net (Continue st1) = Continue st2 \<Longrightarrow>
 g_vmstate st1 = InstructionToEnvironment (ContractFail lst) v hint \<Longrightarrow>
 length (g_stack st2) + 1 = length (g_stack st1)"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma return_stack :
"next0 net (Continue st1) = Continue st2 \<Longrightarrow>
 g_vmstate st1 = InstructionToEnvironment (ContractReturn lst) v hint \<Longrightarrow>
 length (g_stack st2) + 1 = length (g_stack st1)"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma suicide_stack :
"next0 net (Continue st1) = Continue st2 \<Longrightarrow>
 g_vmstate st1 = InstructionToEnvironment (ContractSuicide lst) v hint \<Longrightarrow>
 length (g_stack st2) + 1 = length (g_stack st1)"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma env_stack :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   g_stack st2 = g_stack st1"
by (auto simp add:next0_def next_state_def Let_def
  continue_meter_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma call_success :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc CALL) = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def call_system_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma callcode_success :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc CALLCODE) = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def callcode_system_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma delegate_success :
  "\<not> before_homestead net \<Longrightarrow>
   g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractDelegateCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc DELEGATECALL) = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def delegate_system_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

(* next have to show that the amount of gas cannot increase.
   I'll split it to many cases first, and then collect them *)

lemma env_gas :
 "vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
  instruction_sem v1 c inst net = InstructionToEnvironment act v2 x33 \<Longrightarrow>
  vctx_gas v2 \<le> vctx_gas v1"
using env_meter_gas meter_gas_ge_0
by force

lemma gas_le_continue :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   vctx_gas v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
apply (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def delegate_system_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)
  using continue_decr_gas apply force
subgoal proof -
  fix x2 :: inst and x32 :: variable_ctx and x1 :: call_arguments and x33 :: "(int \<times> int) option"
  assume a1: "0 \<le> vctx_memory_usage v1"
  assume a2: "vctx_next_instruction v1 (g_cctx st1) = Some x2"
  assume a3: "instruction_sem v1 (g_cctx st1) x2 net = InstructionToEnvironment (ContractCall x1) x32 x33"
  have f4: "\<forall>x1a x2a x5. (vctx_gas (x1a::variable_ctx) + uint (callarg_gas (x2a::call_arguments)) < vctx_gas (x5::variable_ctx)) = (\<not> 0 \<le> vctx_gas x1a + uint (callarg_gas x2a) + - 1 * vctx_gas x5)"
    by auto
  have f5: "x2 \<in> {Misc CALL, Misc CALLCODE}"
    using a3 by (meson did_not_call)
  have f6: "\<forall>x1a x2a x5. (vctx_gas (x1a::variable_ctx) + uint (callarg_gas (x2a::call_arguments)) < vctx_gas (x5::variable_ctx)) = (\<not> 0 \<le> vctx_gas x1a + uint (callarg_gas x2a) + - 1 * vctx_gas x5)"
    by auto
  { assume "instruction_sem v1 (g_cctx st1) (Misc CALLCODE) net = InstructionToEnvironment (ContractCall x1) x32 x33 \<and> vctx_next_instruction v1 (g_cctx st1) = Some (Misc CALLCODE)"
    then have "\<not> 0 \<le> vctx_gas x32 + uint (callarg_gas x1) + - 1 * vctx_gas v1"
      using f4 a1 by (metis callcode_system_gas)
    then have "vctx_gas x32 + uint (callarg_gas x1) + - 1 * vctx_gas v1 \<le> 0"
      by fastforce }
  moreover
  { assume "x2 \<noteq> Misc CALLCODE"
    then have "\<not> 0 \<le> vctx_gas x32 + uint (callarg_gas x1) + - 1 * vctx_gas v1"
      using f6 f5 a3 a2 a1 call_system_gas by blast
    then have "vctx_gas x32 + uint (callarg_gas x1) + - 1 * vctx_gas v1 \<le> 0"
      by auto }
  ultimately show "vctx_gas x32 + uint (callarg_gas x1) \<le> vctx_gas v1"
    using a3 a2 by auto
qed
subgoal proof -
  fix x2 :: inst and x32 :: variable_ctx and x2a :: call_arguments and x33 :: "(int \<times> int) option"
  assume a1: "0 \<le> vctx_memory_usage v1"
  assume a2: "vctx_next_instruction v1 (g_cctx st1) = Some x2"
  assume a3: "instruction_sem v1 (g_cctx st1) x2 net = InstructionToEnvironment (ContractDelegateCall x2a) x32 x33"
  have "\<forall>i v c n ca va z. i = Misc DELEGATECALL \<or> instruction_sem v c i n \<noteq> InstructionToEnvironment (ContractDelegateCall ca) va z"
    by (meson did_not_delegate)
  then have "x2 = Misc DELEGATECALL"
    using a3 by meson
  then show "vctx_gas x32 + uint (callarg_gas x2a) \<le> vctx_gas v1"
    using a3 a2 a1 delegate_system_gas by fastforce
qed
  using env_gas apply fastforce
  using env_gas apply fastforce
  using env_gas apply fastforce
  using env_gas apply fastforce
done

lemma gas_le_fail :
  "g_vmstate st1 = InstructionToEnvironment (ContractFail lst) v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   vctx_gas v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)

lemma gas_update_world :
  "vctx_gas (vctx_update_from_world v1 x y v2) =
   vctx_gas v1 + vctx_gas v2"
by (simp add:vctx_update_from_world_def)

lemma gas_le_return :
  "g_vmstate st1 = InstructionToEnvironment (ContractReturn lst) v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   vctx_gas v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_update_world
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)

lemma gas_le_suicide :
  "g_vmstate st1 = InstructionToEnvironment (ContractSuicide lst) v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_update_world
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)

lemma gas_create_env :
  "vctx_gas (create_env a state value data gs cller origin block x) =
   gs"
by (simp add:create_env_def)


lemma gas_le_create :
  "g_vmstate st1 = InstructionToEnvironment (ContractCreate lst) v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_create_env
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)

lemma gas_start_env :
  "vctx_gas (start_env a state args cller origin block x) =
   uint (callarg_gas args)"
by (simp add:start_env_def)


lemma gas_le_delegate :
  "g_vmstate st1 = InstructionToEnvironment (ContractDelegateCall args) v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_start_env
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)

lemma gas_le_call :
  "g_vmstate st1 = InstructionToEnvironment (ContractCall args) v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_start_env
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)


lemma gas_le :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow>
   vm_gas (g_vmstate st1) \<ge> 0 \<Longrightarrow>
   system_gas st1 \<ge> system_gas st2"
apply (cases "g_vmstate st1")
apply (simp add:vm_gas_def memu_invariant_def system_vms_def
  gas_le_continue)
apply (case_tac x21)
apply (auto simp add:vm_gas_def memu_invariant_def system_vms_def
  gas_le_call gas_le_delegate gas_le_create gas_le_fail
  gas_le_suicide gas_le_return Let_def)
done

fun estimate_vm :: "instruction_result \<Rightarrow> int" where
"estimate_vm (InstructionToEnvironment (ContractDelegateCall args) _ _) = 4"
| "estimate_vm (InstructionToEnvironment (ContractCall args) _ _) = 4"
| "estimate_vm (InstructionToEnvironment (ContractCreate args) _ _) = 4"
| "estimate_vm (InstructionToEnvironment _ _ _) = 0"
| "estimate_vm _ = 1"

definition estimate :: "global0 \<Rightarrow> int" where
"estimate g = 5*system_gas g + 2*int (length (g_stack g)) + estimate_vm (g_vmstate g)"

lemma estimation_basic :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some inst = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   inst \<noteq> Misc STOP \<Longrightarrow>
   inst \<noteq> Misc SUICIDE \<Longrightarrow>
   inst \<noteq> Misc RETURN \<Longrightarrow>
   inst \<noteq> Misc CALL \<Longrightarrow>
   inst \<noteq> Misc CALLCODE \<Longrightarrow>
   inst \<noteq> Misc DELEGATECALL \<Longrightarrow>
   inst \<notin> range Unknown \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
apply (simp add:estimate_def)
  by (smt basic env_stack)

lemma inst_clean_none :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   None = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   False"
by (auto simp:next0_def next_state_def instruction_sem_simps Let_def split:split_inst)


lemma inst_clean :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some inst = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   inst \<in>  {Misc STOP, Misc SUICIDE,
      Misc RETURN, 
      Misc CALL, Misc CALLCODE,
      Misc DELEGATECALL} \<union> range Unknown \<Longrightarrow>
   False"
by (auto simp:next0_def next_state_def instruction_sem_simps Let_def split:split_inst)

lemma estimation_clean :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionContinue v2 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
apply (cases "vctx_next_instruction v1 (g_cctx st1)")
using inst_clean_none apply force
using inst_clean estimation_basic apply fastforce
done

lemma call_success2 :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc CALL) = vctx_next_instruction v1 (g_cctx st1) \<or>
   Some (Misc CALLCODE) = vctx_next_instruction v1 (g_cctx st1)"
by (auto simp:next0_def next_state_def instruction_sem_simps Let_def split:split_inst)

lemma call_success3 :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
using call_success callcode_success call_success2 by metis

lemma delegate_success2 :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractDelegateCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc DELEGATECALL) = vctx_next_instruction v1 (g_cctx st1)
   \<and> \<not> before_homestead net"
by (auto simp:next0_def next_state_def instruction_sem_simps Let_def split:split_inst)

lemma delegate_success3 :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractDelegateCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
using delegate_success delegate_success2 by metis

lemma estimation_call :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 =
     InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
apply (simp add:estimate_def)
by (smt call_success3 env_stack)

lemma estimation_delegate :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 =
     InstructionToEnvironment (ContractDelegateCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
apply (simp add:estimate_def)
by (smt delegate_success3 env_stack)

lemma create_success :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCreate args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2"
apply (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_start_env
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)
using create_decr_gas by force

lemma estimation_create :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 =
     InstructionToEnvironment (ContractCreate args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
apply (simp add:estimate_def)
by (smt create_success env_stack)

lemma estimation_fail :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 =
     InstructionToEnvironment (ContractFail args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow>
   vm_gas (g_vmstate st1) \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
by (simp add:estimate_def env_stack gas_le)

lemma estimation_return :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 =
     InstructionToEnvironment (ContractReturn args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow>
   vm_gas (g_vmstate st1) \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
by (simp add:estimate_def env_stack gas_le)

lemma estimation_suicide :
  "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 =
     InstructionToEnvironment (ContractSuicide args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow>
   vm_gas (g_vmstate st1) \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
by (simp add:estimate_def env_stack gas_le)

lemma stack_limit :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   length (g_stack st1) + 1 \<ge> length (g_stack st2)"
by (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def stack_gas_def
  gas_start_env
  split:if_split_asm option.split_asm list.split_asm
   contract_action.splits stack_hint.split_asm
   instruction_result.splits)

lemma env_continue_est :
  "g_vmstate st1 = InstructionToEnvironment act v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   estimate_vm (g_vmstate st2) = 1"
by (auto simp add:next0_def next_state_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

lemma super_hard :
   "s2 + 1 = s1 \<Longrightarrow>
    g2 \<le> g1 \<Longrightarrow>
    5 * g2 + 2 * int s2 + 1 < 5 * g1 + 2 * int s1"
  by simp


lemma estimation :
  "Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow>
   vm_gas (g_vmstate st1) \<ge> 0 \<Longrightarrow>
   estimate st1 > estimate st2"
apply (cases "g_vmstate st1")
apply (cases "g_vmstate st2")
apply (clarsimp simp add:memu_invariant_def system_vms_def)
using estimation_clean apply force
apply (case_tac x21)
apply (clarsimp simp add:memu_invariant_def system_vms_def
  estimation_call)
apply (clarsimp simp add:memu_invariant_def system_vms_def
  estimation_delegate)
apply (clarsimp simp add:memu_invariant_def system_vms_def
  estimation_create)
apply (auto simp add:estimation_fail estimation_return estimation_suicide)
apply (case_tac x21)
apply (simp add:estimate_def env_continue_est)
using stack_limit gas_le apply force
apply (simp add:estimate_def env_continue_est)
using stack_limit gas_le apply force
apply (simp add:estimate_def env_continue_est)
using stack_limit gas_le apply force
apply (simp add:estimate_def env_continue_est)
using gas_le
  apply (smt fail_stack of_nat_0_less_iff of_nat_add zero_less_one) 
defer
apply (simp add:estimate_def env_continue_est)
using gas_le
  apply (smt return_stack of_nat_0_less_iff of_nat_add zero_less_one) 
apply (simp add:estimate_def env_continue_est)
apply (rule super_hard)
using suicide_stack apply force
using gas_le apply force
done

(* gas cannot be zero *)

definition gas_invariant :: "global0 \<Rightarrow> bool" where
"gas_invariant g = (\<forall>v \<in> set (system_vms g). vctx_gas v \<ge> 0)"

lemma next_state_gas_continue :
  "next_state stopper c next res = InstructionContinue v2 \<Longrightarrow>
   vctx_gas v2 \<ge> 0"
by (auto simp add:next0_def next_state_def Let_def
  check_resources_def continue_meter_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma next_state_gas_env :
  "vctx_gas v1 \<ge> 0 \<Longrightarrow>
   next_state stopper c next (InstructionContinue v1) =
      InstructionToEnvironment act v2 hint \<Longrightarrow>
   vctx_gas v2 \<ge> 0"
by (auto simp add:next0_def next_state_def Let_def
  check_resources_def env_meter_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma gas_next :
  "gas_invariant st1 \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   gas_invariant st2"
apply (auto simp add:next0_def Let_def
  gas_invariant_def system_vms_def
  gas_update_world gas_create_env gas_start_env L_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

apply (case_tac "next_state (\<lambda>_. ()) (g_cctx st1) net
                 (InstructionContinue x1)", auto)
using next_state_gas_continue apply force
using next_state_gas_env apply force
apply (case_tac "next_state (\<lambda>_. ()) (g_cctx st1) net
                 (InstructionContinue x1)", auto)
using next_state_gas_continue apply force
using next_state_gas_env apply force
done

fun iter_next :: "network \<Rightarrow> global_state \<Rightarrow> nat \<Rightarrow> global_state" where
"iter_next net g 0 = g"
| "iter_next net g (Suc n) = iter_next net (next0 net g) n"

fun seq_next :: "network \<Rightarrow> global_state \<Rightarrow> nat \<Rightarrow> global_state list" where
"seq_next net g 0 = [g]"
| "seq_next net g (Suc n) = g # seq_next net (next0 net g) n"

lemma seq_next_nil : "seq_next net g n = [] \<Longrightarrow> False"
by (cases n, auto)

lemma iter_seq : "last (seq_next net g n) = iter_next net g n"
apply (induction n arbitrary:g, auto)
using seq_next_nil apply force
done

end

