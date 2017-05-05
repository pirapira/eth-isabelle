theory EstimateCalls

imports TrTermination

begin

lemma call_gas_compare2 :
"vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 at_least_eip150 net \<Longrightarrow>
 vctx_stack v1 = x21 # x21a # x21b # x21c # x21d # x21e # x21f # x22f \<Longrightarrow>
 Ccallgas x21 x21a x21b (\<not> vctx_account_existence v1 (vctx_recipient v1 c))
                (vctx_gas v1) net
                (calc_memu_extra (vctx_memory_usage v1) x21 x21a x21b x21c x21d x21e
                  x21f) + 699
       < meter_gas (Misc CALL) v1 c net"
by (simp add:gas_simps  Ccallgas_def meter_gas_def C_def
  thirdComponentOfC_def Gcallstipend_def vctx_stack_default_def
  uint_nat cmem_new_helper  cmem_new_helper2
calc_memu_extra_def min_L_helper min_L_helper2)

lemma aux2 :
 "x + z < y \<Longrightarrow> x \<ge> 0 \<Longrightarrow> uint (word_of_int x :: w256) + z < y"
using word_convert_compare [of x]
by auto

lemma call_system_gas2 :
"at_least_eip150 net \<Longrightarrow>
 instruction_sem v1 c (Misc CALL) net =
 InstructionToEnvironment (ContractCall args) v2 x33 \<Longrightarrow>
  vctx_next_instruction v1 c = Some (Misc CALL) \<Longrightarrow>
 vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_gas v1 > vctx_gas v2 + uint (callarg_gas args) + 699"
apply (auto simp:instruction_sem_simps Let_def split:split_inst)
apply (rule aux2)
apply (rule call_gas_compare2, auto)
apply (simp add:vctx_recipient_def vctx_next_instruction_default_def
  vctx_stack_default_def)
using callgas_ge0 memu_extra_ge0 apply force
done

lemma callcode_gas_compare2 :
"at_least_eip150 net \<Longrightarrow>
 vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_stack v1 = x21 # x21a # x21b # x21c # x21d # x21e # x21f # x22f \<Longrightarrow>
 Ccallgas x21 x21a x21b (\<not> vctx_account_existence v1 (vctx_recipient v1 c))
    (vctx_gas v1) net
    (calc_memu_extra (vctx_memory_usage v1) x21 x21a x21b x21c x21d x21e x21f)
    + 699   < meter_gas (Misc CALLCODE) v1 c net"
by (simp add:gas_simps  Ccallgas_def meter_gas_def C_def
  thirdComponentOfC_def Gcallstipend_def vctx_stack_default_def
  uint_nat cmem_new_helper  cmem_new_helper2
calc_memu_extra_def min_L_helper min_L_helper2 memu_code)

lemma callcode_system_gas2 :
"at_least_eip150 net \<Longrightarrow>
 instruction_sem v1 c (Misc CALLCODE) net =
 InstructionToEnvironment (ContractCall args) v2 x33 \<Longrightarrow>
 vctx_next_instruction v1 c = Some (Misc CALLCODE) \<Longrightarrow>
 vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
 vctx_gas v1 > vctx_gas v2 + uint (callarg_gas args) + 699"
apply (auto simp:instruction_sem_simps Let_def split:split_inst)
apply (rule aux2)
apply (rule callcode_gas_compare2, auto)
apply (simp add:vctx_recipient_def vctx_next_instruction_default_def
  vctx_stack_default_def)
using callgas_ge0 memu_extra_ge0 apply force
done

lemma call_success_tight :
  "at_least_eip150 net \<Longrightarrow>
   g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc CALL) = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2 + 699"
apply (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def call_system_gas2
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)
using call_system_gas2 by force

lemma callcode_success_tight :
  "at_least_eip150 net \<Longrightarrow>
   g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   Some (Misc CALLCODE) = vctx_next_instruction v1 (g_cctx st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2 + 699"
apply (auto simp add:next0_def next_state_def Let_def
  system_gas_def vm_gas_def callcode_system_gas
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)
using callcode_system_gas2 by force

lemma call_tight :
  "at_least_eip150 net \<Longrightarrow>
   g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   g_vmstate st2 = InstructionToEnvironment (ContractCall args) v2 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   vctx_memory_usage v1 \<ge> 0 \<Longrightarrow>
   system_gas st1 > system_gas st2 + 699"
using call_success_tight callcode_success_tight call_success2
by metis

fun count_call :: "global_state \<Rightarrow> int" where
"count_call (Continue g) = (case g_vmstate g of
   InstructionToEnvironment (ContractCall _) v hint \<Rightarrow> 1
 | _ \<Rightarrow> 0)"
| "count_call _ = 0"

(*

fun iter_next :: "network \<Rightarrow> global_state \<Rightarrow> nat \<Rightarrow> global_state" where
"iter_next net g 0 = g"
| "iter_next net g (Suc n) = iter_next net (next0 net g) n"

fun count_calls :: "network \<Rightarrow> global_state \<Rightarrow> nat \<Rightarrow> int" where
"count_calls net g n = (\<Sum>i=1..n. count_call (iter_next net g i))"

lemma iter_next_next :
  "iter_next net (next0 net st) i = iter_next net st (Suc i)"
by auto

declare iter_next.simps [simp del]
declare count_calls.simps [simp del]

lemma count_calls_next :
  "count_calls net (next0 net st) num +
   count_call (next0 net st) =
   count_calls net st (num+1)"
apply auto
apply (subst count_calls.simps)
apply (subst count_calls.simps)
apply (subst iter_next_next)

lemma estimate_calls_continue :
"      at_least_eip150 net \<Longrightarrow>
       iter_next net (Continue st) num = Continue st2 \<Longrightarrow>
       count_calls net (Continue st) num * 699
           \<le> system_gas st - system_gas st2 \<Longrightarrow>
       at_least_eip150 net \<Longrightarrow>
       Continue st = next0 net (Continue st1) \<Longrightarrow>
       iter_next net (Continue st1) (Suc num) = Continue st2 \<Longrightarrow>
       g_vmstate st2 = InstructionContinue x1 \<Longrightarrow>
       count_calls net (Continue st1) (Suc num) * 699
       \<le> system_gas st1 - system_gas st2"
apply auto

lemma estimate_calls :
  "at_least_eip150 net \<Longrightarrow>
   iter_next net (Continue st1) num = Continue st2 \<Longrightarrow>
   count_calls net (Continue st1) num * 699 \<le>
   system_gas st1 - system_gas st2"
apply (induction num arbitrary:st1 st2, simp)
apply (case_tac "g_vmstate st2",auto)

*)

(*
"count_calls net g 0 = 0"
| "count_calls net g (Suc n) =
     count_call g + count_calls net (next0 net g) n"
*)

end
