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
   memu_invariant st1 \<Longrightarrow>
   system_gas st1 > system_gas st2 + 699"
apply (simp add: memu_invariant_def system_vms_def)
using call_success_tight callcode_success_tight call_success2
by metis

fun count_call :: "global_state \<Rightarrow> int" where
"count_call (Continue g) = (case g_vmstate g of
   InstructionToEnvironment (ContractCall _) v hint \<Rightarrow> 1
 | _ \<Rightarrow> 0)"
| "count_call _ = 0"



definition count_calls :: "network \<Rightarrow> global_state \<Rightarrow> nat \<Rightarrow> int" where
"count_calls net g n =
   sum_list (map count_call (seq_next net g n))"

lemma count_calls_next :
  "count_calls net (next0 net st) num +
   count_call st =
   count_calls net st (num+1)"
by (auto simp:count_calls_def)

lemma gas_le2 :
  "Continue st =
  next0 net (Continue st1) \<Longrightarrow>
  memu_invariant st1 \<Longrightarrow>
  gas_invariant st1 \<Longrightarrow>
  system_gas st \<le> system_gas st1"
by (rule gas_le [of st net st1],
   auto simp:gas_invariant_def system_vms_def vm_gas_def
     split:instruction_result.splits contract_action.splits)

lemma estimate_calls_continue :
"(\<forall>st1 v1.(g_vmstate st1 = InstructionContinue v1 \<longrightarrow>
        memu_invariant st1 \<longrightarrow>
        gas_invariant st1 \<longrightarrow>
        iter_next net (Continue st1) num =
        Continue st2 \<longrightarrow>
        count_calls net (Continue st1) num * 699
        \<le> system_gas st1 - system_gas st2)) \<Longrightarrow>

      g_vmstate st = InstructionContinue v \<Longrightarrow>
       iter_next net (Continue st) num =
           Continue st2 \<Longrightarrow>
   memu_invariant st \<Longrightarrow> gas_invariant st \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow> gas_invariant st1 \<Longrightarrow>
       Continue st = next0 net (Continue st1) \<Longrightarrow>
       g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
       iter_next net (Continue st1) (Suc num) =
         Continue st2 \<Longrightarrow>
       count_calls net (Continue st1) (Suc num) * 699
          \<le> system_gas st1 - system_gas st2"
unfolding count_calls_def
using gas_le2 [of st net st1] by force

lemma unimp_cont :
"iter_next net Unimplemented num = Continue st2 \<Longrightarrow> False"
by (induction num; auto simp:next0_def)

lemma finished_cont :
"iter_next net (Finished f) num = Continue st2 \<Longrightarrow> False"
by (induction num; auto simp:next0_def)

lemma anno_stuck :
   "g_vmstate st1 = InstructionAnnotationFailure \<Longrightarrow>
    Continue st2 = next0 net (Continue st1) \<Longrightarrow>
    g_vmstate st2 = InstructionAnnotationFailure"
by (simp add:next0_def next_state_def)

lemma anno_count :
   "g_vmstate st1 = InstructionAnnotationFailure \<Longrightarrow>
    count_calls net (Continue st1) num * 699 = 0"
by(induction num arbitrary:st1;
   simp add:count_calls_def next0_def next_state_def)

lemma anno_simp :
"g_vmstate st1 = InstructionAnnotationFailure \<Longrightarrow>
 st1\<lparr>g_vmstate := InstructionAnnotationFailure\<rparr> = st1"
by simp

lemma anno_stuck_gas :
   "g_vmstate st1 = InstructionAnnotationFailure \<Longrightarrow>
    iter_next net (Continue st1) num = Continue st2 \<Longrightarrow>
    system_gas st1 = system_gas st2"
by(induction num arbitrary:st1 st2;
   auto simp add:count_calls_def next0_def next_state_def
     anno_simp)

lemma more_aux : "x = (0::int) \<Longrightarrow> z\<ge>y \<Longrightarrow> x \<le> z - y"
by simp

lemma count_calls_cont :
 "g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
  Continue st = next0 net (Continue st1) \<Longrightarrow>
  count_calls net (Continue st1) (Suc num) =
  count_calls net (Continue st) num"
by(simp add:count_calls_def)

lemma split_compare :
 "iter_next net (Continue st) num =
    Continue st2 \<Longrightarrow>
  Continue st = next0 net (Continue st1) \<Longrightarrow>
  count_call (Continue st1) * 699 \<le> system_gas st1 - system_gas st \<Longrightarrow>
  count_calls net (Continue st) num * 699
    \<le> system_gas st - system_gas st2 \<Longrightarrow>
  count_calls net (Continue st1) (Suc num) * 699
    \<le> system_gas st1 - system_gas st2"
by (simp add:count_calls_def)

lemma split_compare2 :
 "iter_next net (Continue st) num =
    Continue st2 \<Longrightarrow>
  Continue st = next0 net (Continue st1) \<Longrightarrow>
  count_call (Continue st1) * 699 +
  count_calls net (Continue st) num * 699
    \<le> system_gas st1 - system_gas st2 \<Longrightarrow>
  count_calls net (Continue st1) (Suc num) * 699
    \<le> system_gas st1 - system_gas st2"
by (simp add:count_calls_def)

lemma split_compare3 :
 "Continue st_b = next0 net (Continue st1) \<Longrightarrow>
  Continue st = next0 net (Continue st_b) \<Longrightarrow>
  count_call (Continue st_b) * 699 \<le>
    system_gas st1 - system_gas st_b \<Longrightarrow>
  count_calls net (Continue st) num * 699
    \<le> system_gas st_b - system_gas st2 \<Longrightarrow>
  count_calls net (Continue st_b) (Suc num) * 699
    \<le> system_gas st1 - system_gas st2"
by (simp add:count_calls_def)

lemma mega_rule :
"next0 net (Continue st_b) = Continue st \<Longrightarrow>
 g_vmstate st = InstructionContinue v \<Longrightarrow>
 memu_invariant st_b \<Longrightarrow>
 gas_invariant st_b \<Longrightarrow>
 ( memu_invariant st_b \<longrightarrow>
   gas_invariant st_b \<longrightarrow>
   count_calls net (Continue st) num3 * 699
    \<le> system_gas st - system_gas st2 ) \<Longrightarrow>
 count_calls net (Continue st) num3 * 699
    \<le> system_gas st_b - system_gas st2"
using gas_le2 [of st net st_b] by force

lemma estimate_calls :
  "at_least_eip150 net \<Longrightarrow>
   g_vmstate st1 = InstructionContinue v1 \<Longrightarrow>
   memu_invariant st1 \<Longrightarrow>
   gas_invariant st1 \<Longrightarrow>
   iter_next net (Continue st1) num = Continue st2 \<Longrightarrow>
   count_calls net (Continue st1) num * 699 \<le>
   system_gas st1 - system_gas st2"
apply (induction num arbitrary:st1 v1  rule:less_induct)
subgoal for num st1 v1
apply (case_tac num, auto)
apply (simp add:count_calls_def)
apply (case_tac "next0 net (Continue st1)", auto)
using unimp_cont apply force
defer
using finished_cont apply force
apply (case_tac "g_vmstate x2")
apply (rule split_compare, auto)
subgoal for num2 st v
using gas_le2 [of st net st1]
apply force
done
apply (metis gas_next lessI memu_next)
subgoal for num2 st
apply (rule more_aux)
using anno_count [of st net num2] count_calls_next
apply (simp add:count_calls_cont)
using gas_le2 [of st net st1]
  anno_stuck_gas  [of st net num2 st2]
apply force
done

subgoal for num2 st_b act v_b x33
apply (case_tac num2, auto)
apply (cases act; auto simp add:count_calls_def)
using call_tight apply force
using gas_le2 [of st2 net st1] apply force
using gas_le2 [of st2 net st1] apply force
using gas_le2 [of st2 net st1] apply force
using gas_le2 [of st2 net st1] apply force
using gas_le2 [of st2 net st1] apply force
subgoal for num3
apply (rule split_compare2, auto)
apply (case_tac "next0 net (Continue st_b)", auto)
using unimp_cont apply force
defer
using finished_cont apply force

apply (rule split_compare3, auto)
apply (cases act; auto simp add:count_calls_def)
subgoal for st args
using call_tight [of net st1 v1 st_b args v_b x33]
by force
subgoal for st args
using gas_le2 [of st_b net st1] by force
subgoal for st args
using gas_le2 [of st_b net st1] by force
subgoal for st args
using gas_le2 [of st_b net st1] by force
subgoal for st args
using gas_le2 [of st_b net st1] by force
subgoal for st args
using gas_le2 [of st_b net st1] by force

apply(case_tac "g_vmstate x2")
defer

subgoal for st
using env_continue [of st_b act v_b x33 st net]
by force

subgoal for st
using env_continue [of st_b act v_b x33 st net]
by force

subgoal for st v
apply (rule mega_rule, auto)
using memu_next apply metis
using gas_next apply metis
using memu_next gas_next
  by (metis Suc_lessD lessI)
done done done done

end
