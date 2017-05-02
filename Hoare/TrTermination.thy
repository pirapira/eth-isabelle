theory TrTermination

imports Balance

begin

(* basic case: simple instructions *)
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
   vctx_gas v1 > vctx_gas v2"
by (simp add:next0_def next_state_def Let_def
  continue_meter_gas meter_gas_gt_0
  split:if_split_asm option.split_asm)

(* environment becomes a continue *)
lemma env_continue :
  "g_vmstate st1 = InstructionToEnvironment act v1 hint \<Longrightarrow>
   Continue st2 = next0 net (Continue st1) \<Longrightarrow>
   \<exists>v2. g_vmstate st2 = InstructionContinue v2"
by (auto simp add:next0_def next_state_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm)

end

