theory "ConstantMemory" 

imports 
   "InstructionAux" "../ProgramInAvl"

begin

declare stack_1_1_op_def [simp del]
declare jump_def [simp del]
declare cut_memory.simps [simp del]

theorem lemma_stack_2_1_op :
"stack_2_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_memory v = vctx_memory nv"
apply(auto simp:stack_2_1_op_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

theorem lemma_stack_3_1_op :
"stack_3_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_memory v = vctx_memory nv"
apply(auto simp:stack_3_1_op_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply auto
apply(cases "tl (tl (vctx_stack v))")
apply auto
done

theorem lemma_stack_1_1_op :
"stack_1_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_memory v = vctx_memory nv"
apply(auto simp:stack_1_1_op_def)
apply(cases "vctx_stack v")
apply(auto split:option.split)
done

theorem lemma_jump [simp] :
"jump v c = InstructionContinue nv \<Longrightarrow>
 vctx_memory v = vctx_memory nv"
apply(auto simp:jump_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "vctx_next_instruction
   (v\<lparr>vctx_stack := tl (vctx_stack v), vctx_pc := unat (hd (vctx_stack v))\<rparr>) c")
apply(auto)
apply(cases "get_some (vctx_next_instruction
   (v\<lparr>vctx_stack := tl (vctx_stack v), vctx_pc := unat (hd (vctx_stack v))\<rparr>) c)")
apply(auto)
apply(cases "get_pc (vctx_next_instruction
   (v\<lparr>vctx_stack := tl (vctx_stack v), vctx_pc := unat (hd (vctx_stack v))\<rparr>) c)")
apply(auto)
done

theorem lemma_jump_foo [simp] :
"jump (v\<lparr>vctx_stack:=x\<rparr>) c = InstructionContinue nv \<Longrightarrow>
 vctx_memory v = vctx_memory nv"
apply(auto simp:jump_def)
apply(cases "x")
apply(auto)
apply(cases "vctx_next_instruction
   (v\<lparr>vctx_stack := tl x, vctx_pc := unat (hd x)\<rparr>) c")
apply(auto)
apply(cases "get_some (vctx_next_instruction
   (v\<lparr>vctx_stack := tl x, vctx_pc := unat (hd x)\<rparr>) c)")
apply(auto)
apply(cases "get_pc (vctx_next_instruction
   (v\<lparr>vctx_stack := tl x, vctx_pc := unat (hd x)\<rparr>) c)")
apply(auto)
done

theorem lemma_pop_stack [simp] :
"vctx_memory v = vctx_memory (vctx_pop_stack n v)"
apply(auto)
done

theorem lemma_update_storage [simp] :
"vctx_memory v = vctx_memory (vctx_update_storage a aa v)"
apply(auto)
done

lemma lemma_subtract : 
  "subtract_gas x (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   vctx_memory v = vctx_memory nv"
apply auto
done

declare instruction_aux_def [simp]

theorem no_modify_memory_aux :
  "inst \<noteq> Memory MSTORE \<Longrightarrow>
   inst \<noteq> Memory MSTORE8 \<Longrightarrow>
   inst \<noteq> Memory CALLDATACOPY \<Longrightarrow>
   inst \<noteq> Memory CODECOPY \<Longrightarrow>
   inst \<noteq> Memory EXTCODECOPY \<Longrightarrow>
   instruction_aux v c inst = InstructionContinue nv \<Longrightarrow>
   vctx_memory v = vctx_memory nv"
apply(cases inst)

apply(auto)
(* apply(auto simp:lemma_subtract) *)

apply(cases "get_bits (Some inst)",
   auto simp:lemma_stack_2_1_op lemma_stack_3_1_op lemma_stack_1_1_op)
apply(cases "get_sarith (Some inst)",
   auto simp:lemma_stack_2_1_op lemma_stack_3_1_op lemma_stack_1_1_op)
apply(cases "get_arith (Some inst)",
   auto simp:lemma_stack_2_1_op lemma_stack_3_1_op lemma_stack_1_1_op)

apply(auto simp:sha3_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "get_info (Some inst)")
apply(auto simp:lemma_stack_2_1_op lemma_stack_3_1_op lemma_stack_1_1_op
  split:option.split)
apply(cases "index (vctx_stack v)
              (nat (uint (get_dup (Some inst))))")
apply(auto split:option.split)
apply(cases "get_memory (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto split:option.split)
apply(cases "get_storage (Some inst)")
apply(auto simp:lemma_stack_1_1_op)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto simp:strict_if_def split:option.split)
apply(cases "get_pc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto simp:strict_if_def split:option.split)
apply(cases "hd (tl (vctx_stack v)) = 0")
apply(auto)
apply(cases "get_stack inst")
apply(auto simp:lemma_stack_1_1_op)
apply(cases "vctx_stack v")
apply(auto split:option.split)
apply(cases "index (vctx_stack v)
              (nat (uint (get_swap (Some inst))))")
apply(auto split:option.split)
apply(cases "index (vctx_stack v) (Suc (nat (uint (get_swap (Some inst)))))")
apply(auto split:option.split)
apply(cases "index (vctx_stack v) 0")
apply(auto split:option.split)

apply(cases "get_log (Some inst)")
apply(auto simp:log_def split:option.split)
apply(cases "get_misc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(simp)
apply(cases "vctx_balance v (cctx_this c) < hd (vctx_stack v)")
apply(auto)
apply(cases "vctx_stack v")
apply(simp)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(cases "tl (tl (vctx_stack v))")
apply(simp)
apply(cases "tl (tl (tl (vctx_stack v)))")
apply(simp)
apply(cases "tl (tl (tl (tl (vctx_stack v))))")
apply(simp)
apply(cases "tl (tl (tl (tl (tl (vctx_stack v)))))")
apply(simp)
apply(cases "tl (tl (tl (tl (tl (tl (vctx_stack v))))))")
apply(auto)
apply(cases "vctx_balance v (cctx_this c) <
    hd (tl (tl (vctx_stack v)))")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
apply(cases "tl (tl (tl (vctx_stack v)))")
apply(auto)
apply(cases "tl (tl (tl (tl (vctx_stack v))))")
apply(auto)
apply(cases "tl (tl (tl (tl (tl (vctx_stack v)))))")
apply(auto)
apply(cases "tl (tl (tl (tl (tl (tl (vctx_stack v))))))")
apply(auto)
apply(cases "vctx_balance v (cctx_this c) <
    hd (tl (tl (vctx_stack v)))")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
apply(cases "tl (tl (tl (vctx_stack v)))")
apply(auto)
apply(cases "tl (tl (tl (tl (vctx_stack v))))")
apply(auto)
apply(cases "tl (tl (tl (tl (tl (vctx_stack v)))))")
apply(auto)
apply(cases "vctx_balance v (cctx_this c) <
    vctx_value_sent v")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
done

lemma no_modify_memory :
  "inst \<noteq> Memory MSTORE \<Longrightarrow>
   inst \<noteq> Memory MSTORE8 \<Longrightarrow>
   inst \<noteq> Memory CALLDATACOPY \<Longrightarrow>
   inst \<noteq> Memory CODECOPY \<Longrightarrow>
   inst \<noteq> Memory EXTCODECOPY \<Longrightarrow>
   instruction_sem v c inst = InstructionContinue nv \<Longrightarrow>
   vctx_memory v = vctx_memory nv"
apply(subst (asm) inst_gas)
apply(cases "instruction_aux v c inst")
defer
apply(simp)
apply(simp)
  by (metis lemma_subtract no_modify_memory_aux)

end

