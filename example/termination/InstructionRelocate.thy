theory "InstructionRelocate" 

imports 
   "InstructionAux"

begin

declare instruction_failure_result_def [simp]
declare vctx_advance_pc_def [simp]

theorem lemma_stack_2_1_op [simp] :
"stack_2_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_next_instruction v c =
    vctx_next_instruction (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 \<Longrightarrow>
 stack_2_1_op (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 f =
    InstructionContinue (nv\<lparr>vctx_pc:=vctx_pc nv+x\<rparr>)"
apply(auto simp:stack_2_1_op_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

theorem lemma_stack_3_1_op [simp] :
"stack_3_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_next_instruction v c =
    vctx_next_instruction (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 \<Longrightarrow>
 stack_3_1_op (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 f =
    InstructionContinue (nv\<lparr>vctx_pc:=vctx_pc nv+x\<rparr>)"
apply(auto simp:stack_3_1_op_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto split:option.split)
done

theorem lemma_stack_1_1_op [simp] :
"stack_1_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_next_instruction v c =
    vctx_next_instruction (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 \<Longrightarrow>
 stack_1_1_op (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 f =
    InstructionContinue (nv\<lparr>vctx_pc:=vctx_pc nv+x\<rparr>)"
apply(auto simp:stack_1_1_op_def)
apply(cases "vctx_stack v")
apply(auto split:option.split)
done

theorem "lemma_next_ind" [simp]:
"vctx_next_instruction (v\<lparr>vctx_stack := list\<rparr>) c =
 vctx_next_instruction v c"
apply(auto simp:vctx_next_instruction_def)
done

theorem lemma_pop_stack [simp] :
"vctx_next_instruction (vctx_pop_stack n v) c =
vctx_next_instruction v c"
apply(auto simp:vctx_pop_stack_def)
done

theorem lemma_update_storage [simp] :
"vctx_pc (vctx_update_storage a aa v) = vctx_pc v"
apply(auto simp:vctx_update_storage_def)
done

theorem lemma_gas [simp] :
 "gas (v\<lparr>vctx_pc := vctx_pc v + x\<rparr>) = gas v"
apply(auto simp:gas_def)
done

theorem lemma_mstore [simp] :
"mstore v c = InstructionContinue nv \<Longrightarrow>
 vctx_next_instruction v c =
    vctx_next_instruction (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 \<Longrightarrow>
 mstore (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 =
    InstructionContinue (nv\<lparr>vctx_pc:=vctx_pc nv+x\<rparr>)"
apply(auto simp:mstore_def)
apply(cases "vctx_stack v")
apply(simp)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

theorem lemma_venv_memory [simp] :
  "vctx_memory (v\<lparr>vctx_pc := vctx_pc v + x\<rparr>) p =
   vctx_memory v p"
apply(auto)
done

theorem lemma_mem_update [simp] :
 "(\<lambda>p. if p = a then ucast aa
                  else vctx_memory
                        (v\<lparr>vctx_pc := vctx_pc v + x\<rparr>)
                        p) =
(\<lambda>p. if p = a then ucast aa
                  else vctx_memory v p)"
apply(auto)
done

theorem lemma_mstore8 [simp] :
"mstore8 v c = InstructionContinue nv \<Longrightarrow>
 vctx_next_instruction v c =
    vctx_next_instruction (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 \<Longrightarrow>
 mstore8 (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 =
    InstructionContinue (nv\<lparr>vctx_pc:=vctx_pc nv+x\<rparr>)"
apply(auto simp:mstore8_def)
apply(cases "vctx_stack v")
apply(simp)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(auto split:option.split)
done

theorem "lemma_lambda" [simp] :
"(\<lambda>xa. if xa = a then aa
                else vctx_storage (v\<lparr>vctx_pc := x\<rparr>) xa) = 
(\<lambda>x. if x = a then aa else vctx_storage v x)"
apply(auto)
done

theorem "lemma_update2" [simp] :
"vctx_update_storage a aa (v\<lparr>vctx_pc := x\<rparr>) =
 (vctx_update_storage a aa v) \<lparr>vctx_pc := x\<rparr>"
apply(auto simp:vctx_update_storage_def)
done

theorem lemma_venv_next_update [simp] :
"vctx_next_instruction
        (vctx_update_storage a aa v) c =
       vctx_next_instruction v c"
apply(auto simp:vctx_next_instruction_def)
done

theorem lemma_venv_next_update2 [simp] :
"vctx_next_instruction
        (vctx_update_storage a aa v
         \<lparr>vctx_pc := vctx_pc v + x\<rparr>) c =
 vctx_next_instruction (v\<lparr>vctx_pc := vctx_pc v + x \<rparr>) c"
apply(auto simp:vctx_next_instruction_def)
done

theorem lemma_cutdata [simp] :
"cut_data (v\<lparr>vctx_pc := vctx_pc v + x\<rparr>) = cut_data v"
apply(auto simp:cut_data_def)
done

theorem lemma_pop_s [simp] :
"vctx_pop_stack n (v\<lparr> vctx_pc := x \<rparr>) =
 (vctx_pop_stack n v) \<lparr> vctx_pc := x \<rparr>"
apply(auto simp:vctx_pop_stack_def)
done

theorem lemma_pop_stack_pc [simp] :
"vctx_pc (vctx_pop_stack n v) = vctx_pc v"
apply(auto simp:vctx_pop_stack_def)
done

theorem lemma_stack_default [simp] :
"vctx_stack_default n (v\<lparr>vctx_pc := x\<rparr>) =
 vctx_stack_default n v"
apply(auto simp:vctx_stack_default_def)
done

fun relocatable :: "inst \<Rightarrow> bool" where
   "relocatable (Pc _) = False"
|  "relocatable (Info _) = False"
|  "relocatable (Memory CODECOPY) = False"
|  "relocatable _ = True"

lemma lemma_create_log [simp] :
   "cctx_this c2 = cctx_this c1 \<Longrightarrow>
    create_log_entry n (v\<lparr>vctx_pc := x\<rparr>) c2 =
    create_log_entry n v c1"
apply(auto simp:create_log_entry_def)
apply(auto simp:vctx_returned_bytes_def)
apply(cases "vctx_stack v")
apply(auto)
done

theorem relocatable_inst :
  "relocatable inst \<Longrightarrow>
   instruction_aux v c inst = InstructionContinue nv \<Longrightarrow>
   vctx_next_instruction v c =
    vctx_next_instruction (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 \<Longrightarrow>
   cctx_this c2 = cctx_this c \<Longrightarrow>
   instruction_aux (v\<lparr>vctx_pc:=vctx_pc v+x\<rparr>) c2 inst =
    InstructionContinue (nv\<lparr>vctx_pc:=vctx_pc nv+x\<rparr>)"
apply(cases inst)
apply(auto simp:instruction_aux_def)

apply(cases "get_bits (Some inst)", auto)
apply(cases "get_sarith (Some inst)", auto)
apply(cases "get_arith (Some inst)", auto)

apply(auto simp:sha3_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
(*
apply(cases "get_info (Some inst)")
apply(auto split:option.split)
*)
apply(simp add:general_dup_def)
apply(cases "index (venv_stack v) (unat (get_dup (Some inst)))")
apply(auto split:option.split)
apply(cases "get_memory (Some inst)")
apply(auto simp:mload_def stack_0_1_op_def)
apply(cases "vctx_stack v")
apply(auto split:option.split)
apply(simp add:calldatacopy_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto split:option.split)
apply(simp add:extcodecopy_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
apply(cases "tl (tl (tl (vctx_stack v)))")
apply(auto split:option.split)
apply(cases "get_storage (Some inst)")
apply(auto)
apply(simp add:sstore_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto simp:strict_if_def vctx_next_instruction_def
   split:option.split)

apply(cases "get_stack inst")
apply(auto)
apply(simp add:pop_def)
apply(cases "vctx_stack v")
apply(auto simp:vctx_next_instruction_def stack_0_1_op_def split:option.split)
apply(simp add:swap_def)
apply(cases "list_swap (Suc (unat (get_swap (Some inst)))) (vctx_stack v)")
apply(auto simp:vctx_next_instruction_def split:option.split)
apply(cases "get_log (Some inst)")
apply(auto simp:log_def split:option.split)
apply(auto simp:vctx_next_instruction_def vctx_pop_stack_def
  split:option.split)
apply(cases "get_misc (Some inst)")
apply(auto)
apply(simp add:stop_def)
apply(simp add:create_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto simp:vctx_next_instruction_def split:option.split)
apply(cases "vctx_balance v (cctx_this c) < hd (vctx_stack v)")
apply(auto)
apply (meson instruction_result.simps(6))
apply(simp add:call_def)
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
apply(auto simp:strict_if_def vctx_next_instruction_def update_balance_def
 split:option.split)
apply(simp add:callcode_def)
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
apply(simp)
apply(cases "vctx_balance v (cctx_this c) <
    hd (tl (tl (vctx_stack v)))")
apply(auto simp:strict_if_def vctx_next_instruction_def update_balance_def
 split:option.split)
apply(simp add:delegatecall_def)
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
apply(simp)
apply(cases "vctx_balance v (cctx_this c) <
    vctx_value_sent v")
apply(auto simp:strict_if_def vctx_next_instruction_def update_balance_def
 split:option.split)
apply(simp add:ret_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(simp add:suicide_def)
apply(cases "vctx_stack v")
apply(auto)
done

end
