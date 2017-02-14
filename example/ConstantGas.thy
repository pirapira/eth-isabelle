theory "ConstantGas" 

imports 
   "InstructionAux" "../ProgramInAvl"

begin

declare stack_1_1_op_def [simp del]
declare jump_def [simp del]

lemma lemma_stack_2_1_op :
"stack_2_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_gas v = vctx_gas nv"
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

lemma lemma_sstore :
"sstore v c = InstructionContinue nv \<Longrightarrow>
 vctx_gas v = vctx_gas nv"
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

lemma lemma_stack_3_1_op :
"stack_3_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_gas v = vctx_gas nv"
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(cases "tl (tl (vctx_stack v))")
apply(simp)
apply(auto)
done

lemma lemma_stack_1_1_op :
"stack_1_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_gas v = vctx_gas nv"
apply(auto simp:stack_1_1_op_def)
apply(cases "vctx_stack v")
apply(auto split:option.split)
done

theorem lemma_jump [simp] :
"jump v c = InstructionContinue nv \<Longrightarrow>
 vctx_gas v = vctx_gas nv"
apply(auto simp:jump_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "program_content (cctx_program c)
                   (uint (hd (vctx_stack v)))")
apply auto
apply(cases "get_some (program_content (cctx_program c)
                   (uint (hd (vctx_stack v))))")
apply auto
apply(cases "get_pc (program_content (cctx_program c)
                   (uint (hd (vctx_stack v))))")
apply auto
done

theorem lemma_jump_foo [simp] :
"jump (v\<lparr>vctx_stack := a # lista\<rparr>) c = InstructionContinue nv \<Longrightarrow>
 vctx_gas v = vctx_gas nv"
apply(auto simp:jump_def)
apply(cases "program_content (cctx_program c)
                   (uint a)")
apply auto
apply(cases "get_some (program_content (cctx_program c)
                   (uint a))")
apply auto
apply(cases "get_pc (program_content (cctx_program c)
                   (uint a))")
apply auto
done

declare cut_memory.simps [simp del]

theorem no_modify_gas :
  "instruction_aux v c inst = InstructionContinue nv \<Longrightarrow>
   vctx_gas v = vctx_gas nv"
apply(cases inst)
apply(auto simp:instruction_aux_def)
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
apply(simp)
apply(simp)
apply(auto split:option.split)
apply(cases "get_info (Some inst)")
apply(auto simp:lemma_stack_2_1_op lemma_stack_3_1_op lemma_stack_1_1_op)
apply(cases "index (vctx_stack v) (nat (uint (get_dup (Some inst))))")
apply(auto split:option.split)
apply(cases "get_memory (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
apply(cases "tl (tl (tl (vctx_stack v)))")
apply(auto split:option.split)
apply(cases "get_storage (Some inst)")
apply(auto simp:lemma_stack_2_1_op lemma_stack_3_1_op
   lemma_stack_1_1_op lemma_sstore)
apply(cases "get_pc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto simp:strict_if_def split:option.split)
apply(cases "hd (tl (vctx_stack v)) = 0")
apply(auto simp:blockedInstructionContinue_def split:option.split)

apply(cases "get_stack inst")
apply(auto simp:lemma_stack_2_1_op lemma_stack_3_1_op lemma_stack_1_1_op)
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
apply(auto)
apply(cases "get_misc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
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

lemma new_memory :
  "0 \<le> vctx_memory_usage v \<Longrightarrow> 0 \<le> new_memory_consumption inst v"
apply (cases inst)
apply(auto)
apply (cases "get_arith (Some inst)")
apply(auto)
apply (cases "get_memory (Some inst)")
apply(auto)
apply (cases "get_misc (Some inst)")
apply(auto)
done

lemma new_memory_cons :
  "vctx_memory_usage v \<le> new_memory_consumption inst v"
apply (cases inst)
apply(auto)
apply (cases "get_arith (Some inst)")
apply(auto)
apply (cases "get_memory (Some inst)")
apply(auto)
apply (cases "get_misc (Some inst)")
apply(auto)
done

fun no_spend_gas :: "inst \<Rightarrow> bool" where
"no_spend_gas (Unknown _) = True"
| "no_spend_gas (Misc STOP) = True"
| "no_spend_gas (Misc RETURN) = True"
| "no_spend_gas (Misc SUICIDE) = True"
| "no_spend_gas _ = False"

lemma third_component_stop :
  "no_spend_gas inst \<Longrightarrow>
  thirdComponentOfC inst s0 s1 s2 s3 recipient_empty orig new_val remaining_gas blocknumber \<ge> 0"
apply(cases inst)
apply (auto simp:thirdComponentOfC.simps)
apply(cases "get_misc (Some inst)")
apply (auto simp:thirdComponentOfC.simps Csuicide_def)
done

lemma uint_pos : "uint x \<ge> 0"
apply auto
done

lemma pos_div : "(x::int) \<ge> 0 \<Longrightarrow> x div 32 \<ge> 0"
apply arith
done

lemma simple_mem : "0 < 3 + 3 * ((uint s2 + 31) div 32)"
proof -
have "uint s2 \<ge> 0" by auto
then have "uint s2 + (31::int) \<ge> 0" by arith
then have "((uint s2 + 31) div 32) \<ge> 0" by arith
then show "0 < 3 + 3 * ((uint s2 + 31) div 32)" by arith
qed

lemma simple_mem2 : "0 < 700 + 3 * ((uint s2 + 31) div 32)"
proof -
have "uint s2 \<ge> 0" by auto
then have "uint s2 + (31::int) \<ge> 0" by arith
then have "((uint s2 + 31) div 32) \<ge> 0" by arith
then show "0 < 700 + 3 * ((uint s2 + 31) div 32)" by arith
qed

lemma simple_mem3 : "0 < 20 + 3 * ((uint s2 + 31) div 32)"
proof -
have "uint s2 \<ge> 0" by auto
then have "uint s2 + (31::int) \<ge> 0" by arith
then have "((uint s2 + 31) div 32) \<ge> 0" by arith
then show "0 < 20 + 3 * ((uint s2 + 31) div 32)" by arith
qed

lemma simple : "(x::int) \<ge> 0 \<Longrightarrow> 0 < 3 + 3 * x"
apply arith
done

lemma arith_log : assumes a: "0 < x" shows "0 < x + 8 * uint y"
proof -
have "uint y \<ge> 0" by auto
then have b: "uint y * 8 \<ge> 0" by arith
then show "0 < x + 8 * uint y" using a by arith
qed

lemma lemma_gascap :
   "Cgascap s0 s1 recipient_empty
         remaining_gas blocknumber \<ge> 0"
apply(auto simp:Cgascap_def)
done

lemma misc_calc :
"0 < x \<Longrightarrow> 0 < Cgascap s0 s1 recipient_empty
         remaining_gas blocknumber + x"
using lemma_gascap
  by (simp add: add.commute add_pos_nonneg)

lemma sha3_calc : "0 < 30 + 6 * ((uint x + 31) div 32)"
proof -
  have "uint x \<ge> 0" by auto
  then have "((uint x + 31) div 32) \<ge> 0" by arith
  then show ?thesis by arith
qed

fun log256floor_nat  :: " int \<Rightarrow> nat "  where 
     " log256floor_nat x = (
  if x \<le>( 255 :: int) then( 0 :: nat )
  else( 1 :: nat) + log256floor_nat (x div( 256 :: int)))" 

declare log256floor.simps [simp del]
declare log256floor_nat.simps [simp del]

lemma abs_stuff : "abs (x div 256) \<le> abs (x::int)"
apply arith
done

lemma log_nat : "log256floor x = int (log256floor_nat x)"
(* apply(cases " x \<le>( 255 :: int)") *)
apply(induction x rule:log256floor.induct)
apply(cases " x \<le>( 255 :: int)")
apply(subst log256floor_nat.simps)
apply(subst log256floor.simps)
apply(simp)
apply(subst log256floor_nat.simps)
apply(subst log256floor.simps)
apply(simp)
done

lemma log_floor_calc : "log256floor x \<ge> 0"
apply(auto simp:log_nat)
done

lemma exp_case : assumes a:"inst = Arith x4" and
       b:"get_arith (Some inst) = EXP" shows
       "0 < thirdComponentOfC (Arith x4)
            s0 s1 s2 s3 recipient_empty
            orig new_val remaining_gas
            blocknumber"
proof -
from a and b have d: "x4 = EXP" by auto
have c: "thirdComponentOfC (Arith EXP)
            s0 s1 s2 s3 recipient_empty
            orig new_val remaining_gas
            blocknumber =
 ( Gexp + (if s1 =((word_of_int 0) ::  256 word) then
 ( 0 :: int) else Gexpbyte * (( 1 :: int) + log256floor (Word.uint s1))))"
by auto
from log_floor_calc have "0 \<le> Gexpbyte * (( 1 :: int) + log256floor (Word.uint s1))" by auto
then have "(if s1 =((word_of_int 0) ::  256 word) then
 ( 0 :: int) else Gexpbyte * (( 1 :: int) + log256floor (Word.uint s1)))
 \<ge> 0" by auto
then have " Gexp + (if s1 =((word_of_int 0) ::  256 word) then
 ( 0 :: int) else Gexpbyte * (( 1 :: int) + log256floor (Word.uint s1)))
 > 0" by auto
then show ?thesis using c and d by auto
qed

lemma exp_calc : "0 < 60 + 50 * log256floor (uint s1)"
proof -
have "log256floor (uint s1) \<ge> 0" by (auto simp:log_floor_calc)
then show ?thesis by arith
qed

lemma third_component :
  "\<not> no_spend_gas inst \<Longrightarrow>
   thirdComponentOfC inst s0 s1 s2 s3 recipient_empty orig new_val remaining_gas blocknumber > 0"
apply (cases inst)
apply (auto simp:thirdComponentOfC.simps)
apply (cases "get_bits (Some inst)")
apply (auto simp:thirdComponentOfC.simps)
apply (cases "get_sarith (Some inst)")
apply (auto simp:thirdComponentOfC.simps)
defer
apply (cases "get_info (Some inst)")
apply (auto simp:thirdComponentOfC.simps)
apply (cases "get_memory (Some inst)")
apply (auto simp:thirdComponentOfC.simps)
apply(auto simp:simple_mem simple_mem2 simple_mem3)
apply (cases "get_storage (Some inst)")
apply (auto simp:thirdComponentOfC.simps)
apply(simp add:Csstore_def)
apply (cases "get_pc (Some inst)")
apply (auto simp:thirdComponentOfC.simps)
apply (cases "get_stack inst")
apply (auto simp:thirdComponentOfC.simps)
apply (cases "get_log (Some inst)")
apply (auto simp:thirdComponentOfC.simps arith_log)
apply (cases "get_misc (Some inst)")
apply (auto simp:thirdComponentOfC.simps lemma_gascap
  Cxfer_def Cnew_def misc_calc)
apply (cases "get_arith (Some inst)")
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
defer
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply (simp add:thirdComponentOfC.simps)
apply(simp add:sha3_calc)
apply (auto simp:exp_calc)
done

lemma foo : assumes a:"0 \<le> vctx_memory_usage v"
shows "3 * new_memory_consumption inst v +
         new_memory_consumption inst v *
         new_memory_consumption inst
          v div
         512 \<ge>
         3 * vctx_memory_usage v +
          vctx_memory_usage v *
          vctx_memory_usage v div
          512"
proof -
from new_memory_cons and a have b: "new_memory_consumption inst v \<ge> 0"
  by smt
  
from new_memory_cons and a have
 "new_memory_consumption inst v *
         new_memory_consumption inst v \<ge>
   vctx_memory_usage v * vctx_memory_usage v"
  by (simp add: mult_mono')
then have
 "new_memory_consumption inst v *
         new_memory_consumption inst v div 512 \<ge>
   vctx_memory_usage v * vctx_memory_usage v div 512"
  by (simp add: zdiv_mono1)
then show ?thesis using a and b
  by (smt new_memory_cons) 
qed

lemma lemma1 :
  "0 \<le> vctx_memory_usage v \<Longrightarrow> 0 \<le> x \<Longrightarrow>
  0 \<le> 3 *
         new_memory_consumption inst v +
         new_memory_consumption inst v *
         new_memory_consumption inst
          v div
         512 -
         (3 * vctx_memory_usage v +
          vctx_memory_usage v *
          vctx_memory_usage v div
          512) + x"
using foo apply auto
done

lemma lemma2 :
  "0 \<le> vctx_memory_usage v \<Longrightarrow> 0 < x \<Longrightarrow>
  0 < 3 *
         new_memory_consumption inst v +
         new_memory_consumption inst v *
         new_memory_consumption inst
          v div
         512 -
         (3 * vctx_memory_usage v +
          vctx_memory_usage v *
          vctx_memory_usage v div
          512) + x"
using foo
  by smt

declare vctx_next_instruction_default_def [simp del]

lemma third_component2 :
  "\<not> no_spend_gas inst \<Longrightarrow>
   thirdComponentOfC inst s0 s1 s2 s3 recipient_empty orig new_val remaining_gas blocknumber \<ge> 0"
using third_component
  by (simp add: dual_order.order_iff_strict)

lemma lemma_predict : 
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   predict_gas inst v c \<ge> 0"
apply (cases "no_spend_gas (vctx_next_instruction_default v c)")
apply (auto simp:third_component_stop lemma1)
apply (rule lemma1)
apply(auto)
using third_component2
apply(auto)
done

lemma lemma_predict2 : 
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   \<not>no_spend_gas (vctx_next_instruction_default v c) \<Longrightarrow>
   predict_gas inst v c > 0"
apply (auto simp:third_component lemma2)
done

declare predict_gas_def [simp del]

lemma lemma_next :
"vctx_next_instruction_default (v\<lparr>vctx_gas := x \<rparr>) c =
  vctx_next_instruction_default v c"
apply(auto simp:vctx_next_instruction_default_def)
done

theorem gas_smaller :
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   instruction_sem v c inst = InstructionContinue nv \<Longrightarrow>
   \<not>no_spend_gas (vctx_next_instruction_default v c) \<Longrightarrow>
   vctx_gas nv < vctx_gas v"
apply(subst (asm) inst_gas)
apply(cases "instruction_aux v c inst")
defer
apply(simp)
apply(simp)
apply(auto simp:no_modify_gas lemma_next)
apply(auto simp:lemma_predict2)
done

theorem gas_maybe_smaller :
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   instruction_sem v c inst = InstructionContinue nv \<Longrightarrow>
   no_spend_gas (vctx_next_instruction_default v c) \<Longrightarrow>
   vctx_gas nv \<le> vctx_gas v"
apply(subst (asm) inst_gas)
apply(cases "instruction_aux v c inst")
defer
apply(simp)
apply(simp)
apply(auto simp:no_modify_gas lemma_next)
apply(auto simp:lemma_predict)
done

(* memory usage grows *)

lemma lemma_stack_2_1_op2 :
"stack_2_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_memory_usage v = vctx_memory_usage nv"
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

lemma lemma_sstore2 :
"sstore v c = InstructionContinue nv \<Longrightarrow>
 vctx_memory_usage v = vctx_memory_usage nv"
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
done

lemma lemma_stack_3_1_op2 :
"stack_3_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_memory_usage v = vctx_memory_usage nv"
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(cases "tl (tl (vctx_stack v))")
apply(simp)
apply(auto)
done

lemma lemma_stack_1_1_op2 :
"stack_1_1_op v c f = InstructionContinue nv \<Longrightarrow>
 vctx_memory_usage v = vctx_memory_usage nv"
apply(auto simp:stack_1_1_op_def)
apply(cases "vctx_stack v")
apply(auto split:option.split)
done

theorem lemma_jump2 [simp] :
"jump v c = InstructionContinue nv \<Longrightarrow>
 vctx_memory_usage v = vctx_memory_usage nv"
apply(auto simp:jump_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "program_content (cctx_program c)
                   (uint (hd (vctx_stack v)))")
apply auto
apply(cases "get_some (program_content (cctx_program c)
                   (uint (hd (vctx_stack v))))")
apply auto
apply(cases "get_pc (program_content (cctx_program c)
                   (uint (hd (vctx_stack v))))")
apply auto
done

theorem lemma_jump_foo2 [simp] :
"jump (v\<lparr>vctx_stack := a # lista\<rparr>) c = InstructionContinue nv \<Longrightarrow>
 vctx_memory_usage v = vctx_memory_usage nv"
apply(auto simp:jump_def)
apply(cases "program_content (cctx_program c)
                   (uint a)")
apply auto
apply(cases "get_some (program_content (cctx_program c)
                   (uint a))")
apply auto
apply(cases "get_pc (program_content (cctx_program c)
                   (uint a))")
apply auto
done

theorem memory_usage_grows :
  "instruction_aux v c inst = InstructionContinue nv \<Longrightarrow>
   vctx_memory_usage v \<le> vctx_memory_usage nv"
apply(cases inst)
apply(auto simp:instruction_aux_def)
apply(cases "get_bits (Some inst)",
   auto simp:lemma_stack_2_1_op2 lemma_stack_3_1_op2 lemma_stack_1_1_op2)
apply(cases "get_sarith (Some inst)",
   auto simp:lemma_stack_2_1_op2 lemma_stack_3_1_op2 lemma_stack_1_1_op2)
apply(cases "get_arith (Some inst)",
   auto simp:lemma_stack_2_1_op2 lemma_stack_3_1_op2 lemma_stack_1_1_op2)

apply(auto simp:sha3_def)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
apply(cases "get_info (Some inst)")
apply(auto simp:lemma_stack_2_1_op2 lemma_stack_3_1_op2 lemma_stack_1_1_op2)
apply(cases "index (vctx_stack v) (nat (uint (get_dup (Some inst))))")
apply(auto split:option.split)
apply(cases "get_memory (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto split:option.split)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
apply(cases "tl (tl (tl (vctx_stack v)))")
apply(auto split:option.split)
apply(cases "get_storage (Some inst)")
apply(auto simp:lemma_stack_2_1_op2 lemma_stack_3_1_op2
   lemma_stack_1_1_op2 lemma_sstore2)
apply(cases "get_pc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto simp:strict_if_def split:option.split)
apply(cases "hd (tl (vctx_stack v)) = 0")
apply(auto simp:blockedInstructionContinue_def split:option.split)

apply(cases "get_stack inst")
apply(auto simp:lemma_stack_2_1_op2 lemma_stack_3_1_op2 lemma_stack_1_1_op2)
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
apply(auto)
apply(cases "get_misc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "tl (tl (vctx_stack v))")
apply(auto)
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

declare check_annotations_def [simp del]
declare vctx_next_instruction_def [simp del]

lemma gas_left :
  "program_step c (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   vctx_gas nv \<ge> 0"
apply(auto simp:program_step_def)
apply(subst (asm) inst_gas)


apply(cases "\<not> check_annotations v c")
apply(auto)
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c (vctx_stack v)
  (get_some (vctx_next_instruction v c))")
apply(auto)

apply(cases "instruction_aux v c (get_some (vctx_next_instruction v c))")

apply(auto simp:no_modify_gas subtract_gas.simps)
apply(auto simp:check_resources_def)
using lemma_predict
  by (simp add: no_modify_gas)

lemma iter_reorder :
   "program_iter n c (program_step c v) =
    program_step c (program_iter n c v)"
apply(induction n arbitrary:v)
apply(auto)
done

lemma iter_gas_left :
  "vctx_gas v \<ge> 0 \<Longrightarrow>
   program_iter n c (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   vctx_gas nv \<ge> 0"
apply(cases n)
apply(auto simp:iter_reorder)
using gas_left and  program_step_continue
  by metis

declare instruction_sem_def [simp del]

lemma no_spend_gas_exit : 
   "instruction_aux v c inst = InstructionContinue nv \<Longrightarrow>
    no_spend_gas inst \<Longrightarrow>
    False"
apply(cases inst)
apply(auto simp:instruction_aux_def)
apply(cases "get_misc (Some inst)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
apply(cases "tl (vctx_stack v)")
apply(auto)
apply(cases "vctx_stack v")
apply(auto)
done

lemma step_gas_less :
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   program_step c (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   vctx_gas nv < vctx_gas v"
apply(auto simp:program_step_def)

apply(cases "\<not> check_annotations v c")
apply(auto)
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c (vctx_stack v)
  (get_some (vctx_next_instruction v c))")
apply(auto)

apply(cases "instruction_sem v c (get_some (vctx_next_instruction v c))")
apply(auto)
apply(cases "\<not>no_spend_gas (vctx_next_instruction_default v c)")
using gas_smaller apply blast
apply auto
apply(simp add:vctx_next_instruction_default_def)
apply(subst (asm) inst_gas)
apply(cases "instruction_aux v c (get_some (vctx_next_instruction v c))")
apply(auto)
using no_spend_gas_exit
apply blast
done

lemma step_memory_usage :
 "0 \<le> vctx_memory_usage v \<Longrightarrow>
  program_step c (InstructionContinue v) =
         InstructionContinue nv \<Longrightarrow>
  0 \<le> vctx_memory_usage nv"
apply(auto simp:program_step_def)
apply(subst (asm) inst_gas)


apply(cases "\<not> check_annotations v c")
apply(auto)
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c (vctx_stack v)
  (get_some (vctx_next_instruction v c))")
apply(auto)
apply(cases "instruction_aux v c (get_some (vctx_next_instruction v c))")
apply(auto)
  using memory_usage_grows by force

lemma iter_gas_less_aux :
  "(
           0 \<le> vctx_memory_usage v2 \<Longrightarrow>
           program_iter n c
            (InstructionContinue v2) =
           InstructionContinue nv \<Longrightarrow>
           vctx_gas nv + int n
           \<le> vctx_gas v2 \<and>
           0 \<le> vctx_memory_usage nv) \<Longrightarrow>
       0 \<le> vctx_memory_usage v \<Longrightarrow>
       program_iter n c
        (program_step c
          (InstructionContinue v)) =
       InstructionContinue nv \<Longrightarrow>
       program_step c (InstructionContinue v) =
         InstructionContinue v2 \<Longrightarrow>
       0 \<le> vctx_memory_usage nv"
using step_memory_usage
apply fastforce
done

fun get_continue :: "instruction_result \<Rightarrow> variable_ctx" where
"get_continue (InstructionContinue v) = v"

lemma get_continue_lemma :
"program_iter n c
        (program_step c
          (InstructionContinue v)) =
       InstructionContinue nv \<Longrightarrow>
       program_step c
        (InstructionContinue v) =
       InstructionContinue
        (get_continue
          (program_step c
            (InstructionContinue v)))"
apply(cases "program_step c
            (InstructionContinue v)")
apply(auto)
using program_iter_failure apply blast
using program_iter_env apply blast
done

lemma iter_gas_less_aux2 :
"(0 \<le> vctx_memory_usage v2 \<Longrightarrow>
             program_iter n c
              (InstructionContinue v2) =
             InstructionContinue nv \<Longrightarrow>
             vctx_gas nv + int n
             \<le> vctx_gas v2 \<and>
             0 \<le> vctx_memory_usage
                   nv) \<Longrightarrow>
       0 \<le> vctx_memory_usage v \<Longrightarrow>
       program_iter n c
        (program_step c
          (InstructionContinue v)) =
       InstructionContinue nv \<Longrightarrow>
      program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
       vctx_gas nv  + (1 + int n) \<le> vctx_gas v"
using step_gas_less
  by (smt step_memory_usage)

lemma iter_gas_less :
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   program_iter n c (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   (vctx_gas nv + n \<le> vctx_gas v \<and> 0 \<le> vctx_memory_usage nv)"
apply(induction n arbitrary:v)
apply(simp)
apply(auto)
defer

apply(rule_tac v=v and n=n and ?v2.0 = "get_continue (program_step c
          (InstructionContinue v))" in iter_gas_less_aux)
apply(auto)
using get_continue_lemma apply blast

apply(rule_tac v=v and n=n and ?v2.0 = "get_continue (program_step c
          (InstructionContinue v))" in iter_gas_less_aux2)
apply(auto)
using get_continue_lemma apply blast
done

lemma gas_will_run_out_aux :
  assumes a:"0 \<le> vctx_memory_usage v" and
   b:"vctx_gas v \<ge> 0" and
   c:"program_iter (nat (vctx_gas v)+1) c (InstructionContinue v) = InstructionContinue nv"
   shows "False"
proof -
   from iter_gas_less and a and c
   have "vctx_gas nv  + (nat (vctx_gas v)+1) \<le> vctx_gas v" by blast
   then have "vctx_gas nv < 0"
     by linarith
   then show False
     by (smt assms(3) b iter_gas_left)  
qed

lemma gas_will_run_out :
  "0 \<le> vctx_memory_usage v \<Longrightarrow>
   vctx_gas v \<ge> 0 \<Longrightarrow>
   program_sem  stopper c (nat (vctx_gas v)+1) (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   False"
apply(subst (asm) program_iter_is_sem)
using gas_will_run_out_aux apply blast
done

end

