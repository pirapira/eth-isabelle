theory "ToyExamplesBlocks"

imports "../Hoare/HoareTripleForBasicBlocks"
begin

lemmas evm_fun_simps = 
  stack_inst_code.simps inst_size_def inst_code.simps 

lemmas blocks_simps = build_blocks_def byteListInt_def find_block_def blocks_indexes_def build_basic_blocks_def
 aux_basic_block.simps add_address_def block_pt_def

lemma word_rcat_fixed_simps:
  fixes x::byte
  shows
 "(word_rcat (x#xs) :: w256) =  word_of_int (bin_rcat 8 (map uint (x#xs)))"
 "(word_rcat (x#xs) :: 160 word) =  word_of_int (bin_rcat 8 (map uint (x#xs)))"
  by (simp add: word_rcat_def)+

lemmas word_rcat_simps = word_rcat_fixed_simps bin_rcat_def bin_cat_def


lemmas pure_emp_simps = pure_def pure_sep emp_def emp_sep zero_set_def

lemma word_rcat_eq: "word_rcat [x] = x"
  by (simp add: word_rcat_def bin_rcat_def)

lemma pure_false_simps:
"(\<langle> False \<rangle> \<and>* R) = \<langle> False \<rangle>"
"(R \<and>* \<langle> False \<rangle>) = \<langle> False \<rangle>"
by (rule ext, simp add: pure_def sep_conj_def emp_def )+

context
notes if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add]
begin

(* Example with a Jumpi and a No block *)

definition ex1 where
"ex1 = build_blocks [ Stack (PUSH_N [1]), Stack (PUSH_N [8]), Pc JUMPI, Stack (PUSH_N [1]), Misc STOP, Pc JUMPDEST, Stack (PUSH_N [2]), Misc STOP]"

schematic_goal ex1_val:
 " ex1 = ?p"
 by(simp add: ex1_def  word_rcat_simps Let_def dropWhile.simps  blocks_simps next_i_def
  split:if_splits nat.splits option.splits )

lemmas strengthen_insts =
inst_strengthen_pre[OF inst_stack[OF inst_push_n]]
inst_strengthen_pre[OF inst_stack[OF inst_pop]]
inst_strengthen_pre[OF inst_stack[OF inst_calldataload]]
inst_strengthen_pre[OF inst_swap]
inst_strengthen_pre[OF inst_dup]
inst_strengthen_pre[OF inst_memory[OF inst_mstore]]
inst_strengthen_pre[OF inst_memory[OF inst_mload]]
inst_strengthen_pre[OF inst_storage[OF inst_sload]]
inst_strengthen_pre[OF inst_storage[OF inst_sstore]]
inst_strengthen_pre[OF inst_info[OF inst_callvalue]]
inst_strengthen_pre[OF inst_info[OF inst_caller]]
inst_strengthen_pre[OF inst_info[OF inst_calldatasize]]
inst_strengthen_pre[OF inst_pc[OF inst_jumpdest]]
inst_strengthen_pre[OF inst_pc[OF inst_instPC]]
inst_strengthen_pre[OF inst_misc[OF inst_stop]]
inst_strengthen_pre[OF inst_misc[OF inst_return_memory]]
inst_strengthen_pre[OF inst_misc[OF inst_return]]
inst_strengthen_pre[OF inst_misc[OF inst_suicide]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_mul]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_div]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_mod]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_add]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_sub]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_gt]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_eq]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_lt]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_addmod]]
inst_strengthen_pre[OF inst_arith[OF inst_arith_mulmod]]
inst_strengthen_pre[OF inst_arith[OF inst_iszero]]
inst_strengthen_pre[OF inst_bits[OF inst_bits_not]]
inst_strengthen_pre[OF inst_bits[OF inst_bits_and]]
inst_strengthen_pre[OF inst_bits[OF inst_bits_and]]
inst_strengthen_pre[OF inst_bits[OF inst_bits_or]]
inst_strengthen_pre[OF inst_bits[OF inst_bits_xor]]
inst_strengthen_pre[OF inst_bits[OF inst_bits_byte]]
inst_strengthen_pre[OF inst_unknown]


lemma instantiate_emp:
"P sd \<Longrightarrow> (P \<and>* emp) sd"
apply(sep_simp simp: emp_sep)
done

method sep_imp_solve =
clarsimp;
(rule conjI),
  (clarsimp simp add: word_rcat_def)?,
  (sep_cancel)+,
  (erule instantiate_emp)?,
(simp)

method sep_imp_solve_cancel_simp =
clarsimp?;
(rule conjI),
  (clarsimp simp add: word_rcat_def)?,
  (sep_cancel, simp?)+,
  (erule instantiate_emp)?,
(simp)

method triple_seq_vcg =
  (rule seq_inst; ((rule strengthen_insts) | triple_seq_vcg)?) |
  rule seq_empty

method triple_jumpi_vcg =
 ((rule blocks_jumpi; (rule refl)?),
  triple_seq_vcg, (sep_imp_solve_cancel_simp|sep_imp_solve)+); simp add: bin_rcat_def

method triple_jump_vcg =
 ((rule blocks_jump; (rule refl)?),
  triple_seq_vcg, sep_imp_solve+); simp add: bin_rcat_def


method triple_no_vcg =
 (rule blocks_no; triple_seq_vcg, sep_imp_solve+),
 simp add: word_rcat_simps, sep_cancel+

method triple_next_vcg =
 ((rule blocks_next; (rule refl)?),
  triple_seq_vcg, sep_imp_solve+); simp add: bin_rcat_def;
  (simp add: word_rcat_simps; sep_cancel+)?


method triple_vcg =
 (triple_jumpi_vcg |
  triple_jump_vcg |
  triple_no_vcg |
  triple_next_vcg |
  rule blocks_false_pre)+

thm triple_blocks.intros
(* For a jumpif that can be solved statically, it works *)
lemma
 "\<exists>rest. triple_blocks net ex1
(continuing ** stack_height 0 ** program_counter 0 ** gas_pred 1000 ** memory_usage 0)
(0,the (block_lookup ex1 0))
(stack 0 (word_rcat [2::byte]) ** rest)"
 apply(unfold ex1_val)
 apply (simp)
 apply(rule exI)
  apply triple_vcg
done

(* Same example but we put an unknown value and an if in the post condition *)
(* For a jumpif where we don't know at all which branch to follow, it works *)
definition ex2 where
"ex2 x = build_blocks [ Stack (PUSH_N [x]), Stack (PUSH_N [8]), Pc JUMPI, Stack (PUSH_N [1]), Misc STOP, Pc JUMPDEST, Stack (PUSH_N [2]), Misc STOP]"

schematic_goal ex2_val:
 " ex2 x = ?p"
 by(simp add: ex2_def  word_rcat_simps Let_def dropWhile.simps blocks_simps next_i_def
  split:if_splits nat.splits option.splits )

lemma
 " \<exists>rest0 restn0. triple_blocks net (ex2 cond)
(continuing ** stack_height 0 ** program_counter 0 ** gas_pred 1000 ** memory_usage 0)
(0, the (block_lookup (ex2 cond) 0))
(if word_rcat [cond] = (0::256 word) then stack 0 (word_rcat [1::byte]) ** restn0 else stack 0 (word_rcat [2::byte]) ** rest0)
"
 apply(unfold ex2_val)
 apply (simp split: if_splits, rule conjI; clarsimp)
  apply(rule exI, triple_vcg)
 apply(rule exI, triple_vcg)
 apply (clarsimp simp: word_rcat_simps bintrunc_def)
done

(* Same example as the previous one but with the unknown value as a precondition *)

lemma
 "\<exists>rest. triple_blocks net (ex2 cond)
(continuing ** stack_height 0 ** program_counter 0 ** gas_pred 1000 ** memory_usage 0 **
 \<langle> (word_rcat [cond] \<noteq> (0::256 word)) \<rangle>)
(0,the (block_lookup (ex2 cond) 0))
(stack 0 (word_rcat [2::byte]) ** rest )
"
apply(unfold ex2_val)
apply (simp)
apply(rule exI)
apply(triple_vcg)
done

(* Example with a Jump and a Next block*)

definition ex3 where
"ex3 = build_blocks [ Stack (PUSH_N [1]), Stack (PUSH_N [5]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [2]), Pc JUMPDEST, Misc STOP]"

schematic_goal ex3_val:
 " ex3  = ?p"
 by(simp add: ex3_def  word_rcat_simps Let_def dropWhile.simps blocks_simps next_i_def
  split:if_splits nat.splits option.splits )

lemma
 "\<exists>rest. triple_blocks net ex3
(continuing ** stack_height 0 ** program_counter 0 ** gas_pred 1000 ** memory_usage 0)
(0, the (block_lookup ex3 0))
(stack 0 (word_rcat [1::byte]) ** stack_height (Suc (Suc 0)) ** stack 1 (word_rcat [2::byte]) ** rest)
"
apply(unfold ex3_val)
apply (simp)
apply(rule exI)
apply(triple_vcg)
done
end

end
