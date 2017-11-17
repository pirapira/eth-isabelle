theory Dispatcher

imports
  "../Parse"
  "../Hoare/HoareTripleForBasicBlocks"
  "./ToyExamplesBlocks"
  "../Word_Lib/Word_Lemmas_32"
begin

definition 
dispatch1_hash :: "32 word"
where
"dispatch1_hash == 0x3ecb5edf"

definition 
dispatch2_hash :: "32 word"
where
"dispatch2_hash == 0x8cd5b077"

lemmas blocks_simps = build_blocks_def byteListInt_def find_block_def blocks_indexes_def build_basic_blocks_def
 aux_basic_block.simps add_address_def block_pt_def

value "parse_bytecode ''90''"

value"(parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ecb5edf1460475780638cd5b07714607b575b600080fd5b3415605157600080fd5b6065600480803590602001909190505060a1565b6040518082815260200191505060405180910390f35b3415608557600080fd5b608b60ad565b6040518082815260200191505060405180910390f35b6000600190505b919050565b6000600290505b905600a165627a7a72305820c9cf1e9d83721f6f9afecea62b7e868d98502ee8556dcaf6abb24acb8bc0d9fb0029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Swap 0, Arith DIV, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Bits inst_AND, Dup 0,
  Stack (PUSH_N [0x3E, 0xCB, 0x5E, 0xDF]), Arith inst_EQ, Stack (PUSH_N [0x47]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [0x8C, 0xD5, 0xB0, 0x77]), Arith inst_EQ, Stack (PUSH_N [0x7B]), Pc JUMPI, Pc JUMPDEST,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [0x51]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0x65]), Stack (PUSH_N [4]), Dup 0, Dup 0, Stack CALLDATALOAD, Swap 0,
  Stack (PUSH_N [0x20]), Arith ADD, Swap 0, Swap 1, Swap 0, Stack POP, Stack POP, Stack (PUSH_N [0xA1]),
  Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Dup 2, Dup 1, Memory MSTORE,
  Stack (PUSH_N [0x20]), Arith ADD, Swap 1, Stack POP, Stack POP, Stack (PUSH_N [0x40]), Memory MLOAD,
  Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [0x85]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0x8B]), Stack (PUSH_N [0xAD]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0x40]), Memory MLOAD,
  Dup 0, Dup 2, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD, Swap 1, Stack POP, Stack POP,
  Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST,
  Stack (PUSH_N [0]), Stack (PUSH_N [1]), Swap 0, Stack POP, Pc JUMPDEST, Swap 1, Swap 0, Stack POP,
  Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]), Stack (PUSH_N [2]), Swap 0, Stack POP, Pc JUMPDEST, Swap 0,
  Pc JUMP, Misc STOP, Log LOG1, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3,
  Unknown 0xC9, Unknown 0xCF, Unknown 0x1E, Swap 0xD, Dup 3,
  Stack (PUSH_N
          [0x1F, 0x6F, 0x9A, 0xFE, 0xCE, 0xA6, 0x2B, 0x7E, 0x86, 0x8D, 0x98, 0x50, 0x2E, 0xE8, 0x55, 0x6D,
           0xCA, 0xF6, 0xAB]),
  Unknown 0xB2, Unknown 0x4A, Unknown 0xCB, Dup 0xB, Unknown 0xC0, Unknown 0xD9, Unknown 0xFB, Misc STOP,
  Unknown 0x29]"

lemma
 "parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ecb5edf1460475780638cd5b07714607b575b600080fd5b3415605157600080fd5b6065600480803590602001909190505060a1565b6040518082815260200191505060405180910390f35b3415608557600080fd5b608b60ad565b6040518082815260200191505060405180910390f35b6000600190505b919050565b6000600290505b905600a165627a7a72305820c9cf1e9d83721f6f9afecea62b7e868d98502ee8556dcaf6abb24acb8bc0d9fb0029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition blocks_ex where
"blocks_ex == build_blocks insts_ex"

schematic_goal blocks_ex_val:
 " blocks_ex  = ?p"
 by(simp add: ex3_def insts_ex_def  word_rcat_simps Let_def dropWhile.simps blocks_simps next_i_def
  split:if_splits nat.splits option.splits )

context
notes if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add] iszero_stack_def[simp add]
begin

lemma stack_height_not_stack:
"stack n m s \<Longrightarrow> \<not> stack_height h s"
by(simp add: stack_height_def stack_def)

lemma memory_elm_not_stack:
"stack n m s \<Longrightarrow> \<not> memory8 h d s"
by(simp add: memory8_def stack_def)

lemma memory_range_not_stack:
"stack n m s \<Longrightarrow> \<not> memory_range h d s"
apply(induction d arbitrary: h s; simp add: stack_def)
apply(simp add: memory8_sep)
done

lemma memory_not_stack:
"stack n m s \<Longrightarrow> \<not> memory h d s"
by(simp add: memory_def stack_def memory_range_not_stack)

lemma gas_pred_not_stack:
"stack n m s \<Longrightarrow> \<not> gas_pred h s"
by(simp add: gas_pred_def stack_def)

lemma continuing_not_stack:
"stack n m s \<Longrightarrow> \<not> continuing s"
by(simp add: continuing_def stack_def)

lemma sent_data_not_stack:
"stack n m s \<Longrightarrow> \<not> sent_data h s"
by(simp add: sent_data_def stack_def)

lemma sent_value_not_stack:
"stack n m s \<Longrightarrow> \<not> sent_value h s"
by(simp add: sent_value_def stack_def)

lemma memory_usage_not_stack:
"stack n m s \<Longrightarrow> \<not> memory_usage h s"
by(simp add: memory_usage_def stack_def)

lemma not_continuing_not_stack:
"stack n m s \<Longrightarrow> \<not> not_continuing s"
by(simp add: not_continuing_def stack_def)

lemma program_counter_not_stack:
"stack n m s \<Longrightarrow> \<not> program_counter p s"
by(simp add: program_counter_def stack_def)

lemma action_not_stack:
"stack n m s \<Longrightarrow> \<not> action a s"
by(simp add: action_def stack_def)

lemmas not_stack =
action_not_stack
program_counter_not_stack
not_continuing_not_stack
memory_usage_not_stack
sent_value_not_stack
sent_data_not_stack
continuing_not_stack
gas_pred_not_stack
memory_not_stack
memory_range_not_stack
stack_height_not_stack
memory_elm_not_stack

lemma stack_height_first:
"(a \<and>* stack_height h \<and>* b) = (stack_height h \<and>* a \<and>* b)"
by(rule sep.mult.left_commute)

lemma stack_first:
"\<forall>n m s. stack n m s \<longrightarrow> \<not> a s \<Longrightarrow>
(a \<and>* stack h d \<and>* b) = (stack h d \<and>* a \<and>* b)"
by(rule sep.mult.left_commute)

method order_sep_conj=
(simp add: stack_first not_stack)?,
(simp add: stack_height_first)?

method sep_imp_solve =
(clarsimp?),
(rule conjI),
  (clarsimp simp add: word_rcat_simps)?,
  order_sep_conj?,
  (sep_cancel, simp?)+,
  (erule instantiate_emp)?,
(simp add:word_rcat_simps)?
value "word_rsplit (0x3ecb5edf::32 word):: byte list"
find_theorems "size" name:word

lemma length_word_rsplit_32:
"length (word_rsplit (x::w256)::byte list) = 32"
by(simp add: length_word_rsplit_exp_size' word_size)

lemma word_of_int_hash_not_0:
"word_of_int
 (bin_rcat 8
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) \<noteq>
(0::w256)"
by(simp add: bin_rcat_def bin_cat_def)


lemmas calldataload_simps=
read_word_from_bytes_def
byte_list_fill_right_def

lemmas words_simps=
word_of_int_hash_not_0
word_rcat_eq
length_word_rsplit_32

method blocks_rule_vcg=
rule blocks_jumpi_uint |
rule blocks_jump_uint |
rule blocks_next |
rule blocks_no

method block_vcg=
((blocks_rule_vcg; (rule refl)?), triple_seq_vcg),
(sep_imp_solve; simp?)+,
(simp_all add: word_rcat_simps bin_cat_def)?

context
notes
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  memory_range.simps[simp del]
  blocks_ex_def[simp add]
  insts_ex_def[simp add]
begin

lemma length_word_rsplit_4:
"length (word_rsplit (x::32 word)::byte list) = 4"
by(simp add: length_word_rsplit_exp_size' word_size)


lemma power_mult:
"((\<lambda>s. s * (x::int)) ^^ m) = (\<lambda>s. s * (x ^ m))"
apply(rule ext)
apply(induction m; simp)
done

lemma div_mult2_eq_word:
"unat b * unat d < 2 ^ len_of TYPE('a) \<Longrightarrow>
(a:: 'a :: len word) div (b * d) = a div b div d"
  apply unat_arith
  apply clarsimp
  apply (subst unat_mult_lem [THEN iffD1], simp)
  apply(rule div_mult2_eq)
done

lemma word_mult_left_cancel: 
  "(0 :: 'a :: len word) < y \<Longrightarrow> unat x * unat y < 2 ^ len_of TYPE('a) \<Longrightarrow>
   unat z * unat y < 2 ^ len_of TYPE('a) \<Longrightarrow>
    (x * y = z * y) = (x = z)"
  apply unat_arith
  apply clarsimp
  apply(rule iffI)
   defer
   apply(simp)
  apply(drule unat_cong)
  apply (subst (asm)unat_mult_lem [THEN iffD1], simp)
  apply(simp)
  apply (subst (asm)unat_mult_lem [THEN iffD1], simp)
  apply auto
  done

lemma word_rcat_div_1_a_not0:
"a \<noteq> 0 \<Longrightarrow>
 n \<le> 27 \<Longrightarrow>
 m \<le> 27 \<Longrightarrow>
16777216 * uint a + 65536 * uint b + 256 * uint d + uint e = f \<Longrightarrow>
((word_rcat ([a::byte,b,d,e] @ replicate (Suc n) 0))::w256) div
(word_rcat ([1::byte] @ (replicate (Suc m) 0))::w256) =
(word_rcat ([a,b,d,e] @ (replicate n 0))::w256) div
(word_rcat ([1::byte] @ (replicate m 0))::w256)"
apply(simp add: word_rcat_def bin_rcat_def bin_cat_num)
apply(rule subst[OF mult.commute])
apply(simp add: foldl_conv_fold power_mult)
apply(subst Word.word_ubin.norm_Rep[where x=a, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=b, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=d, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=e, simplified])+
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. x div _ = _"])
apply(rule subst[OF wi_hom_mult[where b=256 and a="16777216 * uint a + 65536 * uint b + 256 * uint d + uint e", simplified], where P="\<lambda>x. x * _ div _ = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ div x = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ = x div _"])
apply(simp add: mult.commute)
apply(subst div_mult2_eq_word)
 apply(simp add: unat_def uint_word_of_int)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst int_mod_eq')
   apply(simp)
  apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=32 and a=256, simplified])
  apply(simp)
 apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=31 and a=256, simplified])
 apply(simp)
apply(simp add: mult.assoc mult.commute[where a="0x100"])
apply(simp add: sym[OF mult.assoc])
apply(subst Word.word_div_mult)
  apply(simp_all)
apply(subgoal_tac "f > 0")
 apply(simp add: unat_def)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst wi_hom_mult)
 apply(subst sym[OF word_less_alt[where a="word_of_int (f * 256^n)" and b="word_of_int (uint (2^248::w256))::w256", simplified]])
 apply(subst wi_less[where n="f * 256^n" and m="uint (2^248::w256)" and 'a=256, simplified])
 apply(subgoal_tac "f < 256 ^4"; simp)
	apply(subst int_mod_eq'[where a="f * 256 ^ n" and b="2^256", simplified]; simp?)
   apply(rule mult_strict_mono[where d="256^28::int" and b=4294967296, simplified]; simp?)
   apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=28 and a=256, simplified], simp)
  apply(rule mult_less_le_imp_less[where d="256^27::int" and b=4294967296, simplified]; simp?)
  apply(rule Power.linordered_semidom_class.power_increasing[where N=27 and a=256, simplified], simp)
 apply(drule sym; simp)
 apply(insert uint_lt[where w="a"])[1]
 apply(insert uint_lt[where w="b"])[1]
 apply(insert uint_lt[where w="d"])[1]
 apply(insert uint_lt[where w="e"])[1]
 apply(simp)
apply(drule sym; simp)
apply(subgoal_tac "uint a > 0")
 apply(insert uint_0[where w=b])[1]
 apply(insert uint_0[where w=d])[1]
 apply(insert uint_0[where w=e])[1]
 apply(arith)
apply(insert uint_0[where w=a])[1]
apply(subgoal_tac "uint a \<noteq> 0")
 apply(arith)
apply(rule notI)
apply(simp add: uint_0_iff)
done

method word32_not_0_aux=
		 (subgoal_tac "uint a > 0"),
	  (arith),
	 (subgoal_tac "uint a \<noteq> 0"),
	  (arith),
	 (rule notI),
	 (simp add: uint_0_iff)

lemma word32_not_0:
	"\<And>a b d e.(a \<noteq> 0 \<or> b\<noteq>0 \<or> d\<noteq>0 \<or> e\<noteq>0) \<Longrightarrow> (uint a * 16777216 + uint b * 65536 + uint d * 256 + uint e) > 0"
apply(cut_tac w=a in uint_0)
apply(cut_tac w=b in uint_0)
apply(cut_tac w=d in uint_0)
apply(cut_tac w=e in uint_0)
	apply(erule disjE, word32_not_0_aux)
	apply(erule disjE)
		apply(rename_tac b a d e, word32_not_0_aux)
	apply(erule disjE)
		apply(rename_tac d b a e, word32_not_0_aux)
	apply(rename_tac e b d a, word32_not_0_aux)
done
	
lemma word_rcat_div_1:
"a \<noteq> 0 \<or> b\<noteq>0 \<or> d\<noteq>0 \<or> e\<noteq>0 \<Longrightarrow>
 n \<le> 27 \<Longrightarrow>
 m \<le> 27 \<Longrightarrow>
16777216 * uint a + 65536 * uint b + 256 * uint d + uint e = f \<Longrightarrow>
((word_rcat ([a::byte,b,d,e] @ replicate (Suc n) 0))::w256) div
(word_rcat ([1::byte] @ (replicate (Suc m) 0))::w256) =
(word_rcat ([a,b,d,e] @ (replicate n 0))::w256) div
(word_rcat ([1::byte] @ (replicate m 0))::w256)"
apply(simp add: word_rcat_def bin_rcat_def bin_cat_num)
apply(rule subst[OF mult.commute])
apply(simp add: foldl_conv_fold power_mult)
apply(subst Word.word_ubin.norm_Rep[where x=a, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=b, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=d, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=e, simplified])+
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. x div _ = _"])
apply(rule subst[OF wi_hom_mult[where b=256 and a="16777216 * uint a + 65536 * uint b + 256 * uint d + uint e", simplified], where P="\<lambda>x. x * _ div _ = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ div x = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ = x div _"])
apply(simp add: mult.commute)
apply(subst div_mult2_eq_word)
 apply(simp add: unat_def uint_word_of_int)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst int_mod_eq')
   apply(simp)
  apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=32 and a=256, simplified])
  apply(simp)
 apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=31 and a=256, simplified])
 apply(simp)
apply(simp add: mult.assoc mult.commute[where a="0x100"])
apply(simp add: sym[OF mult.assoc])
apply(subst Word.word_div_mult)
  apply(simp_all)
apply(subgoal_tac "f > 0")
 apply(simp add: unat_def)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst wi_hom_mult)
 apply(subst sym[OF word_less_alt[where a="word_of_int (f * 256^n)" and b="word_of_int (uint (2^248::w256))::w256", simplified]])
 apply(subst wi_less[where n="f * 256^n" and m="uint (2^248::w256)" and 'a=256, simplified])
 apply(subgoal_tac "f < 256 ^4"; simp)
	apply(subst int_mod_eq'[where a="f * 256 ^ n" and b="2^256", simplified]; simp?)
   apply(rule mult_strict_mono[where d="256^28::int" and b=4294967296, simplified]; simp?)
   apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=28 and a=256, simplified], simp)
  apply(rule mult_less_le_imp_less[where d="256^27::int" and b=4294967296, simplified]; simp?)
  apply(rule Power.linordered_semidom_class.power_increasing[where N=27 and a=256, simplified], simp)
 apply(drule sym; simp)
 apply(insert uint_lt[where w="a"])[1]
 apply(insert uint_lt[where w="b"])[1]
 apply(insert uint_lt[where w="d"])[1]
 apply(insert uint_lt[where w="e"])[1]
 apply(simp)
apply(drule sym; simp add: mult.commute)
apply(rule word32_not_0[simplified], assumption)
done

lemma word_rcat_div1:
"a \<noteq> 0 \<or> b\<noteq>0 \<or> d\<noteq>0 \<or> e\<noteq>0 \<Longrightarrow>
 n \<le> 28 \<Longrightarrow>
16777216 * uint a + 65536 * uint b + 256 * uint d + uint e = f \<Longrightarrow>
((word_rcat ([a::byte,b,d,e] @ replicate n 0))::w256) div
(word_rcat ([1::byte] @ (replicate n 0))::w256) =
(word_rcat ([a,b,d,e])::w256)"
apply(induction n; simp)
 apply(subgoal_tac "word_rcat [1::byte] = (1::(w256))")
  apply(simp add: word_div_def)
 apply(simp add: word_rcat_simps)
apply(subst word_rcat_div_1[simplified]; simp)
done

definition bit_mask :: "32 word \<Rightarrow> 256 word" where
"bit_mask z =  4294967295 AND
    word_of_int
     (uint
       (word_rcat
         (word_rsplit z @
          [0::byte, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           0, 0, 0, 0, 0, 0, 0, 0])::w256) div
      26959946667150639794667015087019630673637144422540572481103610249216)"

lemma w:
 "  word_rsplit w = sw \<Longrightarrow>
  \<forall>k m. k < length sw \<longrightarrow> m < size (hd sw) \<longrightarrow>
  rev sw ! k !! m = w !! (k * size (hd sw) + m)"
apply (clarsimp)
apply (rule test_bit_rsplit[OF sym, rule_format] ; simp)
done

lemma list0_x:
"\<forall>k<Suc (Suc (Suc (Suc 0))).
       \<forall>m<8.
          [0, 0, 0, 0::byte] ! k !! m = z !! (k * 8 + m) \<Longrightarrow>
n <32 \<Longrightarrow>
    \<not> z !! n"
apply(drule_tac x="n div 8" in spec)
apply(drule mp)
apply unat_arith
apply(drule_tac x="n mod 8" in spec)
 apply(drule mp, arith)
apply(simp)
apply(subgoal_tac "[0, 0, 0, 0] ! (n div 8) = (0::byte)")
apply(simp)
apply(subgoal_tac "n div 8 < 4")
apply (subst nth_Cons', clarsimp  split: if_split)+
apply (unat_arith)
done

lemma word_rsplit_0':
	"word_rsplit (z::32 word) = [0,0,0,0::byte] \<Longrightarrow>
	z =0"
apply (drule w)
apply clarsimp
apply (simp add: word_size)
apply (word_bitwise)
apply ((rule conjI)?, erule list0_x, simp)+
done

lemma word_rcat_nul_bits:
"n \<ge> 32 \<Longrightarrow>  \<not>((word_rcat ([a,b,d,e]::byte list))::w256) !! n"
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
apply(simp add: bintrunc_def)
done

lemma word_rsplit_32:
"\<exists>a b d e. word_rsplit (z::32 word) = [a,b,d,e::byte]"
apply(insert length_word_rsplit_4[where x=z])
apply(case_tac "word_rsplit z::byte list")
 apply(simp)
apply(rename_tac list, case_tac list, simp)
apply(rename_tac list, case_tac list, simp)
apply(rename_tac list, case_tac list, simp)
  apply(simp)
done

lemma word_rcat_rsplit_ucast:
"(word_rcat (word_rsplit z::byte list)::w256) = ucast (z::32 word)"
 apply(simp add: ucast_def)
 apply (rule word_eqI)
 apply(case_tac "n < 32")
  apply (clarsimp simp add : test_bit_rcat word_size)
  apply (subst refl [THEN test_bit_rsplit])
    apply (simp_all add: word_size 
      refl [THEN length_word_rsplit_size [simplified not_less [symmetric], simplified]])
  apply safe
     apply(subst (asm) word_test_bit_def, assumption)
    apply(arith)
   apply(subst word_test_bit_def, assumption)
  apply(drule leI)
  apply(insert word_rsplit_32[where z=z], clarsimp)[1]
  apply(drule_tac a=a and b=b and d=d and e=e in word_rcat_nul_bits, simp)
 apply(drule leI)
 apply(drule bin_nth_uint_imp, simp)
done

lemma word_rcat_bits_eq:
"n < 32 \<Longrightarrow>  ((word_rcat (word_rsplit z::byte list))::w256) !! n = (z::32 word) !! n"
apply(insert word_rsplit_32[where z=z])
apply(clarsimp)
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
apply(simp add: bintrunc_def)
oops

lemma word_rcat_rsplit_max: "(word_rcat [a,b,d,e::byte]::w256) \<le> mask 32"
apply(subst le_mask_iff)
  apply (rule word_eqI)
 apply (subst nth_shiftr)
  apply(simp add: word_size)
  apply(simp add: word_rcat_nul_bits)
done

lemma
	eval_bit_mask':
	"bit_mask z = word_rcat (word_rsplit (z::32 word)::byte list)"
	apply(simp add: bit_mask_def)
  apply(subgoal_tac "\<exists>a b d e. word_rsplit (z::32 word) = [a::byte,b,d,e]")
	apply(rule subst[OF uint_div[where x="word_rcat
         (word_rsplit z @
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           0])" and y="26959946667150639794667015087019630673637144422540572481103610249216::w256", simplified],
          where P="\<lambda>x. _ AND word_of_int x = _"])
  apply(case_tac "z\<noteq>0")
  apply(clarsimp)
   apply(cut_tac a=a and b=b and d=d and e=e and n=28 in word_rcat_div1)
   apply(subgoal_tac "\<not>([a::byte,b,d,e] = [0,0,0,0::byte])")
    apply(simp)
   apply(rule notI)
    apply(drule sym[where s="word_rsplit _"]; simp)
    apply(drule word_rsplit_0')
   apply(simp)+
   apply(subgoal_tac "word_rcat [1::byte, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
        (0x100000000000000000000000000000000000000000000000000000000::w256)")
    apply(clarsimp)
   (* apply(thin_tac _, thin_tac _,thin_tac _, thin_tac _) *)
   apply(thin_tac "word_rcat _ = _", thin_tac " _ = word_rcat _")
   apply (subgoal_tac "0xFFFFFFFF = (mask 32::256 word)")
   apply(simp only:word_bw_comms)
 apply (subst word_bw_comms(1))
   apply (subst le_mask_imp_and_mask)
   apply(rule word_rcat_rsplit_max)
apply(simp)
apply(simp add: mask_def)
apply(thin_tac _)+
apply(simp add: word_rcat_simps bin_cat_def)
apply(clarsimp)
apply(subst (asm) Word_Lemmas_32.word_rsplit_0)
apply(clarsimp simp add: word_rcat_simps bin_cat_def)
apply(rule word_rsplit_32)
done

lemma
	eval_bit_mask:
	"bit_mask z = ucast (z::32 word)"
apply(subst eval_bit_mask')
apply(subst word_rcat_rsplit_ucast)
apply(rule refl)
done


lemma bit_mask_noteq:
"x \<noteq> y \<Longrightarrow> bit_mask x \<noteq> bit_mask y"
apply(rule notI)
apply(subst (asm) eval_bit_mask)+
apply(drule up_ucast_inj; simp)
done

method bit_mask_solve=
(insert length_word_rsplit_4[where x=z])[1],
(split if_split_asm; simp)+,
(drule bit_mask_noteq),
(subst (asm) eval_bit_mask)+,
(simp add: ucast_def)

lemmas bit_mask_rev = sym[OF bit_mask_def]

definition return_action' ::"32 word  \<Rightarrow> contract_action" where
"return_action' z = 
  (if z = dispatch1_hash then ContractReturn (word_rsplit (1::w256))
  else (if z = dispatch2_hash then ContractReturn (word_rsplit (2:: w256))
  else ContractFail [ShouldNotHappen]))"
(*
lemma spec_fail:
notes bit_mask_rev[simp add]
shows
"z \<noteq> dispatch1_hash \<Longrightarrow>
z \<noteq> dispatch2_hash \<Longrightarrow>
\<exists>r.
triple 
  (
program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (z::32 word)::byte list)) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_ex
  (action (ContractFail [ShouldNotHappen]) ** r)"
apply (simp add: blocks_simps triple_def dispatch1_hash_def dispatch2_hash_def)
apply(rule exI)
apply(block_vcg; bit_mask_solve)
apply(block_vcg; bit_mask_solve)
apply(block_vcg)
apply(sep_cancel)+
done
    
lemma spec_fun1:
"\<exists>r.
triple 
  (
program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (0x3ecb5edf::32 word))) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_ex
  (action (ContractReturn (word_rsplit (1:: w256))) ** r)"
apply (simp add: triple_def blocks_simps)
apply(rule exI)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
apply(sep_cancel)+
done

lemma spec_fun2:
"\<exists>r.
triple 
  (
program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (0x8cd5b077::32 word))) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_ex
  (action (ContractReturn (word_rsplit (2:: w256))) ** r)"
apply (simp add: blocks_simps triple_def)
apply(rule exI)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
	apply(block_vcg)
	apply(block_vcg)+
apply(sep_cancel)+
done

lemma verify_dispatcher:
notes
  bit_mask_rev[simp add]
shows
"\<exists>r. triple 
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (z::32 word)::byte list)) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_ex
  (action (return_action' z) ** r)"
apply(simp add: return_action'_def blocks_simps triple_def dispatch1_hash_def dispatch2_hash_def)
apply(split if_split, rule conjI)
 apply(rule impI, rule exI)
 apply((block_vcg)+)[1]
 apply(sep_cancel)+
apply(clarsimp simp add: dispatch2_hash_def)
apply(split if_split, rule conjI)
 apply(rule impI, rule exI)
 apply((block_vcg)+)[1]
 apply(sep_cancel)+
apply(clarsimp simp add: dispatch2_hash_def)
apply(rule exI)
apply((block_vcg; bit_mask_solve?)+)[1]
apply(sep_cancel)+
done
*)
end
end
end
