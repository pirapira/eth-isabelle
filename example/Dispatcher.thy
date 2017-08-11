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

lemmas blocks_simps = build_blocks_def byteListInt_def find_block_def extract_indexes_def build_vertices_def
 aux_basic_block.simps add_address_def block_pt_def

value "parse_bytecode ''90''"

value"blocks_list (build_blocks (parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ecb5edf1460475780638cd5b07714607b575b600080fd5b3415605157600080fd5b6065600480803590602001909190505060a1565b6040518082815260200191505060405180910390f35b3415608557600080fd5b608b60ad565b6040518082815260200191505060405180910390f35b6000600190505b919050565b6000600290505b905600a165627a7a72305820c9cf1e9d83721f6f9afecea62b7e868d98502ee8556dcaf6abb24acb8bc0d9fb0029''))"

definition insts where
"insts \<equiv>
[Stack (PUSH_N [96]), Stack (PUSH_N [64]), Memory MSTORE, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Swap 0, Arith DIV, Stack (PUSH_N [255, 255, 255, 255]), Bits inst_AND, Dup 0,
  Stack (PUSH_N [62, 203, 94, 223]), Arith inst_EQ, Stack (PUSH_N [71]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [140, 213, 176, 119]), Arith inst_EQ, Stack (PUSH_N [123]), Pc JUMPI, Pc JUMPDEST,
  Stack (PUSH_N [0]), Dup 0, Unknown 253, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [81]),
  Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 253, Pc JUMPDEST, Stack (PUSH_N [101]), Stack (PUSH_N [4]),
  Dup 0, Dup 0, Stack CALLDATALOAD, Swap 0, Stack (PUSH_N [32]), Arith ADD, Swap 0, Swap 1, Swap 0, Stack POP,
  Stack POP, Stack (PUSH_N [161]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [64]), Memory MLOAD, Dup 0, Dup 2,
  Dup 1, Memory MSTORE, Stack (PUSH_N [32]), Arith ADD, Swap 1, Stack POP, Stack POP, Stack (PUSH_N [64]),
  Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [133]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 253, Pc JUMPDEST, Stack (PUSH_N [139]),
  Stack (PUSH_N [173]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [64]), Memory MLOAD, Dup 0, Dup 2, Dup 1,
  Memory MSTORE, Stack (PUSH_N [32]), Arith ADD, Swap 1, Stack POP, Stack POP, Stack (PUSH_N [64]),
  Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST, Stack (PUSH_N [0]),
  Stack (PUSH_N [1]), Swap 0, Stack POP, Pc JUMPDEST, Swap 1, Swap 0, Stack POP, Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0]), Stack (PUSH_N [2]), Swap 0, Stack POP, Pc JUMPDEST, Swap 0, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [98, 122, 122, 114, 48, 88]), Arith SHA3, Unknown 201, Unknown 207, Unknown 30, Swap 13, Dup 3,
  Stack (PUSH_N [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202, 246, 171]),
  Unknown 178, Unknown 74, Unknown 203, Dup 02, Unknown 192, Unknown 217, Unknown 251, Misc STOP, Unknown 41]"

definition blocks where
"blocks =
\<lparr>blocks_indexes = [0, 56, 66, 71, 77, 81, 101, 123, 129, 133, 139, 161, 168, 173, 180, 183, 184, 226],
    blocks_list = map_of [(0, [(0, Stack (PUSH_N [96])), (2, Stack (PUSH_N [64])), (4, Memory MSTORE), (5, Stack (PUSH_N [0])),
            (7, Stack CALLDATALOAD),
            (8, Stack (PUSH_N
                        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                         0])),
            (38, Swap 0), (39, Arith DIV), (40, Stack (PUSH_N [255, 255, 255, 255])), (45, Bits inst_AND),
            (46, Dup 0), (47, Stack (PUSH_N [62, 203, 94, 223])), (52, Arith inst_EQ),
            (53, Stack (PUSH_N [71]))],
        Jumpi),
       (56, [(56, Dup 0), (57, Stack (PUSH_N [140, 213, 176, 119])), (62, Arith inst_EQ),
             (63, Stack (PUSH_N [123]))],
        Jumpi),
       (66, [(66, Pc JUMPDEST), (67, Stack (PUSH_N [0])), (69, Dup 0), (70, Unknown 253)], No),
       (71, [(71, Pc JUMPDEST), (72, Info CALLVALUE), (73, Arith ISZERO), (74, Stack (PUSH_N [81]))], Jumpi),
       (77, [(77, Stack (PUSH_N [0])), (79, Dup 0), (80, Unknown 253)], No),
       (81, [(81, Pc JUMPDEST), (82, Stack (PUSH_N [101])), (84, Stack (PUSH_N [4])), (86, Dup 0), (87, Dup 0),
             (88, Stack CALLDATALOAD), (89, Swap 0), (90, Stack (PUSH_N [32])), (92, Arith ADD), (93, Swap 0),
             (94, Swap 1), (95, Swap 0), (96, Stack POP), (97, Stack POP), (98, Stack (PUSH_N [161]))],
        Jump),
       (101, [(101, Pc JUMPDEST), (102, Stack (PUSH_N [64])), (104, Memory MLOAD), (105, Dup 0), (106, Dup 2),
              (107, Dup 1), (108, Memory MSTORE), (109, Stack (PUSH_N [32])), (111, Arith ADD), (112, Swap 1),
              (113, Stack POP), (114, Stack POP), (115, Stack (PUSH_N [64])), (117, Memory MLOAD),
              (118, Dup 0), (119, Swap 1), (120, Arith SUB), (121, Swap 0), (122, Misc RETURN)],
        No),
       (123, [(123, Pc JUMPDEST), (124, Info CALLVALUE), (125, Arith ISZERO), (126, Stack (PUSH_N [133]))],
        Jumpi),
       (129, [(129, Stack (PUSH_N [0])), (131, Dup 0), (132, Unknown 253)], No),
       (133, [(133, Pc JUMPDEST), (134, Stack (PUSH_N [139])), (136, Stack (PUSH_N [173]))], Jump),
       (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [64])), (142, Memory MLOAD), (143, Dup 0), (144, Dup 2),
              (145, Dup 1), (146, Memory MSTORE), (147, Stack (PUSH_N [32])), (149, Arith ADD), (150, Swap 1),
              (151, Stack POP), (152, Stack POP), (153, Stack (PUSH_N [64])), (155, Memory MLOAD),
              (156, Dup 0), (157, Swap 1), (158, Arith SUB), (159, Swap 0), (160, Misc RETURN)],
        No),
       (161, [(161, Pc JUMPDEST), (162, Stack (PUSH_N [0])), (164, Stack (PUSH_N [1])), (166, Swap 0),
              (167, Stack POP)],
        Next),
       (168, [(168, Pc JUMPDEST), (169, Swap 1), (170, Swap 0), (171, Stack POP)], Jump),
       (173, [(173, Pc JUMPDEST), (174, Stack (PUSH_N [0])), (176, Stack (PUSH_N [2])), (178, Swap 0),
              (179, Stack POP)],
        Next),
       (180, [(180, Pc JUMPDEST), (181, Swap 0)], Jump), (183, [(183, Misc STOP)], No),
       (184, [(184, Log LOG1), (185, Stack (PUSH_N [98, 122, 122, 114, 48, 88])), (192, Arith SHA3),
              (193, Unknown 201), (194, Unknown 207), (195, Unknown 30), (196, Swap 13), (197, Dup 3),
              (198, Stack (PUSH_N
                            [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202,
                             246, 171])),
              (218, Unknown 178), (219, Unknown 74), (220, Unknown 203), (221, Dup 02), (222, Unknown 192),
              (223, Unknown 217), (224, Unknown 251), (225, Misc STOP)],
        No),
       (226, [(226, Unknown 41)], No)],
    all_blocks =
      [(0, [(0, Stack (PUSH_N [96])), (2, Stack (PUSH_N [64])), (4, Memory MSTORE), (5, Stack (PUSH_N [0])),
            (7, Stack CALLDATALOAD),
            (8, Stack (PUSH_N
                        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                         0])),
            (38, Swap 0), (39, Arith DIV), (40, Stack (PUSH_N [255, 255, 255, 255])), (45, Bits inst_AND),
            (46, Dup 0), (47, Stack (PUSH_N [62, 203, 94, 223])), (52, Arith inst_EQ),
            (53, Stack (PUSH_N [71]))],
        Jumpi),
       (56, [(56, Dup 0), (57, Stack (PUSH_N [140, 213, 176, 119])), (62, Arith inst_EQ),
             (63, Stack (PUSH_N [123]))],
        Jumpi),
       (66, [(66, Pc JUMPDEST), (67, Stack (PUSH_N [0])), (69, Dup 0), (70, Unknown 253)], Next),
       (71, [(71, Pc JUMPDEST), (72, Info CALLVALUE), (73, Arith ISZERO), (74, Stack (PUSH_N [81]))], Jumpi),
       (77, [(77, Stack (PUSH_N [0])), (79, Dup 0), (80, Unknown 253)], Next),
       (81, [(81, Pc JUMPDEST), (82, Stack (PUSH_N [101])), (84, Stack (PUSH_N [4])), (86, Dup 0), (87, Dup 0),
             (88, Stack CALLDATALOAD), (89, Swap 0), (90, Stack (PUSH_N [32])), (92, Arith ADD), (93, Swap 0),
             (94, Swap 1), (95, Swap 0), (96, Stack POP), (97, Stack POP), (98, Stack (PUSH_N [161]))],
        Jump),
       (101, [(101, Pc JUMPDEST), (102, Stack (PUSH_N [64])), (104, Memory MLOAD), (105, Dup 0), (106, Dup 2),
              (107, Dup 1), (108, Memory MSTORE), (109, Stack (PUSH_N [32])), (111, Arith ADD), (112, Swap 1),
              (113, Stack POP), (114, Stack POP), (115, Stack (PUSH_N [64])), (117, Memory MLOAD),
              (118, Dup 0), (119, Swap 1), (120, Arith SUB), (121, Swap 0), (122, Misc RETURN)],
        No),
       (123, [(123, Pc JUMPDEST), (124, Info CALLVALUE), (125, Arith ISZERO), (126, Stack (PUSH_N [133]))],
        Jumpi),
       (129, [(129, Stack (PUSH_N [0])), (131, Dup 0), (132, Unknown 253)], Next),
       (133, [(133, Pc JUMPDEST), (134, Stack (PUSH_N [139])), (136, Stack (PUSH_N [173]))], Jump),
       (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [64])), (142, Memory MLOAD), (143, Dup 0), (144, Dup 2),
              (145, Dup 1), (146, Memory MSTORE), (147, Stack (PUSH_N [32])), (149, Arith ADD), (150, Swap 1),
              (151, Stack POP), (152, Stack POP), (153, Stack (PUSH_N [64])), (155, Memory MLOAD),
              (156, Dup 0), (157, Swap 1), (158, Arith SUB), (159, Swap 0), (160, Misc RETURN)],
        No),
       (161, [(161, Pc JUMPDEST), (162, Stack (PUSH_N [0])), (164, Stack (PUSH_N [1])), (166, Swap 0),
              (167, Stack POP)],
        Next),
       (168, [(168, Pc JUMPDEST), (169, Swap 1), (170, Swap 0), (171, Stack POP)], Jump),
       (173, [(173, Pc JUMPDEST), (174, Stack (PUSH_N [0])), (176, Stack (PUSH_N [2])), (178, Swap 0),
              (179, Stack POP)],
        Next),
       (180, [(180, Pc JUMPDEST), (181, Swap 0)], Jump), (183, [(183, Misc STOP)], No),
       (184, [(184, Log LOG1), (185, Stack (PUSH_N [98, 122, 122, 114, 48, 88])), (192, Arith SHA3),
              (193, Unknown 201), (194, Unknown 207), (195, Unknown 30), (196, Swap 13), (197, Dup 3),
              (198, Stack (PUSH_N
                            [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202,
                             246, 171])),
              (218, Unknown 178), (219, Unknown 74), (220, Unknown 203), (221, Dup 02), (222, Unknown 192),
              (223, Unknown 217), (224, Unknown 251), (225, Misc STOP)],
        No),
       (226, [(226, Unknown 41)], Next)]\<rparr>"
context
notes if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add] iszero_stack_def[simp add]
begin

lemma aux1:
"(word_of_int (bin_rcat 8 [62, 203, 94, 223]) ::w256)=
    word_of_int (bin_rcat 8 [255, 255, 255, 255]) AND
    (if word_of_int
         (bin_rcat 8
           [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =
        (0::w256)
     then word_of_int 0
     else word_of_int
           (uint
             (read_word_from_bytes
               (unat (word_of_int (bin_rcat 8 [0])))
               (word_rsplit dispatch1_hash)) div
            uint
             (word_of_int
               (bin_rcat 8
                 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])::w256)))"
apply(split if_splits)
 apply(simp add: bin_rcat_def bin_cat_def)
unfolding read_word_from_bytes_def dispatch1_hash_def
apply simp
apply (simp add: byte_list_fill_right_def)
apply (simp add: word_rcat_def bin_rcat_def bin_cat_def  )
done

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
(simp_all add: word_rcat_simps bin_cat_def)

context
notes
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  memory_range.simps[simp del]
begin

lemma spec_fun1:
"\<exists>r.
triple 
  (
program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (0x3ecb5edf::32 word))) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks
  (action (ContractReturn (word_rsplit (1:: w256))) ** r)"
apply (simp add: blocks_def triple_def)
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
  blocks
  (action (ContractReturn (word_rsplit (2:: w256))) ** r)"
apply (simp add: blocks_def triple_def)
apply(rule exI)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
apply(block_vcg)
	apply(block_vcg)
	apply(block_vcg)+
apply(sep_cancel)+
done

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
find_theorems word_rsplit
lemma
	"z \<noteq> 0 \<Longrightarrow>
	 word_rsplit (z::32 word) = [a, b, d, e::byte] \<Longrightarrow>
	 a \<noteq> 0 \<or> b \<noteq> 0 \<or> d \<noteq> 0 \<or> e \<noteq> 0"
	apply(simp add: word_rsplit_def)
		apply(simp add: bin_rsplit_def bin_last_def bin_rest_def)
	oops
	value "(2^32::32word)"
lemma word_rsplit_upt:
  "\<lbrakk> size x = len_of TYPE('a :: len) * n; n \<noteq> 0 \<rbrakk>
    \<Longrightarrow> word_rsplit x = map (\<lambda>i. ucast (x >> i * len_of TYPE ('a)) :: 'a word) (rev [0 ..< n])"
sorry
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

lemma "(x::32 word) AND y = y AND x"
oops

value "(0xffffffff::256 word) !! 32"

lemma
"n < 256 \<Longrightarrow> n \<ge> (8* length zs) \<Longrightarrow>  \<not>(word_rcat (zs::byte list)::w256) !! n"
apply(induction zs arbitrary: n)
 apply(simp add: word_rcat_simps )
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
sorry

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
 apply(rule word_rcat_nul_bits)
apply(simp)
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

lemma spec_fail:
notes
  bit_mask_rev[simp add]
shows
"z \<noteq> dispatch1_hash \<Longrightarrow>
z \<noteq> dispatch2_hash \<Longrightarrow>
\<exists>r.
triple 
  (
program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (z::32 word)::byte list)) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks
  (action (ContractFail [ShouldNotHappen]) ** r)"
apply (simp add: blocks_def triple_def dispatch1_hash_def dispatch2_hash_def)
apply(rule exI)
apply(block_vcg; bit_mask_solve)
apply(block_vcg; bit_mask_solve)
apply(block_vcg)
apply(sep_cancel)+
done

definition return_action' ::"32 word \<Rightarrow> w256 \<Rightarrow> contract_action" where
"return_action' z x = 
  (if z = dispatch1_hash then ContractReturn (word_rsplit (x))
  else (if z = dispatch2_hash then ContractReturn (word_rsplit (2:: w256))
  else ContractFail [ShouldNotHappen]))"


lemma verify_dispatcher:
"\<exists>r. triple 
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (z::32 word)::byte list)) ** sent_value 1 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks
  (action (return_action' z 1) ** r)"
apply(simp add: return_action'_def blocks_def triple_def dispatch1_hash_def dispatch2_hash_def)
apply(split if_split, rule conjI)
 apply(rule impI, rule exI)
 apply((block_vcg)+)[1]
 apply(sep_cancel)+
apply(split if_split, rule conjI)
 apply(rule impI, rule exI)
 apply((block_vcg)+)[1]
 apply(sep_cancel)+
apply(rule impI, rule exI)
apply((block_vcg; bit_mask_solve?)+)[1]
apply(sep_cancel)+
sorry

definition return_action:: "(32 word \<Rightarrow> contract_action option) \<Rightarrow> 32 word \<Rightarrow> contract_action" where
"return_action m w = (case m w of 
   None \<Rightarrow> ContractFail [ShouldNotHappen]
 | Some a \<Rightarrow> a)"

lemma unspec_contract:
"(z = dispatch1_hash \<longrightarrow> triple_blocks blocks (program_counter 71 \<and>* restx) (71, the (blocks_list blocks 71)) (action xx \<and>* restbx)) \<Longrightarrow>
(z = dispatch2_hash \<longrightarrow> triple_blocks blocks (program_counter 123 \<and>* resty) (123, the (blocks_list blocks 123)) (action yy \<and>* restby)) \<Longrightarrow> 
\<exists>rest. 
 triple
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (z::32 word)::byte list)) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [m64::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [m96::byte]::256 word))
  blocks
  (action (return_action (map_of [(dispatch1_hash, xx), (dispatch2_hash, yy)]) z) \<and>* rest) "
apply (simp add: dispatch1_hash_def dispatch2_hash_def)
apply(rule exI)
apply(subst blocks_def, simp add: triple_def)
apply(block_vcg)
apply(case_tac "z=dispatch1_hash")
 apply(simp add: dispatch1_hash_def word_rcat_simps bin_cat_def)
oops

end
end