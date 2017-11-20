theory Escrow2

imports
  Dispatcher
begin
(*
contract EscrowWallet {

    address from;
    address to;
    address owner;
    uint256 amount;

    function EscrowWallet(address _from, address _to, uint256 _amount) public {
            require (amount > 0);
            from = _from;
            to = _to;
            owner = msg.sender;
            amount = _amount;
    }

    function addfund() payable public  {
        require (amount > 0 && msg.value == amount && msg.sender == from);
        amount = 0;
    }

    function refund() public {
        require (msg.sender == owner);
        selfdestruct(from);
    }

    function pay() public {
        require (msg.sender == owner);
        selfdestruct(to);
    }
}

Compiled with:
 solc --optimize --overwrite -o escrow --bin-runtime --asm --hashes escrow.sol

8f9595d4: addfund()
1b9265b8: pay()
590e1ae3: refund()


*)
value"(parse_bytecode ''6060604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b8811461005b578063590e1ae3146100705780638f9595d414610083575b600080fd5b341561006657600080fd5b61006e61008b565b005b341561007b57600080fd5b61006e6100ce565b61006e610111565b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100b357600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100f657600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000600354118015610124575060035434145b801561014b57506000543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561015657600080fd5b60006003555600a165627a7a72305820629d81bfc4f4b93d45c4a23ece82e54d086d3412bb0f9a65747d991d091292610029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [4]), Info CALLDATASIZE,
  Arith inst_LT, Stack (PUSH_N [0, 0x56]), Pc JUMPI, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]),
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Stack (PUSH_N [0]), Stack CALLDATALOAD, Arith DIV, Bits inst_AND, Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8]),
  Dup 1, Arith inst_EQ, Stack (PUSH_N [0, 0x5B]), Pc JUMPI, Dup 0, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x70]), Pc JUMPI, Dup 0, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x83]), Pc JUMPI, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x66]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [0, 0x8B]), Pc JUMP, Pc JUMPDEST,
  Misc STOP, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x7B]), Pc JUMPI, Stack (PUSH_N [0]),
  Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [0, 0xCE]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [1, 0x11]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [2]), Storage SLOAD,
  Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Stack (PUSH_N [0, 0xB3]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [1]), Storage SLOAD,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [2]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Stack (PUSH_N [0, 0xF6]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0]), Storage SLOAD,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [0]), Stack (PUSH_N [3]), Storage SLOAD,
  Arith inst_GT, Dup 0, Arith ISZERO, Stack (PUSH_N [1, 0x24]), Pc JUMPI, Stack POP, Stack (PUSH_N [3]),
  Storage SLOAD, Info CALLVALUE, Arith inst_EQ, Pc JUMPDEST, Dup 0, Arith ISZERO, Stack (PUSH_N [1, 0x4B]),
  Pc JUMPI, Stack POP, Stack (PUSH_N [0]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST, Arith ISZERO, Arith ISZERO,
  Stack (PUSH_N [1, 0x56]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0]),
  Stack (PUSH_N [3]), Storage SSTORE, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Stack (PUSH_N [0x9D, 0x81, 0xBF]),
  Unknown 0xC4, Misc DELEGATECALL, Unknown 0xB9, Unknown 0x3D, Info GASLIMIT, Unknown 0xC4, Log LOG2,
  Unknown 0x3E, Unknown 0xCE, Dup 2, Unknown 0xE5, Unknown 0x4D, Arith ADDMOD,
  Stack (PUSH_N [0x34, 0x12, 0xBB, 0xF, 0x9A, 0x65, 0x74, 0x7D, 0x99, 0x1D, 9, 0x12, 0x92, 0x61]), Misc STOP,
  Unknown 0x29]"
value "length insts_ex"
(* 171 instructions *)

lemma
 "parse_bytecode ''6060604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b8811461005b578063590e1ae3146100705780638f9595d414610083575b600080fd5b341561006657600080fd5b61006e61008b565b005b341561007b57600080fd5b61006e6100ce565b61006e610111565b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100b357600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100f657600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000600354118015610124575060035434145b801561014b57506000543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561015657600080fd5b60006003555600a165627a7a72305820629d81bfc4f4b93d45c4a23ece82e54d086d3412bb0f9a65747d991d091292610029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_escrow == build_blocks insts_ex"
value "blocks_escrow"
lemma blocks_escrow_simp:
 "blocks_escrow = [(0, [(0, Stack (PUSH_N [0x60])), (2, Stack (PUSH_N [0x40])), (4, Memory MSTORE), (5, Stack (PUSH_N [4])),
       (7, Info CALLDATASIZE), (8, Arith inst_LT), (9, Stack (PUSH_N [0, 0x56]))],
   Jumpi),
  (13, [(13, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])),
        (18, Stack (PUSH_N
                     [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])),
        (48, Stack (PUSH_N [0])), (50, Stack CALLDATALOAD), (51, Arith DIV), (52, Bits inst_AND),
        (53, Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8])), (58, Dup 1), (59, Arith inst_EQ),
        (60, Stack (PUSH_N [0, 0x5B]))],
   Jumpi),
  (64, [(64, Dup 0), (65, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3])), (70, Arith inst_EQ),
        (71, Stack (PUSH_N [0, 0x70]))],
   Jumpi),
  (75, [(75, Dup 0), (76, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4])), (81, Arith inst_EQ),
        (82, Stack (PUSH_N [0, 0x83]))],
   Jumpi),
  (86, [(86, Pc JUMPDEST), (87, Stack (PUSH_N [0])), (89, Dup 0), (90, Unknown 0xFD)], Terminal),
  (91, [(91, Pc JUMPDEST), (92, Info CALLVALUE), (93, Arith ISZERO), (94, Stack (PUSH_N [0, 0x66]))], Jumpi),
  (98, [(98, Stack (PUSH_N [0])), (100, Dup 0), (101, Unknown 0xFD)], Terminal),
  (102, [(102, Pc JUMPDEST), (103, Stack (PUSH_N [0, 0x6E])), (106, Stack (PUSH_N [0, 0x8B]))], Jump),
  (110, [(110, Pc JUMPDEST), (111, Misc STOP)], Terminal),
  (112, [(112, Pc JUMPDEST), (113, Info CALLVALUE), (114, Arith ISZERO), (115, Stack (PUSH_N [0, 0x7B]))],
   Jumpi),
  (119, [(119, Stack (PUSH_N [0])), (121, Dup 0), (122, Unknown 0xFD)], Terminal),
  (123, [(123, Pc JUMPDEST), (124, Stack (PUSH_N [0, 0x6E])), (127, Stack (PUSH_N [0, 0xCE]))], Jump),
  (131, [(131, Pc JUMPDEST), (132, Stack (PUSH_N [0, 0x6E])), (135, Stack (PUSH_N [1, 0x11]))], Jump),
  (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [2])), (142, Storage SLOAD), (143, Info CALLER),
         (144, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (165, Swap 0), (166, Dup 1), (167, Bits inst_AND), (168, Swap 1), (169, Bits inst_AND),
         (170, Arith inst_EQ), (171, Stack (PUSH_N [0, 0xB3]))],
   Jumpi),
  (175, [(175, Stack (PUSH_N [0])), (177, Dup 0), (178, Unknown 0xFD)], Terminal),
  (179, [(179, Pc JUMPDEST), (180, Stack (PUSH_N [1])), (182, Storage SLOAD),
         (183, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (204, Bits inst_AND), (205, Misc SUICIDE)],
   Terminal),
  (206, [(206, Pc JUMPDEST), (207, Stack (PUSH_N [2])), (209, Storage SLOAD), (210, Info CALLER),
         (211, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (232, Swap 0), (233, Dup 1), (234, Bits inst_AND), (235, Swap 1), (236, Bits inst_AND),
         (237, Arith inst_EQ), (238, Stack (PUSH_N [0, 0xF6]))],
   Jumpi),
  (242, [(242, Stack (PUSH_N [0])), (244, Dup 0), (245, Unknown 0xFD)], Terminal),
  (246, [(246, Pc JUMPDEST), (247, Stack (PUSH_N [0])), (249, Storage SLOAD),
         (250, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (271, Bits inst_AND), (272, Misc SUICIDE)],
   Terminal),
  (273, [(273, Pc JUMPDEST), (274, Stack (PUSH_N [0])), (276, Stack (PUSH_N [3])), (278, Storage SLOAD),
         (279, Arith inst_GT), (280, Dup 0), (281, Arith ISZERO), (282, Stack (PUSH_N [1, 0x24]))],
   Jumpi),
  (286, [(286, Stack POP), (287, Stack (PUSH_N [3])), (289, Storage SLOAD), (290, Info CALLVALUE),
         (291, Arith inst_EQ)],
   Next),
  (292, [(292, Pc JUMPDEST), (293, Dup 0), (294, Arith ISZERO), (295, Stack (PUSH_N [1, 0x4B]))], Jumpi),
  (299, [(299, Stack POP), (300, Stack (PUSH_N [0])), (302, Storage SLOAD), (303, Info CALLER),
         (304, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (325, Swap 0), (326, Dup 1), (327, Bits inst_AND), (328, Swap 1), (329, Bits inst_AND),
         (330, Arith inst_EQ)],
   Next),
  (331, [(331, Pc JUMPDEST), (332, Arith ISZERO), (333, Arith ISZERO), (334, Stack (PUSH_N [1, 0x56]))], Jumpi),
  (338, [(338, Stack (PUSH_N [0])), (340, Dup 0), (341, Unknown 0xFD)], Terminal),
  (342, [(342, Pc JUMPDEST), (343, Stack (PUSH_N [0])), (345, Stack (PUSH_N [3])), (347, Storage SSTORE)],
   Jump),
  (349, [(349, Misc STOP)], Terminal),
  (350, [(350, Log LOG1), (351, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])), (358, Arith SHA3),
         (359, Stack (PUSH_N [0x9D, 0x81, 0xBF])), (363, Unknown 0xC4)],
   Terminal),
  (364, [(364, Misc DELEGATECALL)], Terminal), (365, [(365, Unknown 0xB9)], Terminal),
  (366, [(366, Unknown 0x3D)], Terminal), (367, [(367, Info GASLIMIT), (368, Unknown 0xC4)], Terminal),
  (369, [(369, Log LOG2), (370, Unknown 0x3E)], Terminal), (371, [(371, Unknown 0xCE)], Terminal),
  (372, [(372, Dup 2), (373, Unknown 0xE5)], Terminal), (374, [(374, Unknown 0x4D)], Terminal),
  (375, [(375, Arith ADDMOD),
         (376, Stack (PUSH_N [0x34, 0x12, 0xBB, 0xF, 0x9A, 0x65, 0x74, 0x7D, 0x99, 0x1D, 9, 0x12, 0x92, 0x61])),
         (391, Misc STOP)],
   Terminal),
  (392, [(392, Unknown 0x29)], Terminal)]"
  by eval

definition addfund_hash :: "32 word"  where
 "addfund_hash = 0x8f9595d4"

definition pay_hash :: "32 word"  where
 "pay_hash = 0x1b9265b8"

definition refund_hash :: "32 word"  where
 "refund_hash = 0x590e1ae3"

definition return_action ::"address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> w256 \<Rightarrow> 32 word \<Rightarrow> w256 \<Rightarrow> contract_action" where
  "return_action sender from to owner amount hash v = 
 (if hash = addfund_hash \<and> sender = from  \<and> v = amount \<and> amount > 0 then
    ContractReturn []
  else if hash = refund_hash \<and> sender = owner \<and> v = 0 then
    ContractSuicide from
  else if hash = pay_hash \<and> sender = owner \<and> v = 0 then
    ContractSuicide to
  else
    ContractFail [ShouldNotHappen])"

definition return_amount ::"address \<Rightarrow> address \<Rightarrow> address  \<Rightarrow> w256 \<Rightarrow> 32 word \<Rightarrow> w256 \<Rightarrow> w256" where
  "return_amount sender from to amount hash v = 
  (if hash = addfund_hash \<and> sender = from \<and> v = amount \<and> amount > 0 then 0 else amount)"

context
notes
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  memory_range.simps[simp del]
 if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add] iszero_stack_def[simp add]
word256FromNat_def[simp add]
begin
abbreviation "blk_num \<equiv> block_number_pred"

lemma address_mask:
 "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = mask 160"
  by (simp add: mask_def)

lemma address_mask_ucast:
 "ucast (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF && (ucast (w::address))::w256) = w"
  apply (simp add: ucast_ucast_mask address_mask ucast_mask_drop word_bool_alg.conj.commute)
  apply (simp add: mask_def)
  done

lemma ucast_and_w256_drop:
 "((ucast (w::address))::w256) && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = ucast w"
  by word_bitwise

definition
  bytestr_to_w256 :: "byte list \<Rightarrow> w256"  where
 "bytestr_to_w256 \<equiv> word_rcat"

lemma hash_diff:
  "ucast (hash::32 word) = (0x1B9265B8::w256) \<Longrightarrow> hash = 0x1B9265B8 "
  "ucast (hash::32 word) = (0x590E1AE3::w256) \<Longrightarrow> hash = 0x590E1AE3 "
  "ucast (hash::32 word) = (0x8f9595d4::w256) \<Longrightarrow> hash = 0x8f9595d4 "
  by word_bitwise+

lemma ucast_160_upto_256_eq:
  " ((ucast (x::160 word))::w256) = ucast y \<Longrightarrow> x = y"
  by (drule ucast_up_inj; simp)

method sep_imp_solve2 uses simp =
 solves \<open>(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:simp|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:simp word_rcat_simps|rule conjI)+)[1])\<close>

theorem verify_escrow_return:
notes
  bit_mask_rev[simp add]
  address_mask_ucast[simp] address_mask_ucast[simplified word_bool_alg.conj.commute, simp]
  ucast_and_w256_drop[simp]
  addfund_hash_def[simp] refund_hash_def[simp] pay_hash_def[simp]
  word_bool_alg.conj.commute[simp]
  length_word_rsplit_4[simp]
  ucast_160_upto_256_eq[simp]
assumes blk_num: "bn > 2463000"
and net: "at_least_eip150 net"
shows
"\<exists>r. triple net
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit hash::byte list))
   ** sent_value v ** caller sender ** blk_num bn **
   memory_usage 0 ** continuing ** gas_pred 100000
   ** storage 0 (ucast from)
   ** storage 1 (ucast to)
   ** storage 2 (ucast owner)
   ** storage 3 amount
   ** account_existence from from_ex 
   ** account_existence to to_ex 
   ** memory (word_rcat [64::byte]) (bytestr_to_w256 [x]) **
   memory (word_rcat [96::byte]) (bytestr_to_w256 [y]))
  blocks_escrow (action (return_action sender from to owner amount hash v)
                 ** storage 3 (return_amount sender from to amount hash v)** r)"
  apply (insert blk_num[simplified word_less_nat_alt] net)
  apply (simp add:blocks_escrow_simp)
  apply(simp add: return_action_def blocks_simps triple_def )
  apply(split if_split, rule conjI)
   apply(rule impI, ((erule conjE)+)?, rule exI)
   apply((block_vcg)+)[1]
   apply (sep_imp_solve2)
  apply(split if_split, rule conjI)
   apply (clarsimp)
  apply (rule exI)
    apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2)+
    apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2)+
   apply((block_vcg)+)[1]
  apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2)+
  apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2)+
   apply (simp)
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2)+
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2|solves \<open>simp\<close>)+
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2|solves \<open>simp\<close>)+
   apply (clarsimp simp add:word_rcat_simps bin_cat_def Csuicide_def)
   apply ( solves \<open>(clarsimp?, ((((sep_cancel, clarsimp?)+)|clarsimp split: if_split |rule conjI)+)[1])\<close>)
   apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2|solves \<open>simp\<close>)+
   apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
(*1*)
  apply(split if_split, rule conjI)
  apply (clarsimp)
  apply (rule exI)
   apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
   apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp simp add:word_rcat_simps bin_cat_def Csuicide_def)
  apply ( solves \<open>(clarsimp?, ((((sep_cancel, clarsimp?)+)|clarsimp split: if_split |rule conjI)+)[1])\<close>)
  apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff Csuicide_def)
(*1*)
  apply (clarsimp)
  apply (case_tac " hash = pay_hash"; clarsimp)
  apply (case_tac "v \<noteq> 0"; clarsimp)
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  (*2*)
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
(*1*)
  apply (case_tac " hash = refund_hash"; clarsimp)
  apply (case_tac "v \<noteq> 0"; clarsimp)
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  (*2*)
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
(*1*)
  apply (case_tac "hash = addfund_hash"; clarsimp)
  apply (case_tac "v > 0")
  apply (case_tac "sender \<noteq> from")
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp simp:word_rcat_simps bin_cat_def hash_diff)
  apply (rule conjI; rule refl)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (rule conjI; rule refl)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (rule conjI; rule refl)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
(*3*)
  apply blast
(*2*)
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
    apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (rule conjI; rule refl)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
    apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
    apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (rule conjI; rule refl)
  apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply (rule conjI; rule refl)
  apply (clarsimp  simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
(* 1 *)
  apply (rule exI)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff eval_bit_mask)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff eval_bit_mask)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply (clarsimp split: if_split_asm simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((((blocks_rule_vcg; (rule refl)?), triple_seq_vcg)); sep_imp_solve2?)+)[1]
  apply (sep_imp_solve2|solves \<open>simp\<close>)+
  done
end
