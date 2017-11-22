theory Escrow

imports
  Dispatcher
begin
(*
pragma solidity ^0.4.0;
contract Escrow {

    address buyer;
    address seller;
    address arbiter;
    uint256 amount;

    function Escrow(address _buyer, address _seller, uint256 _amount) public {
            require (amount > 0 && _buyer != 0 && _seller != 0);
            buyer = _buyer;
            seller = _seller;
            arbiter = msg.sender;
            amount = _amount;
    }

    function addfund() payable public  {
        require (amount > 0 && msg.value == amount && msg.sender == buyer);
        amount = 0;
    }

    function refund() public {
        require (amount == 0 && msg.sender == arbiter);
        selfdestruct(buyer);
    }

    function pay() public {
        require (amount == 0 && msg.sender == arbiter);
        selfdestruct(seller);
    }
}

Compiled with:
 solc --optimize --overwrite -o escrow --bin-runtime --asm --hashes escrow.sol

8f9595d4: addfund()
1b9265b8: pay()
590e1ae3: refund()


*)
value"(parse_bytecode ''6060604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b8811461005b578063590e1ae3146100705780638f9595d414610083575b600080fd5b341561006657600080fd5b61006e61008b565b005b341561007b57600080fd5b61006e6100dc565b61006e61012d565b6003541580156100b657506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b15156100c157600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b60035415801561010757506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561011257600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000600354118015610140575060035434145b801561016757506000543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561017257600080fd5b60006003555600a165627a7a72305820f807170f7f69a6fbdf43f87babe291e9f5d38101a3b65713ccfdbe30975599d30029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [4]),
  Info CALLDATASIZE, Arith inst_LT, Stack (PUSH_N [0, 0x56]), Pc JUMPI,
  Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]),
  Stack
   (PUSH_N
     [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Stack (PUSH_N [0]), Stack CALLDATALOAD, Arith DIV, Bits inst_AND,
  Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8]), Dup 1, Arith inst_EQ, Stack (PUSH_N [0, 0x5B]),
  Pc JUMPI, Dup 0, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3]), Arith inst_EQ,
  Stack (PUSH_N [0, 0x70]), Pc JUMPI, Dup 0, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x83]), Pc JUMPI, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x66]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]),
  Stack (PUSH_N [0, 0x8B]), Pc JUMP, Pc JUMPDEST, Misc STOP, Pc JUMPDEST, Info CALLVALUE,
  Arith ISZERO, Stack (PUSH_N [0, 0x7B]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [0, 0xDC]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [1, 0x2D]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [3]), Storage SLOAD, Arith ISZERO, Dup 0, Arith ISZERO,
  Stack (PUSH_N [0, 0xB6]), Pc JUMPI, Stack POP, Stack (PUSH_N [2]), Storage SLOAD,
  Info CALLER,
  Stack
   (PUSH_N
     [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST,
  Arith ISZERO, Arith ISZERO, Stack (PUSH_N [0, 0xC1]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [1]), Storage SLOAD,
  Stack
   (PUSH_N
     [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [3]), Storage SLOAD, Arith ISZERO,
  Dup 0, Arith ISZERO, Stack (PUSH_N [1, 7]), Pc JUMPI, Stack POP, Stack (PUSH_N [2]),
  Storage SLOAD, Info CALLER,
  Stack
   (PUSH_N
     [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST,
  Arith ISZERO, Arith ISZERO, Stack (PUSH_N [1, 0x12]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0]), Storage SLOAD,
  Stack
   (PUSH_N
     [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [0]), Stack (PUSH_N [3]),
  Storage SLOAD, Arith inst_GT, Dup 0, Arith ISZERO, Stack (PUSH_N [1, 0x40]), Pc JUMPI,
  Stack POP, Stack (PUSH_N [3]), Storage SLOAD, Info CALLVALUE, Arith inst_EQ, Pc JUMPDEST,
  Dup 0, Arith ISZERO, Stack (PUSH_N [1, 0x67]), Pc JUMPI, Stack POP, Stack (PUSH_N [0]),
  Storage SLOAD, Info CALLER,
  Stack
   (PUSH_N
     [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
      0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST,
  Arith ISZERO, Arith ISZERO, Stack (PUSH_N [1, 0x72]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0]), Stack (PUSH_N [3]), Storage SSTORE, Pc JUMP,
  Misc STOP, Log LOG1, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3,
  Unknown 0xF8, Sarith SMOD, Bits inst_OR, Unknown 0xF,
  Stack
   (PUSH_N
     [0x69, 0xA6, 0xFB, 0xDF, 0x43, 0xF8, 0x7B, 0xAB, 0xE2, 0x91, 0xE9, 0xF5, 0xD3, 0x81, 1,
      0xA3, 0xB6, 0x57, 0x13, 0xCC, 0xFD, 0xBE, 0x30, 0x97, 0x55, 0x99, 0xD3, 0, 0x29])]"
value "length insts_ex"
(* 191 instructions *)

lemma
 "parse_bytecode ''6060604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b8811461005b578063590e1ae3146100705780638f9595d414610083575b600080fd5b341561006657600080fd5b61006e61008b565b005b341561007b57600080fd5b61006e6100dc565b61006e61012d565b6003541580156100b657506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b15156100c157600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b60035415801561010757506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561011257600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000600354118015610140575060035434145b801561016757506000543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561017257600080fd5b60006003555600a165627a7a72305820f807170f7f69a6fbdf43f87babe291e9f5d38101a3b65713ccfdbe30975599d30029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_escrow == build_blocks insts_ex"
value "blocks_escrow"
lemma blocks_escrow_simp:
 "blocks_escrow = [(0, [(0, Stack (PUSH_N [0x60])), (2, Stack (PUSH_N [0x40])), (4, Memory MSTORE),
       (5, Stack (PUSH_N [4])), (7, Info CALLDATASIZE), (8, Arith inst_LT),
       (9, Stack (PUSH_N [0, 0x56]))],
   Jumpi),
  (13, [(13, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])),
        (18, Stack
              (PUSH_N
                [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0])),
        (48, Stack (PUSH_N [0])), (50, Stack CALLDATALOAD), (51, Arith DIV),
        (52, Bits inst_AND), (53, Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8])), (58, Dup 1),
        (59, Arith inst_EQ), (60, Stack (PUSH_N [0, 0x5B]))],
   Jumpi),
  (64, [(64, Dup 0), (65, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3])), (70, Arith inst_EQ),
        (71, Stack (PUSH_N [0, 0x70]))],
   Jumpi),
  (75, [(75, Dup 0), (76, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4])), (81, Arith inst_EQ),
        (82, Stack (PUSH_N [0, 0x83]))],
   Jumpi),
  (86, [(86, Pc JUMPDEST), (87, Stack (PUSH_N [0])), (89, Dup 0), (90, Unknown 0xFD)],
   Terminal),
  (91, [(91, Pc JUMPDEST), (92, Info CALLVALUE), (93, Arith ISZERO),
        (94, Stack (PUSH_N [0, 0x66]))],
   Jumpi),
  (98, [(98, Stack (PUSH_N [0])), (100, Dup 0), (101, Unknown 0xFD)], Terminal),
  (102,
   [(102, Pc JUMPDEST), (103, Stack (PUSH_N [0, 0x6E])), (106, Stack (PUSH_N [0, 0x8B]))],
   Jump),
  (110, [(110, Pc JUMPDEST), (111, Misc STOP)], Terminal),
  (112,
   [(112, Pc JUMPDEST), (113, Info CALLVALUE), (114, Arith ISZERO),
    (115, Stack (PUSH_N [0, 0x7B]))],
   Jumpi),
  (119, [(119, Stack (PUSH_N [0])), (121, Dup 0), (122, Unknown 0xFD)], Terminal),
  (123,
   [(123, Pc JUMPDEST), (124, Stack (PUSH_N [0, 0x6E])), (127, Stack (PUSH_N [0, 0xDC]))],
   Jump),
  (131,
   [(131, Pc JUMPDEST), (132, Stack (PUSH_N [0, 0x6E])), (135, Stack (PUSH_N [1, 0x2D]))],
   Jump),
  (139,
   [(139, Pc JUMPDEST), (140, Stack (PUSH_N [3])), (142, Storage SLOAD), (143, Arith ISZERO),
    (144, Dup 0), (145, Arith ISZERO), (146, Stack (PUSH_N [0, 0xB6]))],
   Jumpi),
  (150,
   [(150, Stack POP), (151, Stack (PUSH_N [2])), (153, Storage SLOAD), (154, Info CALLER),
    (155,
     Stack
      (PUSH_N
        [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
         0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (176, Swap 0), (177, Dup 1), (178, Bits inst_AND), (179, Swap 1), (180, Bits inst_AND),
    (181, Arith inst_EQ)],
   Next),
  (182,
   [(182, Pc JUMPDEST), (183, Arith ISZERO), (184, Arith ISZERO),
    (185, Stack (PUSH_N [0, 0xC1]))],
   Jumpi),
  (189, [(189, Stack (PUSH_N [0])), (191, Dup 0), (192, Unknown 0xFD)], Terminal),
  (193,
   [(193, Pc JUMPDEST), (194, Stack (PUSH_N [1])), (196, Storage SLOAD),
    (197,
     Stack
      (PUSH_N
        [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
         0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (218, Bits inst_AND), (219, Misc SUICIDE)],
   Terminal),
  (220,
   [(220, Pc JUMPDEST), (221, Stack (PUSH_N [3])), (223, Storage SLOAD), (224, Arith ISZERO),
    (225, Dup 0), (226, Arith ISZERO), (227, Stack (PUSH_N [1, 7]))],
   Jumpi),
  (231,
   [(231, Stack POP), (232, Stack (PUSH_N [2])), (234, Storage SLOAD), (235, Info CALLER),
    (236,
     Stack
      (PUSH_N
        [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
         0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (257, Swap 0), (258, Dup 1), (259, Bits inst_AND), (260, Swap 1), (261, Bits inst_AND),
    (262, Arith inst_EQ)],
   Next),
  (263,
   [(263, Pc JUMPDEST), (264, Arith ISZERO), (265, Arith ISZERO),
    (266, Stack (PUSH_N [1, 0x12]))],
   Jumpi),
  (270, [(270, Stack (PUSH_N [0])), (272, Dup 0), (273, Unknown 0xFD)], Terminal),
  (274,
   [(274, Pc JUMPDEST), (275, Stack (PUSH_N [0])), (277, Storage SLOAD),
    (278,
     Stack
      (PUSH_N
        [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
         0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (299, Bits inst_AND), (300, Misc SUICIDE)],
   Terminal),
  (301,
   [(301, Pc JUMPDEST), (302, Stack (PUSH_N [0])), (304, Stack (PUSH_N [3])),
    (306, Storage SLOAD), (307, Arith inst_GT), (308, Dup 0), (309, Arith ISZERO),
    (310, Stack (PUSH_N [1, 0x40]))],
   Jumpi),
  (314,
   [(314, Stack POP), (315, Stack (PUSH_N [3])), (317, Storage SLOAD), (318, Info CALLVALUE),
    (319, Arith inst_EQ)],
   Next),
  (320,
   [(320, Pc JUMPDEST), (321, Dup 0), (322, Arith ISZERO), (323, Stack (PUSH_N [1, 0x67]))],
   Jumpi),
  (327,
   [(327, Stack POP), (328, Stack (PUSH_N [0])), (330, Storage SLOAD), (331, Info CALLER),
    (332,
     Stack
      (PUSH_N
        [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
         0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (353, Swap 0), (354, Dup 1), (355, Bits inst_AND), (356, Swap 1), (357, Bits inst_AND),
    (358, Arith inst_EQ)],
   Next),
  (359,
   [(359, Pc JUMPDEST), (360, Arith ISZERO), (361, Arith ISZERO),
    (362, Stack (PUSH_N [1, 0x72]))],
   Jumpi),
  (366, [(366, Stack (PUSH_N [0])), (368, Dup 0), (369, Unknown 0xFD)], Terminal),
  (370,
   [(370, Pc JUMPDEST), (371, Stack (PUSH_N [0])), (373, Stack (PUSH_N [3])),
    (375, Storage SSTORE)],
   Jump),
  (377, [(377, Misc STOP)], Terminal),
  (378,
   [(378, Log LOG1), (379, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])),
    (386, Arith SHA3), (387, Unknown 0xF8)],
   Terminal),
  (388, [(388, Sarith SMOD), (389, Bits inst_OR), (390, Unknown 0xF)], Terminal),
  (391,
   [(391,
     Stack
      (PUSH_N
        [0x69, 0xA6, 0xFB, 0xDF, 0x43, 0xF8, 0x7B, 0xAB, 0xE2, 0x91, 0xE9, 0xF5, 0xD3, 0x81,
         1, 0xA3, 0xB6, 0x57, 0x13, 0xCC, 0xFD, 0xBE, 0x30, 0x97, 0x55, 0x99, 0xD3, 0,
         0x29]))],
   Next)]"
  by eval

definition addfund_hash :: "32 word"  where
 "addfund_hash = 0x8f9595d4"

definition pay_hash :: "32 word"  where
 "pay_hash = 0x1b9265b8"

definition refund_hash :: "32 word"  where
 "refund_hash = 0x590e1ae3"

definition return_action ::"address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> w256 \<Rightarrow> 32 word \<Rightarrow> w256 \<Rightarrow> contract_action" where
  "return_action sender buyer seller arbiter amount hash v = 
 (if hash = addfund_hash \<and> sender = buyer  \<and> v = amount \<and> amount > 0 then
    ContractReturn []
  else if hash = refund_hash \<and> sender = arbiter \<and> v = 0 \<and> amount = 0 then
    ContractSuicide buyer
  else if hash = pay_hash \<and> sender = arbiter \<and> v = 0 \<and> amount = 0 then
    ContractSuicide seller
  else
    ContractFail [ShouldNotHappen])"

definition return_amount ::"address \<Rightarrow> address \<Rightarrow> address  \<Rightarrow> w256 \<Rightarrow> 32 word \<Rightarrow> w256 \<Rightarrow> w256" where
  "return_amount sender buyer seller amount hash v = 
  (if hash = addfund_hash \<and> sender = buyer \<and> v = amount \<and> amount > 0 then 0 else amount)"

context
notes
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  memory_range.simps[simp del]
 if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] gas_simps[simp] pure_emp_simps[simp add]
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
   solves \<open>rule conjI; rule refl\<close>
 | solves \<open>simp\<close>
 | solves \<open>(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:simp|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp?, ((((sep_cancel, clarsimp?)+)|(clarsimp split:if_split simp: simp)|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp split:if_splits simp:word_rcat_simps) ; sep_imp_solve2 \<close>

method split_conds =
 (split if_split_asm; clarsimp simp add: word_rcat_simps)?

method block_vcg2=
  split_conds,
  ((blocks_rule_vcg; (rule refl)?), triple_seq_vcg),
  (sep_imp_solve2)+,
  (solves \<open>split_conds\<close>)?

theorem verify_escrow_return:
notes
  bit_mask_rev[simp add]
  address_mask_ucast[simp] address_mask_ucast[simplified word_bool_alg.conj.commute, simp]
  ucast_and_w256_drop[simp]
  addfund_hash_def[simp] refund_hash_def[simp] pay_hash_def[simp]
  word_bool_alg.conj.commute[simp]
  length_word_rsplit_4[simp]
  ucast_160_upto_256_eq[simp]
  hash_diff[simp]
  eval_bit_mask[simp]
assumes blk_num: "bn > 2463000"
and net: "at_least_eip150 net"
shows
"\<exists>r. triple net
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit hash::byte list))
   ** sent_value v ** caller sender ** blk_num bn **
   memory_usage 0 ** continuing ** gas_pred 40000
   ** storage 0 (ucast buyer)
   ** storage 1 (ucast seller)
   ** storage 2 (ucast arbiter)
   ** storage 3 amount
   ** account_existence buyer buyer_ex 
   ** account_existence seller seller_ex 
   ** memory (word_rcat [64::byte]) (bytestr_to_w256 [x]) **
   memory (word_rcat [96::byte]) (bytestr_to_w256 [y]))
  blocks_escrow (action (return_action sender buyer seller arbiter amount hash v)
                 ** storage 0 (ucast buyer)
                 ** storage 1 (ucast seller)
                 ** storage 2 (ucast arbiter)
                 ** storage 3 (return_amount sender buyer seller amount hash v)** r)"
  apply (insert blk_num[simplified word_less_nat_alt] net)
  apply (simp add:blocks_escrow_simp)
  apply(simp add: return_action_def return_amount_def blocks_simps triple_def )
  apply(split if_split, rule conjI)+
   apply((rule impI)+, ((erule conjE)+)?, rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
(* 1*)
  apply (clarsimp)+
  apply(split if_split, rule conjI)+
  apply(safe; clarsimp)
  apply( clarsimp)
  apply(rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (clarsimp split: if_split_asm simp: word_rcat_simps)
  apply (clarsimp)+
  apply(split if_split, rule conjI)+
  apply(safe; clarsimp)
  apply( clarsimp)
  apply(rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (clarsimp)
   apply (rule conjI)
   apply (clarsimp simp: word_rcat_simps)
 (* write simp rules to put stack in first pos *)
  apply (sep_select 6)
   apply (sep_cancel)+
   apply (clarsimp split: if_split simp: word_rcat_simps)
   apply (split_conds)
   apply (sep_cancel)+
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
(*1*)
  apply (clarsimp split: if_split )
  apply (rule conjI; clarsimp)
  apply (case_tac " hash = pay_hash"; clarsimp)
  apply (case_tac "v \<noteq> 0")
   apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply (case_tac "amount \<noteq> 0"; clarsimp)
  apply(rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply(rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
(*1*)
  apply (case_tac " hash = refund_hash"; clarsimp)
  apply (case_tac "v \<noteq> 0")
   apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply (case_tac "amount \<noteq> 0"; clarsimp)
  apply(rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply(rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
(*1*)
  apply (case_tac "hash = addfund_hash"; clarsimp)
  apply (case_tac "amount > 0")
  apply (case_tac "amount \<noteq> v")
  apply (case_tac "sender \<noteq> buyer")
  apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
  apply ((block_vcg2)[1])
   apply (split_conds)
  apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply (split_conds)
  apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
  done
end
