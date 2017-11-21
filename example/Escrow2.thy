theory Escrow2

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
 solc --optimize --overwrite -o escrow2 --bin-runtime --asm --hashes escrow2.sol

8f9595d4: addfund()
1b9265b8: pay()
590e1ae3: refund()


*)
value"(parse_bytecode ''606060405263ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b88114610052578063590e1ae3146100675780638f9595d41461007a57600080fd5b341561005d57600080fd5b610065610082565b005b341561007257600080fd5b6100656100d3565b610065610124565b6003541580156100ad57506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b15156100b857600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b6003541580156100fe57506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561010957600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000600354118015610137575060035434145b801561015e57506000543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561016957600080fd5b60006003555600a165627a7a7230582029f2f38b5b84c1c55e91aaca3d9362e635c88ad7e3be217a7183f3cccee1aed40029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]),
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Stack (PUSH_N [0]), Stack CALLDATALOAD, Arith DIV, Bits inst_AND,
  Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8]), Dup 1, Arith inst_EQ, Stack (PUSH_N [0, 0x52]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3]), Arith inst_EQ, Stack (PUSH_N [0, 0x67]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4]), Arith inst_EQ, Stack (PUSH_N [0, 0x7A]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [0, 0x5D]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x65]), Stack (PUSH_N [0, 0x82]), Pc JUMP, Pc JUMPDEST, Misc STOP, Pc JUMPDEST,
  Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x72]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x65]), Stack (PUSH_N [0, 0xD3]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x65]), Stack (PUSH_N [1, 0x24]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [3]),
  Storage SLOAD, Arith ISZERO, Dup 0, Arith ISZERO, Stack (PUSH_N [0, 0xAD]), Pc JUMPI, Stack POP,
  Stack (PUSH_N [2]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST, Arith ISZERO,
  Arith ISZERO, Stack (PUSH_N [0, 0xB8]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [1]), Storage SLOAD,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [3]), Storage SLOAD, Arith ISZERO, Dup 0,
  Arith ISZERO, Stack (PUSH_N [0, 0xFE]), Pc JUMPI, Stack POP, Stack (PUSH_N [2]), Storage SLOAD,
  Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST, Arith ISZERO,
  Arith ISZERO, Stack (PUSH_N [1, 9]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0]), Storage SLOAD,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [0]), Stack (PUSH_N [3]), Storage SLOAD,
  Arith inst_GT, Dup 0, Arith ISZERO, Stack (PUSH_N [1, 0x37]), Pc JUMPI, Stack POP, Stack (PUSH_N [3]),
  Storage SLOAD, Info CALLVALUE, Arith inst_EQ, Pc JUMPDEST, Dup 0, Arith ISZERO, Stack (PUSH_N [1, 0x5E]),
  Pc JUMPI, Stack POP, Stack (PUSH_N [0]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Pc JUMPDEST, Arith ISZERO,
  Arith ISZERO, Stack (PUSH_N [1, 0x69]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0]), Stack (PUSH_N [3]), Storage SSTORE, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Unknown 0x29, Misc CALLCODE,
  Misc RETURN, Dup 0xB, Pc JUMPDEST, Dup 4, Unknown 0xC1, Unknown 0xC5, Unknown 0x5E, Swap 1, Unknown 0xAA,
  Unknown 0xCA, Unknown 0x3D, Swap 3, Stack (PUSH_N [0xE6, 0x35, 0xC8]), Dup 0xA, Unknown 0xD7,
  Unknown 0xE3, Unknown 0xBE, Unknown 0x21,
  Stack (PUSH_N [0x71, 0x83, 0xF3, 0xCC, 0xCE, 0xE1, 0xAE, 0xD4, 0, 0x29])]"
value "length insts_ex"
(* 191 instructions *)

lemma
 "parse_bytecode ''606060405263ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b88114610052578063590e1ae3146100675780638f9595d41461007a57600080fd5b341561005d57600080fd5b610065610082565b005b341561007257600080fd5b6100656100d3565b610065610124565b6003541580156100ad57506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b15156100b857600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b6003541580156100fe57506002543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561010957600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000600354118015610137575060035434145b801561015e57506000543373ffffffffffffffffffffffffffffffffffffffff9081169116145b151561016957600080fd5b60006003555600a165627a7a7230582029f2f38b5b84c1c55e91aaca3d9362e635c88ad7e3be217a7183f3cccee1aed40029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_escrow == build_blocks insts_ex"
value "blocks_escrow"
lemma blocks_escrow_simp:
 "blocks_escrow = [(0, [(0, Stack (PUSH_N [0x60])), (2, Stack (PUSH_N [0x40])), (4, Memory MSTORE),
       (5, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])),
       (10, Stack (PUSH_N
                    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                     0])),
       (40, Stack (PUSH_N [0])), (42, Stack CALLDATALOAD), (43, Arith DIV), (44, Bits inst_AND),
       (45, Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8])), (50, Dup 1), (51, Arith inst_EQ),
       (52, Stack (PUSH_N [0, 0x52]))],
   Jumpi),
  (56, [(56, Dup 0), (57, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3])), (62, Arith inst_EQ),
        (63, Stack (PUSH_N [0, 0x67]))],
   Jumpi),
  (67, [(67, Dup 0), (68, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4])), (73, Arith inst_EQ),
        (74, Stack (PUSH_N [0, 0x7A]))],
   Jumpi),
  (78, [(78, Stack (PUSH_N [0])), (80, Dup 0), (81, Unknown 0xFD)], Terminal),
  (82, [(82, Pc JUMPDEST), (83, Info CALLVALUE), (84, Arith ISZERO), (85, Stack (PUSH_N [0, 0x5D]))],
   Jumpi),
  (89, [(89, Stack (PUSH_N [0])), (91, Dup 0), (92, Unknown 0xFD)], Terminal),
  (93, [(93, Pc JUMPDEST), (94, Stack (PUSH_N [0, 0x65])), (97, Stack (PUSH_N [0, 0x82]))], Jump),
  (101, [(101, Pc JUMPDEST), (102, Misc STOP)], Terminal),
  (103, [(103, Pc JUMPDEST), (104, Info CALLVALUE), (105, Arith ISZERO), (106, Stack (PUSH_N [0, 0x72]))],
   Jumpi),
  (110, [(110, Stack (PUSH_N [0])), (112, Dup 0), (113, Unknown 0xFD)], Terminal),
  (114, [(114, Pc JUMPDEST), (115, Stack (PUSH_N [0, 0x65])), (118, Stack (PUSH_N [0, 0xD3]))], Jump),
  (122, [(122, Pc JUMPDEST), (123, Stack (PUSH_N [0, 0x65])), (126, Stack (PUSH_N [1, 0x24]))], Jump),
  (130, [(130, Pc JUMPDEST), (131, Stack (PUSH_N [3])), (133, Storage SLOAD), (134, Arith ISZERO),
         (135, Dup 0), (136, Arith ISZERO), (137, Stack (PUSH_N [0, 0xAD]))],
   Jumpi),
  (141, [(141, Stack POP), (142, Stack (PUSH_N [2])), (144, Storage SLOAD), (145, Info CALLER),
         (146, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (167, Swap 0), (168, Dup 1), (169, Bits inst_AND), (170, Swap 1), (171, Bits inst_AND),
         (172, Arith inst_EQ)],
   Next),
  (173, [(173, Pc JUMPDEST), (174, Arith ISZERO), (175, Arith ISZERO), (176, Stack (PUSH_N [0, 0xB8]))],
   Jumpi),
  (180, [(180, Stack (PUSH_N [0])), (182, Dup 0), (183, Unknown 0xFD)], Terminal),
  (184, [(184, Pc JUMPDEST), (185, Stack (PUSH_N [1])), (187, Storage SLOAD),
         (188, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (209, Bits inst_AND), (210, Misc SUICIDE)],
   Terminal),
  (211, [(211, Pc JUMPDEST), (212, Stack (PUSH_N [3])), (214, Storage SLOAD), (215, Arith ISZERO),
         (216, Dup 0), (217, Arith ISZERO), (218, Stack (PUSH_N [0, 0xFE]))],
   Jumpi),
  (222, [(222, Stack POP), (223, Stack (PUSH_N [2])), (225, Storage SLOAD), (226, Info CALLER),
         (227, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (248, Swap 0), (249, Dup 1), (250, Bits inst_AND), (251, Swap 1), (252, Bits inst_AND),
         (253, Arith inst_EQ)],
   Next),
  (254, [(254, Pc JUMPDEST), (255, Arith ISZERO), (256, Arith ISZERO), (257, Stack (PUSH_N [1, 9]))],
   Jumpi),
  (261, [(261, Stack (PUSH_N [0])), (263, Dup 0), (264, Unknown 0xFD)], Terminal),
  (265, [(265, Pc JUMPDEST), (266, Stack (PUSH_N [0])), (268, Storage SLOAD),
         (269, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (290, Bits inst_AND), (291, Misc SUICIDE)],
   Terminal),
  (292, [(292, Pc JUMPDEST), (293, Stack (PUSH_N [0])), (295, Stack (PUSH_N [3])), (297, Storage SLOAD),
         (298, Arith inst_GT), (299, Dup 0), (300, Arith ISZERO), (301, Stack (PUSH_N [1, 0x37]))],
   Jumpi),
  (305, [(305, Stack POP), (306, Stack (PUSH_N [3])), (308, Storage SLOAD), (309, Info CALLVALUE),
         (310, Arith inst_EQ)],
   Next),
  (311, [(311, Pc JUMPDEST), (312, Dup 0), (313, Arith ISZERO), (314, Stack (PUSH_N [1, 0x5E]))], Jumpi),
  (318, [(318, Stack POP), (319, Stack (PUSH_N [0])), (321, Storage SLOAD), (322, Info CALLER),
         (323, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (344, Swap 0), (345, Dup 1), (346, Bits inst_AND), (347, Swap 1), (348, Bits inst_AND),
         (349, Arith inst_EQ)],
   Next),
  (350, [(350, Pc JUMPDEST), (351, Arith ISZERO), (352, Arith ISZERO), (353, Stack (PUSH_N [1, 0x69]))],
   Jumpi),
  (357, [(357, Stack (PUSH_N [0])), (359, Dup 0), (360, Unknown 0xFD)], Terminal),
  (361, [(361, Pc JUMPDEST), (362, Stack (PUSH_N [0])), (364, Stack (PUSH_N [3])), (366, Storage SSTORE)],
   Jump),
  (368, [(368, Misc STOP)], Terminal),
  (369, [(369, Log LOG1), (370, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])), (377, Arith SHA3),
         (378, Unknown 0x29)],
   Terminal),
  (379, [(379, Misc CALLCODE)], Terminal), (380, [(380, Misc RETURN)], Terminal),
  (381, [(381, Dup 0xB)], Next), (382, [(382, Pc JUMPDEST), (383, Dup 4), (384, Unknown 0xC1)], Terminal),
  (385, [(385, Unknown 0xC5)], Terminal), (386, [(386, Unknown 0x5E)], Terminal),
  (387, [(387, Swap 1), (388, Unknown 0xAA)], Terminal), (389, [(389, Unknown 0xCA)], Terminal),
  (390, [(390, Unknown 0x3D)], Terminal),
  (391, [(391, Swap 3), (392, Stack (PUSH_N [0xE6, 0x35, 0xC8])), (396, Dup 0xA), (397, Unknown 0xD7)],
   Terminal),
  (398, [(398, Unknown 0xE3)], Terminal), (399, [(399, Unknown 0xBE)], Terminal),
  (400, [(400, Unknown 0x21)], Terminal),
  (401, [(401, Stack (PUSH_N [0x71, 0x83, 0xF3, 0xCC, 0xCE, 0xE1, 0xAE, 0xD4, 0, 0x29]))], Next)]"
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
   memory_usage 0 ** continuing ** gas_pred 100000
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
   apply (clarsimp)
   apply (rule conjI)
   apply (clarsimp simp: word_rcat_simps)
 (* write simp rules to put stack in first pos *)
  apply (sep_select 7)
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
   apply (split_conds)
(*1*)
  apply (case_tac " hash = refund_hash"; clarsimp)
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
   apply (split_conds)
  apply (rule exI)
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
   apply ((block_vcg2)[1])
  done
end
