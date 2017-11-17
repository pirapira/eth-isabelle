theory Escrow

imports
  "../Parse"
  "../Hoare/HoareTripleForBasicBlocks"
  "./ToyExamplesBlocks"
  "../Word_Lib/Word_Lemmas_32"
begin
(*
pragma solidity ^0.4.0;
contract EscrowWallet {

    address from;
    address to;
    address owner;

    function EscrowWallet(address _from, address _to) public {
            from = _from;
            to = _to;
            owner = msg.sender;
    }

    function addfund() payable public  {
        require (msg.sender == from);
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
 solc --overwrite -o escrow-data --bin-runtime --asm --hashes escrow.sol

8f9595d4: addfund()
1b9265b8: pay()
590e1ae3: refund()


*)
value"(parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680631b9265b814610053578063590e1ae3146100685780638f9595d41461007d57600080fd5b341561005e57600080fd5b610066610087565b005b341561007357600080fd5b61007b61011e565b005b6100856101b4565b005b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156100e357600080fd5b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff5b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561017a57600080fd5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561020f57600080fd5b5600a165627a7a72305820cd7938db5bada113de91ec979b4dca8fdcb3c616a00562a67f5c288a71c479d10029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Swap 0, Arith DIV, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Bits inst_AND, Dup 0,
  Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8]), Arith inst_EQ, Stack (PUSH_N [0, 0x53]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3]), Arith inst_EQ, Stack (PUSH_N [0, 0x68]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4]), Arith inst_EQ, Stack (PUSH_N [0, 0x7D]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [0, 0x5E]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x66]), Stack (PUSH_N [0, 0x87]), Pc JUMP, Pc JUMPDEST, Misc STOP, Pc JUMPDEST,
  Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x73]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Stack (PUSH_N [0, 0x7B]), Stack (PUSH_N [1, 0x1E]), Pc JUMP, Pc JUMPDEST, Misc STOP,
  Pc JUMPDEST, Stack (PUSH_N [0, 0x85]), Stack (PUSH_N [1, 0xB4]), Pc JUMP, Pc JUMPDEST, Misc STOP,
  Pc JUMPDEST, Stack (PUSH_N [2]), Stack (PUSH_N [0]), Swap 0, Storage SLOAD, Swap 0, Stack (PUSH_N [1, 0]),
  Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Arith inst_EQ, Arith ISZERO, Arith ISZERO, Stack (PUSH_N [0, 0xE3]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [1]), Stack (PUSH_N [0]), Swap 0,
  Storage SLOAD, Swap 0, Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [2]), Stack (PUSH_N [0]), Swap 0, Storage SLOAD,
  Swap 0, Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Arith inst_EQ, Arith ISZERO, Arith ISZERO, Stack (PUSH_N [1, 0x7A]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Swap 0, Storage SLOAD,
  Swap 0, Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Swap 0, Storage SLOAD, Swap 0,
  Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Arith inst_EQ, Arith ISZERO, Arith ISZERO, Stack (PUSH_N [2, 0xF]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Unknown 0xCD,
  Stack (PUSH_N
          [0x38, 0xDB, 0x5B, 0xAD, 0xA1, 0x13, 0xDE, 0x91, 0xEC, 0x97, 0x9B, 0x4D, 0xCA, 0x8F, 0xDC, 0xB3,
           0xC6, 0x16, 0xA0, 5, 0x62, 0xA6, 0x7F, 0x5C, 0x28, 0x8A]),
  Stack (PUSH_N [0xC4, 0x79, 0xD1, 0, 0x29])]"
(* 159 instructions *)

lemma
 "parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680631b9265b814610053578063590e1ae3146100685780638f9595d41461007d57600080fd5b341561005e57600080fd5b610066610087565b005b341561007357600080fd5b61007b61011e565b005b6100856101b4565b005b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156100e357600080fd5b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff5b600260009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561017a57600080fd5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561020f57600080fd5b5600a165627a7a72305820cd7938db5bada113de91ec979b4dca8fdcb3c616a00562a67f5c288a71c479d10029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_escrow == build_blocks insts_ex"
definition addfund_hash :: "32 word"  where
 "addfund_hash = 0x8f9595d4"

definition pay_hash :: "32 word"  where
 "pay_hash = 0x1b9265b8"

definition refund_hash :: "32 word"  where
 "refund_hash = 0x590e1ae3"

definition
 "contract_fail \<equiv> ContractFail [ShouldNotHappen]"

definition return_action ::"address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> 32 word \<Rightarrow> contract_action" where
  "return_action sender from to owner hash  = 
 (if hash = addfund_hash \<and> sender = from then
    ContractReturn []
  else if hash = refund_hash \<and> sender = owner then
    ContractSuicide from
  else if hash = pay_hash \<and> sender = owner then
    ContractSuicide to
  else contract_fail)"

lemma verify_escrow_return:
shows
"\<exists>r. triple 
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (hash::32 word)::byte list))
   ** sent_value v ** caller sender **
   memory_usage 0 ** continuing ** gas_pred 3000
   ** storage 0 (ucast from)
   ** storage 1 (ucast to)
   ** storage 2 (ucast owner)
   ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_escrow (action (return_action sender from to owner hash) ** r)"
  apply(simp add: return_action_def blocks_simps triple_def addfund_hash_def refund_hash_def pay_hash_def)

  oops

end
