theory Wallet

imports
  "../Parse"
  "../Hoare/HoareTripleForBasicBlocks"
  "./ToyExamplesBlocks"
  "../Word_Lib/Word_Lemmas_32"
begin
(*
pragma solidity ^0.4.0;
contract Wallet {

    uint256 balance;
    address owner;

    function Wallet() public {
            balance = 0;
            owner = msg.sender;
    }

    function addfund() payable public returns (uint256) {
        require (msg.sender == owner);
        balance += msg.value;
        return balance;
    }

    function withdraw() public {
        require (msg.sender == owner);
        selfdestruct(owner);
    }
}

Compiled with:
 solc --overwrite -o wallet-data --bin-runtime --asm --hashes wallet.sol

8f9595d4: addfund()
3ccfd60b: withdraw()

*)
value"(parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ccfd60b146100485780638f9595d41461005d57600080fd5b341561005357600080fd5b61005b61007b565b005b610065610112565b6040518082815260200191505060405180910390f35b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156100d757600080fd5b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff5b6000600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561017057600080fd5b3460008082825401925050819055506000549050905600a165627a7a7230582059db8450799f53c1abb1b9ef52ddf2a321e908f3226fb5b962e230f25dfa14ec0029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Swap 0, Arith DIV, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Bits inst_AND, Dup 0,
  Stack (PUSH_N [0x3C, 0xCF, 0xD6, 0xB]), Arith inst_EQ, Stack (PUSH_N [0, 0x48]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4]), Arith inst_EQ, Stack (PUSH_N [0, 0x5D]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [0, 0x53]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x5B]), Stack (PUSH_N [0, 0x7B]), Pc JUMP, Pc JUMPDEST, Misc STOP, Pc JUMPDEST,
  Stack (PUSH_N [0, 0x65]), Stack (PUSH_N [1, 0x12]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0x40]),
  Memory MLOAD, Dup 0, Dup 2, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD, Swap 1, Stack POP,
  Stack POP, Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST,
  Stack (PUSH_N [1]), Stack (PUSH_N [0]), Swap 0, Storage SLOAD, Swap 0, Stack (PUSH_N [1, 0]), Arith EXP,
  Swap 0, Arith DIV,
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
  Bits inst_AND, Arith inst_EQ, Arith ISZERO, Arith ISZERO, Stack (PUSH_N [0, 0xD7]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [1]), Stack (PUSH_N [0]), Swap 0,
  Storage SLOAD, Swap 0, Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [0]), Stack (PUSH_N [1]), Stack (PUSH_N [0]),
  Swap 0, Storage SLOAD, Swap 0, Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
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
  Bits inst_AND, Arith inst_EQ, Arith ISZERO, Arith ISZERO, Stack (PUSH_N [1, 0x70]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Stack (PUSH_N [0]), Dup 0, Dup 2,
  Dup 2, Storage SLOAD, Arith ADD, Swap 2, Stack POP, Stack POP, Dup 1, Swap 0, Storage SSTORE, Stack POP,
  Stack (PUSH_N [0]), Storage SLOAD, Swap 0, Stack POP, Swap 0, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Memory MSIZE, Unknown 0xDB, Dup 4,
  Stack POP,
  Stack (PUSH_N
          [0x9F, 0x53, 0xC1, 0xAB, 0xB1, 0xB9, 0xEF, 0x52, 0xDD, 0xF2, 0xA3, 0x21, 0xE9, 8, 0xF3, 0x22, 0x6F,
           0xB5, 0xB9, 0x62, 0xE2, 0x30, 0xF2, 0x5D, 0xFA, 0x14]),
  Unknown 0xEC, Misc STOP, Unknown 0x29]"
(* 159 instructions *)

lemma
 "parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ccfd60b146100485780638f9595d41461005d57600080fd5b341561005357600080fd5b61005b61007b565b005b610065610112565b6040518082815260200191505060405180910390f35b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156100d757600080fd5b600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16ff5b6000600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561017057600080fd5b3460008082825401925050819055506000549050905600a165627a7a7230582059db8450799f53c1abb1b9ef52ddf2a321e908f3226fb5b962e230f25dfa14ec0029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_wallet == build_blocks insts_ex"
definition addfund_hash :: "32 word"  where
 "addfund_hash = 0x8f9595d4"

definition withdraw_hash :: "32 word"  where
 "withdraw_hash = 0x8f9595d4"

definition
 "contract_fail \<equiv> ContractFail [ShouldNotHappen]"

definition return_action ::"address \<Rightarrow> address \<Rightarrow> 32 word \<Rightarrow> 256 word \<Rightarrow> contract_action" where
  "return_action sender owner hash new_balance = 
 (if hash = addfund_hash \<and> sender = owner then
    ContractReturn (word_rsplit (new_balance::w256))
  else if hash = withdraw_hash \<and> sender = owner then
    ContractSuicide owner
  else contract_fail)"

definition return_storage ::"address \<Rightarrow> address \<Rightarrow> 32 word \<Rightarrow> 256 word \<Rightarrow> contract_action" where
  "return_storage sender owner hash new_balance = 
 (if hash = addfund_hash \<and> sender = owner then
    ContractReturn (word_rsplit (new_balance::w256))
  else if hash = withdraw_hash \<and> sender = owner then
    ContractSuicide owner
  else contract_fail)"


lemma verify_wallet_return:
shows
"\<exists>r. triple 
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (hash::32 word)::byte list))
   ** sent_value v ** caller sender **
   memory_usage 0 ** continuing ** gas_pred 3000 ** storage 0 cur_balance ** storage 1 (ucast owner) ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_wallet (action (return_action sender owner hash (v + cur_balance)) ** r)"
  apply(simp add: return_action_def blocks_simps triple_def addfund_hash_def withdraw_hash_def)

  oops

lemma verify_wallet_storage:
assumes owner_not_sender: "owner \<noteq> sender"
shows
"\<exists>r. triple 
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (hash::32 word)::byte list))
   ** sent_value v ** caller sender **
   memory_usage 0 ** continuing ** gas_pred 3000 ** storage 0 cur_balance ** storage 1 (ucast owner) ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word) **
   memory (word_rcat [96::byte]) (word_rcat [y::byte]::256 word))
  blocks_wallet (storage 0 cur_balance ** r)"
  oops

end
