theory Deed

imports Main "../Parse" "../RelationalSem"

begin

value bytes_of_hex_content

(*
ens: f3334337083728728da56824a5d0a30a8712b60c
solidity: 2d9109ba453d49547778c39a506b0ed492305c16

$ solc/solc --bin-runtime
*)
(*
abbreviation deed :: "char list"
where "deed == ''6060604052361561006c5760e060020a600035046305b34410811461006e5780630b5ab3d51461007c57806313af4035146100895780632b20e397146100af5780638da5cb5b146100c6578063bbe42771146100dd578063faab9d3914610103578063fb1669ca14610129575b005b346100025761014a60015481565b346100025761006c610189565b346100025761006c60043560005433600160a060020a039081169116146101f857610002565b34610002576101a0600054600160a060020a031681565b34610002576101a0600254600160a060020a031681565b346100025761006c60043560005433600160a060020a0390811691161461025757610002565b346100025761006c60043560005433600160a060020a039081169116146102c757610002565b61006c60043560005433600160a060020a039081169116146102e957610002565b60408051918252519081900360200190f35b6040517fbb2ce2f51803bba16bc85282b47deeea9a5c6223eabea1077be696b3f265cf1390600090a16102545b60025460a060020a900460ff16156101bd57610002565b60408051600160a060020a03929092168252519081900360200190f35b604051600254600160a060020a0390811691309091163180156108fc02916000818181858888f19350505050156101f35761deadff5b610002565b6002805473ffffffffffffffffffffffffffffffffffffffff19168217905560408051600160a060020a038316815290517fa2ea9883a321a3e97b8266c2b078bfeec6d50c711ed71f874a90d500ae2eaf369181900360200190a15b50565b60025460a060020a900460ff16151561026f57610002565b6002805474ff00000000000000000000000000000000000000001916905560405161dead906103e830600160a060020a031631848203020480156108fc02916000818181858888f19350505050151561015c57610002565b6000805473ffffffffffffffffffffffffffffffffffffffff19168217905550565b60025460a060020a900460ff16151561030157610002565b8030600160a060020a031631101561031857610002565b600254604051600160a060020a039182169130163183900380156108fc02916000818181858888f1935050505015156102545761000256''"
*)

abbreviation deed :: "char list"
where "deed == ''6060604052361561006c5760e060020a600035046305b34410811461006e5780630b5ab3d51461007c57806313af4035146100895780632b20e397146100af5780638da5cb5b146100c6578063bbe42771146100dd5780''"


definition deed_bytes :: "byte list"
where deed_b [simplified, simp]: "deed_bytes == bytes_of_hex_content deed"

value [simp] "deed_bytes"

definition deed_insts :: "inst list"
where "deed_insts =
Stack (PUSH_N [0x60]) #
Stack (PUSH_N [0x40]) #
Memory MSTORE #
Info CALLDATASIZE #
Arith ISZERO #
Stack (PUSH_N [0x00, 0x6c]) #
Pc JUMPI #
Stack (PUSH_N [0xe0]) #
Stack (PUSH_N [0x02]) #
(*
Arith EXP #
Stack (PUSH_N [0x00]) #
Stack CALLDATALOAD #
Arith DIV #
Stack (PUSH_N [0x05, 0xb3, 0x44, 0x10]) #
Dup 2 #
Arith inst_EQ #
Stack (PUSH_N [0x00, 0x6e]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0x0b, 0x5a, 0xb3, 0xd5]) #
Arith inst_EQ #
Stack (PUSH_N [0x00, 0x7c]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0x13, 0xaf, 0x40, 0x35]) #
Arith inst_EQ #
Stack (PUSH_N [0x00, 0x89]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0x2b, 0x20, 0xe3, 0x97]) #
Arith inst_EQ #
Stack (PUSH_N [0x00, 0xaf]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0x8d, 0xa5, 0xcb, 0x5b]) #
Arith inst_EQ #
Stack (PUSH_N [0x00, 0xc6]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0xbb, 0xe4, 0x27, 0x71]) #
Arith inst_EQ #
Stack (PUSH_N [0x00, 0xdd]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0xfa, 0xab, 0x9d, 0x39]) #
Arith inst_EQ #
Stack (PUSH_N [0x01, 0x03]) #
Pc JUMPI #
Dup 1 #
Stack (PUSH_N [0xfb, 0x16, 0x69, 0xca]) #
Arith inst_EQ #
Stack (PUSH_N [0x01, 0x29]) #
Pc JUMPI #
Pc JUMPDEST #
Misc STOP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x01, 0x4a]) #
Stack (PUSH_N [0x01]) #
Storage SLOAD #
Dup 2 #
Pc JUMP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x6c]) #
Stack (PUSH_N [0x01, 0x89]) #
Pc JUMP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x6c]) #
Stack (PUSH_N [0x04]) #
Stack CALLDATALOAD #
Stack (PUSH_N [0x00]) #
Storage SLOAD #
Info CALLER #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 1 #
Dup 2 #
Bits inst_AND #
Swap 2 #
Bits inst_AND #
Arith inst_EQ #
Stack (PUSH_N [0x01, 0xf8]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x01, 0xa0]) #
Stack (PUSH_N [0x00]) #
Storage SLOAD #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Bits inst_AND #
Dup 2 #
Pc JUMP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x01, 0xa0]) #
Stack (PUSH_N [0x02]) #
Storage SLOAD #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Bits inst_AND #
Dup 2 #
Pc JUMP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x6c]) #
Stack (PUSH_N [0x04]) #
Stack CALLDATALOAD #
Stack (PUSH_N [0x00]) #
Storage SLOAD #
Info CALLER #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 1 #
Dup 2 #
Bits inst_AND #
Swap 2 #
Bits inst_AND #
Arith inst_EQ #
Stack (PUSH_N [0x02, 0x57]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Info CALLVALUE #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x6c]) #
Stack (PUSH_N [0x04]) #
Stack CALLDATALOAD #
Stack (PUSH_N [0x00]) #
Storage SLOAD #
Info CALLER #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 1 #
Dup 2 #
Bits inst_AND #
Swap 2 #
Bits inst_AND #
Arith inst_EQ #
Stack (PUSH_N [0x02, 0xc7]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x00, 0x6c]) #
Stack (PUSH_N [0x04]) #
Stack CALLDATALOAD #
Stack (PUSH_N [0x00]) #
Storage SLOAD #
Info CALLER #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 1 #
Dup 2 #
Bits inst_AND #
Swap 2 #
Bits inst_AND #
Arith inst_EQ #
Stack (PUSH_N [0x02, 0xe9]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x40]) #
Dup 1 #
Memory MLOAD #
Swap 2 #
Dup 3 #
Memory MSTORE #
Memory MLOAD #
Swap 1 #
Dup 2 #
Swap 1 #
Arith SUB #
Stack (PUSH_N [0x20]) #
Arith ADD #
Swap 1 #
Misc RETURN #
Pc JUMPDEST #
Stack (PUSH_N [0x40]) #
Memory MLOAD #
Stack (PUSH_N [0xbb, 0x2c, 0xe2, 0xf5, 0x18, 0x03, 0xbb, 0xa1, 0x6b, 0xc8, 0x52, 0x82, 0xb4, 0x7d, 0xee, 0xea, 0x9a, 0x5c, 0x62, 0x23, 0xea, 0xbe, 0xa1, 0x07, 0x7b, 0xe6, 0x96, 0xb3, 0xf2, 0x65, 0xcf, 0x13]) #
Swap 1 #
Stack (PUSH_N [0x00]) #
Swap 1 #
Log LOG1 #
Stack (PUSH_N [0x02, 0x54]) #
Pc JUMPDEST #
Stack (PUSH_N [0x02]) #
Storage SLOAD #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Swap 1 #
Arith DIV #
Stack (PUSH_N [0xff]) #
Bits inst_AND #
Arith ISZERO #
Stack (PUSH_N [0x01, 0xbd]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x40]) #
Dup 1 #
Memory MLOAD #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 3 #
Swap 1 #
Swap 3 #
Bits inst_AND #
Dup 3 #
Memory MSTORE #
Memory MLOAD #
Swap 1 #
Dup 2 #
Swap 1 #
Arith SUB #
Stack (PUSH_N [0x20]) #
Arith ADD #
Swap 1 #
Misc RETURN #
Pc JUMPDEST #
Stack (PUSH_N [0x40]) #
Memory MLOAD #
Stack (PUSH_N [0x02]) #
Storage SLOAD #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 1 #
Dup 2 #
Bits inst_AND #
Swap 2 #
Info ADDRESS #
Swap 1 #
Swap 2 #
Bits inst_AND #
Info BALANCE #
Dup 1 #
Arith ISZERO #
Stack (PUSH_N [0x08, 0xfc]) #
Arith MUL #
Swap 2 #
Stack (PUSH_N [0x00]) #
Dup 2 #
Dup 2 #
Dup 2 #
Dup 6 #
Dup 9 #
Dup 9 #
Misc CALL #
Swap 4 #
Stack POP #
Stack POP #
Stack POP #
Stack POP #
Arith ISZERO #
Stack (PUSH_N [0x01, 0xf3]) #
Pc JUMPI #
Stack (PUSH_N [0xde, 0xad]) #
Misc SUICIDE #
Pc JUMPDEST #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x02]) #
Dup 1 #
Storage SLOAD #
Stack (PUSH_N [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) #
Bits inst_NOT #
Bits inst_AND #
Dup 3 #
Bits inst_OR #
Swap 1 #
Storage SSTORE #
Stack (PUSH_N [0x40]) #
Dup 1 #
Memory MLOAD #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Dup 4 #
Bits inst_AND #
Dup 2 #
Memory MSTORE #
Swap 1 #
Memory MLOAD #
Stack (PUSH_N [0xa2, 0xea, 0x98, 0x83, 0xa3, 0x21, 0xa3, 0xe9, 0x7b, 0x82, 0x66, 0xc2, 0xb0, 0x78, 0xbf, 0xee, 0xc6, 0xd5, 0x0c, 0x71, 0x1e, 0xd7, 0x1f, 0x87, 0x4a, 0x90, 0xd5, 0x00, 0xae, 0x2e, 0xaf, 0x36]) #
Swap 2 #
Dup 2 #
Swap 1 #
Arith SUB #
Stack (PUSH_N [0x20]) #
Arith ADD #
Swap 1 #
Log LOG1 #
Pc JUMPDEST #
Stack POP #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x02]) #
Storage SLOAD #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Swap 1 #
Arith DIV #
Stack (PUSH_N [0xff]) #
Bits inst_AND #
Arith ISZERO #
Arith ISZERO #
Stack (PUSH_N [0x02, 0x6f]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x02]) #
Dup 1 #
Storage SLOAD #
Stack (PUSH_N [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) #
Bits inst_NOT #
Bits inst_AND #
Swap 1 #
Storage SSTORE #
Stack (PUSH_N [0x40]) #
Memory MLOAD #
Stack (PUSH_N [0xde, 0xad]) #
Swap 1 #
Stack (PUSH_N [0x03, 0xe8]) #
Info ADDRESS #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Bits inst_AND #
Info BALANCE #
Dup 5 #
Dup 3 #
Arith SUB #
Arith MUL #
Arith DIV #
Dup 1 #
Arith ISZERO #
Stack (PUSH_N [0x08, 0xfc]) #
Arith MUL #
Swap 2 #
Stack (PUSH_N [0x00]) #
Dup 2 #
Dup 2 #
Dup 2 #
Dup 6 #
Dup 9 #
Dup 9 #
Misc CALL #
Swap 4 #
Stack POP #
Stack POP #
Stack POP #
Stack POP #
Arith ISZERO #
Arith ISZERO #
Stack (PUSH_N [0x01, 0x5c]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x00]) #
Dup 1 #
Storage SLOAD #
Stack (PUSH_N [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) #
Bits inst_NOT #
Bits inst_AND #
Dup 3 #
Bits inst_OR #
Swap 1 #
Storage SSTORE #
Stack POP #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x02]) #
Storage SLOAD #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Swap 1 #
Arith DIV #
Stack (PUSH_N [0xff]) #
Bits inst_AND #
Arith ISZERO #
Arith ISZERO #
Stack (PUSH_N [0x03, 0x01]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Dup 1 #
Info ADDRESS #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Bits inst_AND #
Info BALANCE #
Arith inst_LT #
Arith ISZERO #
Stack (PUSH_N [0x03, 0x18]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP #
Pc JUMPDEST #
Stack (PUSH_N [0x02]) #
Storage SLOAD #
Stack (PUSH_N [0x40]) #
Memory MLOAD #
Stack (PUSH_N [0x01]) #
Stack (PUSH_N [0xa0]) #
Stack (PUSH_N [0x02]) #
Arith EXP #
Arith SUB #
Swap 2 #
Dup 3 #
Bits inst_AND #
Swap 2 #
Info ADDRESS #
Bits inst_AND #
Info BALANCE #
Dup 4 #
Swap 1 #
Arith SUB #
Dup 1 #
Arith ISZERO #
Stack (PUSH_N [0x08, 0xfc]) #
Arith MUL #
Swap 2 #
Stack (PUSH_N [0x00]) #
Dup 2 #
Dup 2 #
Dup 2 #
Dup 6 #
Dup 9 #
Dup 9 #
Misc CALL #
Swap 4 #
Stack POP #
Stack POP #
Stack POP #
Stack POP #
Arith ISZERO #
Arith ISZERO #
Stack (PUSH_N [0x02, 0x54]) #
Pc JUMPI #
Stack (PUSH_N [0x00, 0x02]) #
Pc JUMP # *)
[]
"

declare deed_insts_def [simp]


lemma test : "program_content (program_of_lst deed_insts) = Leaf"
using [[simp_trace_new interactive mode = full]]

apply(simp)


definition deed_program :: "program"
where
deed_program_def [simplified] : "deed_program = program_of_lst deed_insts"
(* half: 12: 42 -- *)

(* 12:37 -- *)

(* maybe this computation can also be done offline *)

(*
declare deed_program_def [simp]
*)

inductive deed_inv :: "account_state \<Rightarrow> bool"
where
" account_code a = deed_program \<Longrightarrow>
  deed_inv a
"

value [simp] "program_length deed_program"

lemma prolen [simp] : "program_length deed_program = 500"
apply(simp add: deed_program_def)
done

lemma proanno [simp] : "program_annotation deed_program n = []"
apply(simp add: deed_program_def)
done

definition content_compiled :: "(int * inst, nat) tree"
where
content_compiled_def [simp] : "content_compiled == program_content_of_lst 0 deed_insts"

definition x :: "(int * inst, nat) tree"
where x_def [simplified] :"x == content_compiled"

value [simp] x

(* I want to make sure this rule can be invoked only on n being fully simplified *)
lemma pro_content [simp]: "lookup (program_content deed_program) n == lookup x n"
apply(simp add: deed_program_def add: x_def)
done

declare deed_insts_def [simp del]

(* without this, it is impossible to jump to a word *)
declare bin_cat_def [simp]

lemma deed_keeps_invariant :
"no_assertion_failure deed_inv"
apply(simp only: no_assertion_failure_def)
apply(rule allI)
apply(rule impI)
apply(rule impI)
apply(rule allI)
apply(rule impI)
apply(drule star_case; auto)
 apply(simp only: deed_inv.simps; auto)
 apply(simp add: one_step.simps; auto)
 apply(simp add: world_turn.simps; auto)
 apply(drule star_case; auto)
  apply(simp add: contract_turn.simps; auto)
(*  using [[simp_trace = true]] *)
(*  using [[simp_trace_new mode = normal]] *)
  apply(case_tac steps; simp add: x_def)
  
  
  
  (*
  apply(split if_splits; simp) (* this takes around 15 minutes *)
   (* how to disable congruence rule in cases *)
  apply(split if_splits; simp)
   apply(case_tac "callenv_value callargs = 0") (* TODO: create an issue about if_splits tactic not working *)
    apply(simp)
    (* I'm seeing a large program. followed by venv_pc v_env *)
    (* The PC is specified as a hex value, so this has to be reduced *)
    (* The venv is defined in a let, which is a bit awkward *)
  
  
  
  
  
  
  
  
   (* maybe the term for the memory is too big *)
   (* maybe try to compile the basic block into a big function *)
  
*)
oops

end
