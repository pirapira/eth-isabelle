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

(*
lemma dlen : "parse_bytes deed_bytes = None"
using [[simp_trace = true]]
apply(simp)
*)


value "parse_bytes deed_bytes"

value [simp] "parse_bytes deed_bytes"

value [nbe] "parse_bytes deed_bytes"

definition parse_result :: "(inst list \<times> byte list) option"
where
parse_result_def[simplified]: "parse_result = parse_bytes deed_bytes"

definition deed_insts :: "inst list"
where
deed_insts_d [simplified, simp] : "deed_insts = fst (the parse_result)"

value[simp] deed_insts

definition deed_program :: "program"
where
"deed_program == program_of_lst deed_insts"

value deed_program

inductive deed_inv :: "account_state \<Rightarrow> bool"
where
" account_code a = deed_program \<Longrightarrow>
  deed_inv a
"

value "program_length deed_program"

(*
lemma dlen : "program_length deed_program = 500"
using [[simp_trace = true]]

apply(simp)

oops
*)
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
  apply(case_tac steps; auto)
  apply(simp only: parse_result_def)
  

oops

end
