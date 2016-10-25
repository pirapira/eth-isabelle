section {* Verification of the Deed Contract *}

theory Deed

imports Main "../RelationalSem"

begin

subsection {* The code under verification. *}

text {*  The code under verification comes from these commits:
\begin{verbatim}
ens: f3334337083728728da56824a5d0a30a8712b60c
solidity: 2d9109ba453d49547778c39a506b0ed492305c16
\end{verbatim}
and is produced with this command.
\begin{verbatim}
$ solc/solc --bin-runtime
\end{verbatim}

The hex code looks like this\\
\texttt{6060604052361561006c5760e060020a6000350463...}

I parsed this hex code in a Ruby parser\footnote{Available in \url{https://github.com/piraira/eth-isabelle}}
and obtained the following list of instructions.
*}

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
Pc JUMP #
[]
"

declare deed_insts_def [simp]

text {* The next definition translates the list of instructions into an AVL tree.
This single step takes around 10 minutes.  So I need a program that takes a hex code
and produces a binary tree literal in Isabelle/HOL.*} 

definition content_compiled :: "(int * inst, nat) tree"
where
content_compiled_def [simplified] : "content_compiled == program_content_of_lst 0 deed_insts"

text {* The program that appears in the statements of the following lemmata is defined here.
*}

definition deed_program :: "program"
where
deed_program_def: "deed_program =
  \<lparr> program_content = content_compiled
  , program_length = int (length deed_insts)
  , program_annotation = program_annotation_of_lst 0 deed_insts
  \<rparr>"
  
subsection {* The Invariant *}

text {* The invariant is simple.  The code of the account is either the one defined above or empty.
We have to allow the empty case because this contract might destroy itself. *}

inductive deed_inv :: "account_state \<Rightarrow> bool"
where
alive: " account_code a = deed_program \<Longrightarrow>
  deed_inv a
"
| dead: "account_code a = empty_program \<Longrightarrow> deed_inv a"

text {* The program length lookup is optimized. *}

lemma prolen [simp] : "program_length deed_program = 500"
apply(simp add: deed_program_def)
done

text {* The program annotation lookup is also optimized.
There are no annotations in the program under verification.
*}
lemma proanno [simp] : "program_annotation deed_program n = []"
apply(simp add: deed_program_def)
done

text {* Here, a term called @{term x} is defined.  @{term x} is
by definition equal to the binary tree containing the program,
and its definition can be expanded automatically during the proofs.
*}

declare content_compiled_def [simp]

definition x :: "(int * inst, nat) tree"
where x_def [simplified] :"x == content_compiled"

declare content_compiled_def [simp del]

declare deed_program_def [simp del]

text {* Whenever the content of the program is being looked up,
the term @{term x} appears, allowing further expansion.  Otherwise,
@{term "program_content deed_program"} stays as just two words.
This makes sure that the intermediate goals do not contain the
big binary tree as a literal.
*}
lemma pro_content [simp]: "lookup (program_content deed_program) n == lookup x n"
apply(simp add: deed_program_def add: x_def add: content_compiled_def)
done

declare deed_insts_def [simp del]
declare bin_cat_def [simp]

lemma strict_if_split :
"P (strict_if b A B) =
 (\<not> (b \<and> \<not> P (A True) \<or> \<not> b \<and> \<not> P (B True)))"
apply(case_tac b; auto)
done

declare deed_inv.simps [simp]
        one_round.simps [simp]
        world_turn.simps [simp]
        contract_turn.simps [simp]
        x_def [simp]

subsection {* Proof that the Invariant is Kept *}

text {* The following lemma states that, if the account's code is either empty or the
Deed contract's code, that is still the case after an invocation.  *}
        
lemma deed_keeps_invariant :
"no_assertion_failure deed_inv"
apply(simp only: no_assertion_failure_def)
apply(rule allI)
apply(rule allI)
apply(rule impI)
apply(rule impI)
apply(rule allI)
apply(rule impI)
apply(drule star_case; auto)
     apply(case_tac steps; auto)
     apply(split if_splits; auto)
     apply(split strict_if_split; auto)
     apply(split strict_if_split; auto)
    apply(case_tac steps; auto)
    apply(split strict_if_split; auto)
    apply(split strict_if_split; auto)
    apply(split strict_if_split; auto)
   apply(case_tac steps; auto)
   apply(split strict_if_split; auto)
   apply(split strict_if_split; auto)
   apply(split strict_if_split; auto)
  apply(case_tac steps; auto)
 apply(case_tac steps; auto)
apply(case_tac steps; auto)
done


subsection {* Proof about the Case when the Caller is Not the Registrar *}

text {*
If 
\begin{itemize}
\item the caller is not equal to the address stored at index~0,
\item the sent value does not overflow the account's balance,
\item the account is not marked for destruction at the time of invocation,
\item and the invariant holds at the time of invocation,
\end{itemize}
then, after the invocation,
\begin{itemize}
\item the invariant is still kept,
\item the balance of the acount is not smaller, and 
\item the account is still not marked for destruction.
\end{itemize}
*}

lemma deed_only_registrar_can_spend :
"pre_post_conditions deed_inv
 (\<lambda> init_state init_call. account_storage init_state 0 \<noteq> ucast (callenv_caller init_call)
 \<and> account_balance init_state + callenv_value init_call \<ge> account_balance init_state
 \<and> \<not> (account_killed init_state)
 )
 (\<lambda> init_state _ (post_state, _). account_balance init_state \<le> account_balance post_state
 \<and> \<not> (account_killed post_state))
"
apply(simp add: pre_post_conditions_def; auto)
         apply(drule star_case; auto)
          apply(case_tac steps; auto)
          apply(split strict_if_split; auto)
          apply(split strict_if_split; auto)
          apply(split strict_if_split; auto)
         apply(case_tac steps; auto)
         apply(split strict_if_split; auto)
         apply(split strict_if_split; auto)
         apply(split strict_if_split; auto)
        apply(drule star_case; auto)
        apply(case_tac steps; auto)
        apply(split strict_if_split; auto)
         apply(split strict_if_split; auto)
          apply(case_tac initial_account; simp)
         apply(split strict_if_split; auto)
          apply(case_tac initial_account; simp)
         apply(case_tac initial_account; simp)
        apply(case_tac initial_account;simp)
       apply(drule star_case; auto)
       apply(case_tac steps; auto)
       apply(split strict_if_split; auto)
        apply(split strict_if_split; auto)
         apply(case_tac initial_account; simp)
        apply(split strict_if_split; auto)
         apply(case_tac initial_account; simp)
        apply(case_tac initial_account;simp)
       apply(case_tac initial_account;simp)
      (* Initial state is not killed, but the final state might be killed? *)
      (* but that's not the case because the caller is not the registrar *)
      apply(drule star_case; auto)
      apply(case_tac steps; auto)
      apply(split strict_if_split; auto)
       apply(split strict_if_split; auto)
        apply(case_tac initial_account; simp)
       apply(split strict_if_split; auto)
        apply(case_tac initial_account; simp)
       apply(case_tac initial_account; simp)
      apply(case_tac initial_account; simp)
     apply(case_tac initial_account)
     apply(drule star_case; auto)
     apply(case_tac steps; auto)
     apply(split strict_if_split; auto)
     apply(split strict_if_split; auto)
     apply(split strict_if_split; auto)
    apply(case_tac initial_account)
    apply(drule star_case; auto)
    apply(case_tac steps; auto)
    apply(case_tac steps; auto)
   apply(drule star_case; auto)
   apply(case_tac steps; auto)
   apply(case_tac initial_account; auto)
  apply(drule star_case; auto)
  apply(case_tac steps; auto)
  apply(case_tac initial_account; auto)
 apply(case_tac initial_account; auto)
 apply(drule star_case; auto)
 apply(case_tac steps; auto)
apply(drule star_case; auto)
apply(case_tac steps; auto)
apply(case_tac initial_account; auto)
done

text {* It takes 15 minutes to compile this proof on my machine.  Most of the time is spent
translating the list of instructions into an AVL tree. *}

end
