section {* What can Happen during a Contract Invocation *}

text {* This section defines a set of sequence of account states that can appeear during an
invocation of a countract.  The invocation can be a nested reentrancy, but we focus on one
invocation.  This means we do not look into details of further reentrancy, but just assume 
that the inner reentrancy keeps the invariant of the contract.  Of course we need to prove
that the invariant holds for the code, but when we do that we can assume that the inner
nested calls keep the invariants (we can say we are doing mathematical induction on the depth
of reentrancy).  *}

theory RelationalSem

imports Main "./ContractSem"

begin

subsection {* Some Possible Changes on Our Account State *}

text {* The account state might change even when the account's code is not executing. *}

text {* During blocks, the account might gain balances because somebody mines 
Ether for the account.  The balance might increase also while other contracts execute
because they might destroy themselves and send their balance to our account.
The following relation captures this possibility.
*}

text {* When a transaction finishes, if our contract is marked as killed, it is destroyed. *}

inductive account_state_natural_change :: "account_state \<Rightarrow> account_state \<Rightarrow> bool"
where
natural:
 "old_bal \<le> new_bal \<Longrightarrow>
  account_state_natural_change
   \<lparr> account_address = addr
   , account_storage = str
   , account_code = code
   , account_balance = old_bal
   , account_ongoing_calls = going
   , account_killed = killed
   \<rparr>
   \<lparr> account_address = addr
   , account_storage = str
   , account_code = code
   , account_balance = new_bal
   , account_ongoing_calls = going
   , account_killed = killed
   \<rparr>"
| cleaned: -- {* This happens only at the end of a transaction, but we don't know
              the transaction boundaries.  
              So this can happen at any moment when there are no ongoing calls.  *}
  "account_state_natural_change
  \<lparr> account_address = addr
  , account_storage = str
  , account_code = code
  , account_balance = old_bal
  , account_ongoing_calls = []
  , account_killed = True
  \<rparr>
  (empty_account addr)"

declare account_state_natural_change.simps [simp]

text "When the execution comes back from an external call, the account state might have changed
arbitrariliy.  Our strategy is to assume that an invariant is kept here; and later prove that
the invariant actually holds."

inductive account_state_return_change :: "(account_state \<Rightarrow> bool) \<Rightarrow> account_state \<Rightarrow> account_state \<Rightarrow> bool"
where
account_return:
"invariant
 \<lparr> account_address = addr
 , account_storage = new_str
 , account_code = code
 , account_balance = new_bal
 , account_ongoing_calls = ongoing
 , account_killed = killed
 \<rparr>
 \<Longrightarrow>
 account_state_return_change invariant
 \<lparr> account_address = addr
 , account_storage = old_str
 , account_code = code
 , account_balance = old_bal
 , account_ongoing_calls = ongoing
 , account_killed = killed
 \<rparr>
 \<lparr> account_address = addr
 , account_storage = new_str
 , account_code = code
 , account_balance = new_bal
 , account_ongoing_calls = ongoing
 , account_killed = killed
 \<rparr>
 "

declare account_state_return_change.simps [simp]

text "Next we specify which program results might see a return."

fun returnable_result :: "program_result \<Rightarrow> bool"
where
  "returnable_result ProgramStepRunOut = False"
| "returnable_result (ProgramToWorld (ContractCall _, _, _, _)) = True"
| "returnable_result (ProgramToWorld (ContractCreate _, _, _, _)) = True"
| "returnable_result (ProgramToWorld (ContractSuicide, _, _, _)) = False"
| "returnable_result (ProgramToWorld (ContractFail, _, _, _)) = False"
  (* because we are not modeling nested calls here, the effect of the nested calls are modeled in
   * account_state_return_change *)
| "returnable_result (ProgramToWorld (ContractReturn _, _, _, _)) = False"
| "returnable_result (ProgramInit _) = False"
| "returnable_result ProgramInvalid = False"
| "returnable_result ProgramAnnotationFailure = False"

subsection {* A Round of the Game *}

text {* Now we are ready to specify the worlds turn. *}

inductive world_turn :: "(account_state \<Rightarrow> bool) (* The invariant of our contract*)
                      \<Rightarrow> (account_state * program_result)
                         (* the account state before the world's move
                            and the last thing our account did *)
                      \<Rightarrow> (account_state * variable_env)
                         (* the account state after the world's move
                            and the variable environment from which our contract must start.
                          *)
                      \<Rightarrow> bool (* a boolean indicating if that is a possible world's move. *)"
where
  world_call: -- {* the world might call our contract. *}
  "
   build_venv_called old_state callargs next_venv \<Longrightarrow>
   world_turn I (old_state, ProgramInit callargs) (old_state, next_venv)"
| world_return: -- {* the world might return to our contract. *}
  "account_state_return_change I account_state_going_out account_state_back \<Longrightarrow>
   build_venv_returned account_state_back result new_v \<Longrightarrow>
   returnable_result program_r \<Longrightarrow>
   world_turn I (account_state_going_out, program_r)
                (account_state_pop_ongoing_call account_state_back, new_v)"
| world_fail: -- {* the world might fail from an account into our contract. *}
  "account_state_return_change I account_state_going_out account_state_back \<Longrightarrow>
   build_venv_failed account_state_back = Some new_v \<Longrightarrow>
   returnable_result result \<Longrightarrow>
   world_turn I (account_state_going_out, result)
                (account_state_pop_ongoing_call account_state_back, new_v)"

text {* As a reply, our contract might make a move, or report an annotation failure.*}

inductive contract_turn :: "(account_state * variable_env) \<Rightarrow> (account_state * program_result) \<Rightarrow> bool"
where
  contract_to_world:
  "build_cenv old_account = cenv \<Longrightarrow>
   program_sem old_venv cenv 
      (program_length (cenv_program cenv)) steps
      = ProgramToWorld (act, st, bal, opt_v) \<Longrightarrow> (* if the program behaves like this *)
   account_state_going_out (* and if the account state is updated like this*)
     = update_account_state old_account act st bal opt_v \<Longrightarrow>
   contract_turn (old_account, old_venv) (* the contract can change the account state like this. *)
      (account_state_going_out, ProgramToWorld (act, st, bal, opt_v))"
| contract_annotation_failure:
  "build_cenv old_account = cenv \<Longrightarrow>
   program_sem old_venv cenv
      (program_length (cenv_program cenv)) steps = ProgramAnnotationFailure \<Longrightarrow>
   contract_turn (old_account, old_venv) (old_account, ProgramAnnotationFailure)"

text {* When we combine the world's turn and the contract's turn, we get one round.
The round is a binary relation over a single set.
*}

inductive one_round :: "(account_state \<Rightarrow> bool) \<Rightarrow> (account_state * program_result) \<Rightarrow> (account_state * program_result) \<Rightarrow> bool"
where
round:
"world_turn I a b \<Longrightarrow> contract_turn b c \<Longrightarrow> one_round I a c"

subsection {* Repetitions of rounds *}

text {* So, we can repeat rounds and see where they bring us.  *}
text {* The definition is taken from the book Concrete Semantics, and then modified *}
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text {* The repetition of rounds is either zero-times or once and the repetition. *}
lemma star_case :
"star r a c \<Longrightarrow>
 (a = c \<or> (\<exists> b. r a b \<and> star r b c))"
apply(induction rule: star.induct; auto)
done

text {* The next lemma is purely for convenience.
Actually the rounds can go nowhere after this invocation fails.
*}
lemma no_entry_fail [dest!]:
"star (one_round I)
      (a, ProgramToWorld (ContractFail, st, bal, v_opt))
      (b, c) \<Longrightarrow> b = a \<and> c = ProgramToWorld (ContractFail, st, bal, v_opt)"
apply(drule star_case; simp)
apply(simp add: one_round.simps add: world_turn.simps)
done

text {* Similarly, the rounds can go nowhere after this invocation returns. *}
lemma no_entry_return [dest!]:
"star (one_round I)
      (a, ProgramToWorld (ContractReturn data, st, bal, v_opt))
      (b, c) \<Longrightarrow> b = a \<and> c = ProgramToWorld (ContractReturn data, st, bal, v_opt)"
apply(drule star_case; simp)
apply(simp add: one_round.simps add: world_turn.simps)
done

text {* Also similarly, the rounds can go nowhere after this invocation
causes our contract to destroy itself.
*}
lemma no_entry_suicide [dest!]:
"star (one_round I)
      (a, ProgramToWorld (ContractSuicide, st, bal, v_opt))
      (b, c) \<Longrightarrow> b = a \<and> c = ProgramToWorld (ContractSuicide, st, bal, v_opt)"
apply(drule star_case; simp)
apply(simp add: one_round.simps add: world_turn.simps)
done

text {* And then the rounds can go nowhere after an annotation failure. *}
lemma no_entry_annotation_failure [dest!]:
"star (one_round I)
      (a, ProgramAnnotationFailure)
      (b, c) \<Longrightarrow> b = a \<and> c = ProgramAnnotationFailure"
apply(drule star_case; simp)
apply(simp add: one_round.simps add: world_turn.simps)
done

subsection {* How to State an Invariant *}

text {* For any invariant @{term I} over account states, now @{term "star (one_round I)"}
relation shows all possibilities during one invocation, assuming that the
invariant is kept during external calls\footnote{This assumption about deeper reentrancy should
be considered as an induction hypothesis.  There has to be a lemma actually perform
such induction.}.
The following template traverses the states and proves that the invariant is actually kept
after every possible round.  Also the template states that no annotation failures happen.
*}

definition no_assertion_failure :: "(account_state \<Rightarrow> bool) \<Rightarrow> bool"
where
"no_assertion_failure (I :: account_state \<Rightarrow> bool) ==
  (\<forall> init callenv. I (fst init) \<longrightarrow> snd init = ProgramInit callenv \<longrightarrow>
  (\<forall> fin. star (one_round I) init fin \<longrightarrow>
  I (fst fin) \<and>
  snd fin \<noteq> ProgramAnnotationFailure))"

subsection {* How to State a Pre-Post Condition Pair *}

text {* After proving a theorem of the above form, I might be interested in 
a more specific case (if the caller is not this particular account, nothing should change).
For that purpose, here is another template statement.  This contains everything above plus
an assumption about the initial call, and a conclusion about the state after the invocation.
*}

definition pre_post_conditions ::
"(account_state \<Rightarrow> bool) \<Rightarrow> (account_state \<Rightarrow> call_env \<Rightarrow> bool) \<Rightarrow>
 (account_state \<Rightarrow> call_env \<Rightarrow> (account_state \<times> program_result) \<Rightarrow> bool) \<Rightarrow> bool"
where
"pre_post_conditions (I :: account_state \<Rightarrow> bool) (precondition :: account_state \<Rightarrow> call_env\<Rightarrow> bool)
(postcondition :: (account_state \<Rightarrow> call_env \<Rightarrow> (account_state \<times> program_result) \<Rightarrow> bool)) ==
  (\<forall> initial_account initial_call. I initial_account \<longrightarrow>
     precondition initial_account initial_call \<longrightarrow>
  (\<forall> fin. star (one_round I) (initial_account, ProgramInit initial_call) fin \<longrightarrow>
  snd fin \<noteq> ProgramAnnotationFailure \<and>
  (\<forall> fin_observed. account_state_natural_change (fst fin) fin_observed \<longrightarrow>
  I fin_observed \<and>
  postcondition initial_account initial_call (fin_observed, snd fin))))
"

end
