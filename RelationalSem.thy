section {* What can Happen during a Contract Invocation *}

text {* This section defines a set of sequence of account states that can appeear during an
invocation of a countract.  The invocation can be a nested reentrancy, but we focus on one
invocation.  This means we do not look into details of further reentrancy, but just assume 
that the inner reentrancy keeps the invariant of the contract.  Of course we need to prove
that the invariant holds for the code, but when we do that we can assume that the inner
nested calls keep the invariants (we can say we are doing mathematical induction on the depth
of reentrancy)\footnote{This poses troubles dealing with DELEGATECALL and CALLCODE instructions.
Currently execution of these instructions causes an immediate annotation failure.}.  *}

theory RelationalSem

imports Main "./ContractSem"

begin

subsection {* Some Possible Changes on Our Account State *}

text {* The account state might change even when the account's code is not executing. *}

text {* Between blocks, the account might gain balances because somebody mines 
Eth for the account.  Even within a single block,
the balance might increase also while other contracts execute
because they might destroy themselves and send their balance to our account.
When a transaction finishes, if our contract is marked as killed, it is destroyed.
The following relation captures these possibilities.
*}

inductive account_state_natural_change :: "account_state \<Rightarrow> account_state \<Rightarrow> bool"
where
natural: -- {* The balance of this account might increase
whenever the code in our contract is not executing.  Some other account might
destroy itself and give its balance to our account.  *}
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

text {* When the execution comes back from an external call, the account state might have changed
arbitrarily.  Our strategy is to assume that an invariant is kept here; and later prove that
the invariant actually holds (that is, for fewer depth of reentrancy).
The whole argument can be seen as a mathematical induction over depths of reentrancy, though
this idea has not been formalized yet. *}

inductive account_state_return_change ::
"(account_state \<Rightarrow> bool) \<Rightarrow> account_state \<Rightarrow> account_state \<Rightarrow> bool"
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
 account_state_return_change
 invariant
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
-- {* because we are not modeling nested calls here, the effect of the nested calls are modeled in
      account\_state\_return\_change *}
| "returnable_result (ProgramToWorld (ContractReturn _, _, _, _)) = False"
| "returnable_result (ProgramInit _) = False"
| "returnable_result ProgramInvalid = False"
| "returnable_result ProgramAnnotationFailure = False"

subsection {* A Round of the Game *}

text {* Now we are ready to specify the world's turn. *}

inductive world_turn ::
"(account_state \<Rightarrow> bool) (* The invariant of our contract*)
\<Rightarrow> (account_state * program_result)
   (* the account state before the world's move
      and the last thing our account did *)
\<Rightarrow> (account_state * variable_env)
   (* the account state after the world's move
      and the variable environment from which our contract must start. *)
\<Rightarrow> bool (* a boolean indicating if that is a possible world's move. *)"
where
  world_call: -- {* the world might call our contract.  We only consider the initial invocation here
  because the deeper reentrant invocations are considered as a part of the adversarial world. 
  The deeper reentrant invocations are performed without the world replying to the contract. *}
  "(* If a variable environment is built from the old account state *)
   (* and the call arguments, *)
   build_venv_called old_state callargs next_venv \<Longrightarrow>
   
   (* the world makes a move, showing the variable environment. *)
   world_turn I (old_state, ProgramInit callargs) (old_state, next_venv)"
| world_return: -- {* the world might return to our contract. *}
  "(* If the account state can be changed during reentrancy,*)
   account_state_return_change I account_state_going_out account_state_back \<Longrightarrow>

   (* and a variable environment can be recovered from the changed account state,*)
   build_venv_returned account_state_back result new_v \<Longrightarrow>

   (* and the previous move of the contract was a call-like action, *)
   returnable_result program_r \<Longrightarrow>

   (* the world can make a move, telling the contract to continue with *)
   (* the variable environment. *)
   world_turn I (account_state_going_out, program_r)
                (account_state_pop_ongoing_call account_state_back, new_v)"

| world_fail: -- {* the world might fail from an account into our contract. *}
  "(* If a variable environment can be recovered from the previous account state,*)
   build_venv_failed account_state_going_out = Some new_v \<Longrightarrow>
   
   (* and if the previous action from the contract was a call, *)
   returnable_result result = True \<Longrightarrow>
   
   (* the world can make a move, telling the contract to continue with *) 
   (* the variable environment. *)
   world_turn I (account_state_going_out, result)
                (account_state_pop_ongoing_call account_state_going_out, new_v)"

text {* As a reply, our contract might make a move, or report an annotation failure.*}

inductive contract_turn ::
"(account_state * variable_env) \<Rightarrow> (account_state * program_result) \<Rightarrow> bool"
where
  contract_to_world:
  "(* Under a constant environment built from the old account state, *)
   build_cenv old_account = cenv \<Longrightarrow>

   (* if the program behaves like this, *)
   program_sem old_venv cenv 
      (program_length (cenv_program cenv)) steps
      = ProgramToWorld (act, st, bal, opt_v) \<Longrightarrow>

   (* and if the account state is updated from the program's result, *)
   account_state_going_out
     = update_account_state old_account act st bal opt_v \<Longrightarrow>

   (* the contract makes a move and udates the account state. *)
   contract_turn (old_account, old_venv)
      (account_state_going_out, ProgramToWorld (act, st, bal, opt_v))"

| contract_annotation_failure:
  "(* If a constant environment is built from the old account state, *)  
   build_cenv old_account = cenv \<Longrightarrow>
   
   (* and if the contract execution results in an annotation failure, *)
   program_sem old_venv cenv
      (program_length (cenv_program cenv)) steps = ProgramAnnotationFailure \<Longrightarrow>

   (* the contract makes a move, indicating the annotation failure. *)
   contract_turn (old_account, old_venv) (old_account, ProgramAnnotationFailure)"

text {* When we combine the world's turn and the contract's turn, we get one round.
The round is a binary relation over a single set.
*}

inductive one_round ::
"(account_state \<Rightarrow> bool) \<Rightarrow> 
(account_state * program_result) \<Rightarrow> 
(account_state * program_result) \<Rightarrow> bool"
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

text {* The repetition of rounds is either zero-times or once and a repetition. *}
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
relation shows all possibilities during one invocation\footnote{More precisely,
this transitive closure of rounds guides us through all the possible states when the contract loses the control flow.}, assuming that the
invariant is kept during external calls\footnote{This assumption about deeper reentrancy should
be considered as an induction hypothesis.  There has to be a lemma actually perform
such induction.}.
The following template traverses the states and states that the invariant is actually kept
after every possible round.  Also the template states that no annotation failures happen.
When I state something, I will be then obliged to prove the statement.  This happens in the next section.
*}

text {* I define the conjunction of the properties requested at the final states.
The whole thing is more readable when I inline-expand @{term no_assertion_failure_post},
but if I do that, the @{text auto} tactic splits out a subgoal for each conjunct.
This doubles the already massive number of subgoals.
*}

definition no_assertion_failure_post ::
  "(account_state \<Rightarrow> bool) \<Rightarrow> (account_state \<times> program_result) \<Rightarrow> bool"
where
"no_assertion_failure_post I fin =
 (I (fst fin) \<and> (* The invariant holds. *)
  snd fin \<noteq> ProgramAnnotationFailure)  (* No annotations have failed. *)
"

text {* @{term "no_assertion_failure"} is a template for statements.
It takes a single argument @{term I} for the invariant.
The invariant is assumed to hold at the initial state.
The initial state is when the contract is called (this can be the first
invocation of this contract in this transaction, or a reentrancy).
The statement will request us to prove that the invariant also
holds whenever the invocation loses the control flow.
The invocation loses the control flow when the contract returns or fails
from the invocation, and also when it calls an account.
When the contract calls an account, the invocation does not finish so
I need to verify further final states against the postconditions, after
the call finishes.
The repetition is captured by the transitive closure
@{term "star (one_round I)"}.

We prove the invariant when our contract calls out,
and we assume that reentrancy into this contract will
keep the invariant.
The whole argument can be seen as a mathematical induction
over the depth of reentrancy.  So we can assume that
reentrancy of a fewer depth keeps the invariant.
This idea comes from Christian Reitwiessner's treatment of
reentrancy in Why ML.
I have not justified the idea in Isabelle/HOL.
*}

definition no_assertion_failure :: "(account_state \<Rightarrow> bool) \<Rightarrow> bool"
where
"no_assertion_failure (I :: account_state \<Rightarrow> bool) \<equiv>
  (\<forall> addr str code bal ongoing killed callenv.
    I \<lparr> account_address = addr, account_storage = str, account_code = code,
       account_balance = bal, account_ongoing_calls = ongoing,
       account_killed = killed \<rparr> \<longrightarrow>
  (\<forall> fin. star (one_round I) (
    \<lparr> account_address = addr, account_storage = str, account_code = code,
      account_balance = bal, account_ongoing_calls = ongoing,
      account_killed = killed \<rparr>
  , ProgramInit callenv) fin \<longrightarrow>
  no_assertion_failure_post I fin))"

subsection {* How to State a Pre-Post Condition Pair *}

text {* After proving a theorem of the above form, I might be interested in 
a more specific case (e.g.\,if the caller is not this particular account, nothing should change).
For that purpose, here is another template statement.  This contains everything above plus
an assumption about the initial call, and a conclusion about the state after the invocation.
*}

text {* I pack everything that I want when the contract fails or returns.
This definition reduces the number of goals that I need to prove.
Without this definition, the @{text auto} tactic
splits a goal @{prop "A \<Longrightarrow> B \<and> C"} into two subgoals @{prop "A \<Longrightarrow> B"} and @{prop "A \<Longrightarrow> C"}.
When I do complicated case analysis on @{prop A}, the number of subgoals grow rapidly.
So, I define @{term packed} to be @{prop "B \<and> C"} and prevent the @{text auto} tactic from noticing that it is a conjunction.
*}

text {* The following snippet says the invariant still holds in the observed final state%
\footnote{After the invocation finishes, some miner can credit Eth to the account under
verification.  The ``observed'' final state is an arbitrary state 
after such possible balance increases.}
and the postconditions hold there. *}

definition postcondition_pack
where
"postcondition_pack I postcondition fin_observed initial_account initial_call fin
=
  (I fin_observed \<and>
  postcondition initial_account initial_call (fin_observed, snd fin))"
  
text {* The whole template takes an invariant @{term I}, a @{term precondition}
and a @{term postcondition}. The statement is about one invocation of the contract.
This invocation can be a reentrancy.  The initial state is when the contract is invoked,
and the final states\footnote{Since I am considering all possible executions, there are multiple
final states.  Also, even when I concetrate on a single execution, every time the contract calls an
account, I have to check the invariants.  Otherwise, I have no knowledge about what happens
during the following reentrancy. } are
when this invocation makes a call to an account, returns or fails.
We further consider natural balance increases\footnote{The balnace of an Ethereum account increases
naturally when a contract destroys itself and sends its balance to our account, for instance.}
and use the ``observed final state'' to
evaluate the post condition.
Of course, in between, there might be nesting reentrant invocations, that might alter
the storage and the balance of the contract.

At the time of invocation, the invariant and the preconditions are assumed.
During reentrant calls (that are deeper than the current invocation),
the statement will request us to prove that the invariant holds at any moment when
the contract loses the control flow (when the contract returns, fails or calls an account).
Also we will be requested to prove that the postcondition holds on these occasions.
The contract regains the control flow after a deeper call finishes, and the contract
would lose the control flow again.
All these requirements are captured by the transitive closure of @{term one_round} relation.
*}

definition pre_post_conditions ::
"(account_state \<Rightarrow> bool) \<Rightarrow> (account_state \<Rightarrow> call_env \<Rightarrow> bool) \<Rightarrow>
 (account_state \<Rightarrow> call_env \<Rightarrow> (account_state \<times> program_result) \<Rightarrow> bool) \<Rightarrow> bool"
where
"pre_post_conditions
  (I :: account_state \<Rightarrow> bool)
  (precondition :: account_state \<Rightarrow> call_env\<Rightarrow> bool)
  (postcondition :: account_state \<Rightarrow> call_env \<Rightarrow>
                    (account_state \<times> program_result) \<Rightarrow> bool) \<equiv>
                    
  (* for any initial call and initial account state that satisfy *)
  (* the invariant and the precondition, *)
  (\<forall> initial_account initial_call. I initial_account \<longrightarrow>
     precondition initial_account initial_call \<longrightarrow>
     
  (* for any final state that are reachable from these initial conditions, *)
  (\<forall> fin. star (one_round I) (initial_account, ProgramInit initial_call) fin \<longrightarrow>
  
  (* the annotations have not failed *)
  snd fin \<noteq> ProgramAnnotationFailure \<and>
  
  (* and for any observed final state after this final state, *)
  (\<forall> fin_observed. account_state_natural_change (fst fin) fin_observed \<longrightarrow>
  
  (* the postcondition and the invariant holds. *)
  postcondition_pack
  I postcondition fin_observed initial_account initial_call fin)))
"

end
