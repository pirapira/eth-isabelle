theory RelationalSem

(* This is a relational semantics trying to capture
 * one element of the call stack *)

imports Main "./ContractSem"

begin

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

declare account_state_natural_change.simps [simp]

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

fun callable_result :: "program_result \<Rightarrow> bool"
where
  "callable_result ProgramStepRunOut = False"
| "callable_result (ProgramToWorld (_, _, _, _)) = False" (* The reentrance is contained in account_state_return_change *)
| "callable_result ProgramInvalid = False"
| "callable_result ProgramAnnotationFailure = False"
| "callable_result ProgramInit = True"

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
| "returnable_result ProgramInit = False"
| "returnable_result ProgramInvalid = False"
| "returnable_result ProgramAnnotationFailure = False"

inductive world_turn :: "(account_state \<Rightarrow> bool) \<Rightarrow> (account_state * program_result) \<Rightarrow> (account_state * variable_env) \<Rightarrow> bool"
where
(*  world_continue: "world_turn (orig, (InstructionContinue v)) (orig, v)"*)
(* TODO  enable this with invariant. *)
  world_call:
  "account_state_natural_change old_state new_state \<Longrightarrow>
   build_venv_called new_state callargs next_venv \<Longrightarrow>
   callable_result result \<Longrightarrow>
   world_turn _ (old_state, result) (new_state, next_venv)"
| world_return:
  "account_state_return_change I account_state_going_out account_state_back \<Longrightarrow>
   build_venv_returned account_state_back result new_v \<Longrightarrow>
   returnable_result program_r \<Longrightarrow>
   world_turn I (account_state_going_out, program_r) (account_state_pop_ongoing_call account_state_back, new_v)"
| world_fail:
  "account_state_return_change I account_state_going_out account_state_back \<Longrightarrow>
   build_venv_failed account_state_back = Some new_v \<Longrightarrow>
   returnable_result result \<Longrightarrow>
   world_turn I (account_state_going_out, result) (account_state_pop_ongoing_call account_state_back, new_v)"


abbreviation next_instruction :: "constant_env \<Rightarrow> variable_env \<Rightarrow> inst \<Rightarrow> bool"
where
"next_instruction c v i ==
  (case lookup (program_content (cenv_program c)) (venv_pc v) of
      Some i' \<Rightarrow> i = i'
    | _ \<Rightarrow> False)"

inductive contract_turn :: "(account_state * variable_env) \<Rightarrow> (account_state * program_result) \<Rightarrow> bool"
where
  contract_to_world:
  "build_cenv old_account = cenv \<Longrightarrow>
   program_sem old_venv cenv (program_length (cenv_program cenv)) steps = ProgramToWorld (act, st, bal, opt_v) \<Longrightarrow>
   account_state_going_out = update_account_state old_account act st bal opt_v \<Longrightarrow>
   contract_turn (old_account, old_venv) (account_state_going_out, ProgramToWorld (act, st, bal, opt_v))"
| contract_annotation_failure:
  "build_cenv old_account = cenv \<Longrightarrow>
   program_sem old_venv cenv (program_length (cenv_program cenv)) steps = ProgramAnnotationFailure \<Longrightarrow>
   contract_turn (old_account, old_venv) (old_account, ProgramAnnotationFailure)"


inductive one_step :: "(account_state \<Rightarrow> bool) \<Rightarrow> (account_state * program_result) \<Rightarrow> (account_state * program_result) \<Rightarrow> bool"
where
step:
"world_turn I a b \<Longrightarrow> contract_turn b c \<Longrightarrow> one_step I a c"

inductive initial_program_result :: "account_state \<Rightarrow> (account_state * program_result) \<Rightarrow> bool"
where
initial:
"initial_program_result a (a, ProgramInit)"

(* taken from the book Concrete Semantics *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_case' :
"
star r init dst \<Longrightarrow>
(P init) \<Longrightarrow>
(\<forall> next future. r init next \<longrightarrow>
 star r next future \<longrightarrow> (P future))
\<Longrightarrow> P dst
"
apply(induction rule: star.induct; auto)
done

lemma star_case'' :
"
P init \<Longrightarrow>
(\<forall> next future. r init next \<longrightarrow>
 star r next future \<longrightarrow> P future) \<Longrightarrow>
star r init dst \<longrightarrow> P dst
"
apply(auto)
apply(drule star_case'; auto)
done

lemma star_case :
"star r a c \<Longrightarrow>
 (a = c \<or> (\<exists> b. r a b \<and> star r b c))"
apply(induction rule: star.induct; auto)
done

definition no_assertion_failure :: "(account_state \<Rightarrow> bool) \<Rightarrow> bool"
where
"no_assertion_failure (I :: account_state \<Rightarrow> bool) ==
  (\<forall> init. I (fst init) \<longrightarrow> snd init = ProgramInit \<longrightarrow>
  (\<forall> fin. star (one_step I) init fin \<longrightarrow>
  I (fst fin) \<and>
  snd fin \<noteq> ProgramAnnotationFailure))"

end
