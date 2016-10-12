theory FailOnReentrance

imports Main "../ContractSem"

begin

abbreviation after_call :: "inst list"
where
"after_call ==
  Arith ISZERO #
  Stack (PUSH_N [0]) #
  Pc JUMPI #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Storage SSTORE #
  Annotation (\<lambda> aenv. aenv_storage aenv 0 = 0) #
  Misc STOP # []"

abbreviation fail_on_reentrance_program :: "inst list"
where
"fail_on_reentrance_program ==
  Stack (PUSH_N [0]) #
  Storage SLOAD #
  Dup 1 #
  Stack (PUSH_N [2]) #
  Pc JUMPI #
  Stack (PUSH_N [1]) #
  Arith ADD #
  Stack (PUSH_N [0]) #
  Storage SSTORE #
  Stack (PUSH_N [0]) #
  (* TODO: change some of these arguments to value, address *)
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
(*  Annotation (\<lambda> aenv. length (aenv_stack aenv) = 7) # *)
  Misc CALL #
  after_call"
  
definition fail_on_reentrance_address :: address
where
"fail_on_reentrance_address = undefined"

inductive fail_on_reentrance_state :: "nat \<Rightarrow> account_state \<Rightarrow> bool"
where
  depth_zero:
    "account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_storage st 0 = 0 \<Longrightarrow>
     account_code st = fail_on_reentrance_program \<Longrightarrow>
     account_ongoing_calls st = [] \<Longrightarrow>
     fail_on_reentrance_state 0 st"
| depth_one:
    "account_code st = fail_on_reentrance_program \<Longrightarrow>
     account_storage st 0 = 1 \<Longrightarrow>
     account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_ongoing_calls st = [ve] \<Longrightarrow>
     venv_prg_sfx ve = after_call \<Longrightarrow>
     venv_storage ve 0 = 1 \<Longrightarrow>
     venv_storage_at_call ve 0 = 0 \<Longrightarrow>
     fail_on_reentrance_state 1 st"

declare fail_on_reentrance_state.simps [simp]

abbreviation something_to_call :: call_arguments
where
"something_to_call ==
 \<lparr> callarg_gaslimit = 0
 , callarg_code = 0
 , callarg_recipient = 0
 , callarg_value = 0
 , callarg_data = cut_memory 0 0 empty_memory
 , callarg_output_begin = 0
 , callarg_output_size = 0
 \<rparr>"

fun fail_on_reentrance_spec :: "nat \<Rightarrow> response_to_world"
where
  "fail_on_reentrance_spec 0 =
   \<lparr> when_called = \<lambda> _. (ContractCall something_to_call,
                                        fail_on_reentrance_state 1)
   , when_returned = \<lambda> _. (ContractFail, fail_on_reentrance_state 0)
   , when_failed = (ContractFail, fail_on_reentrance_state 0)
   \<rparr>"
| "fail_on_reentrance_spec (Suc 0) =
   \<lparr> when_called = \<lambda> _. (ContractFail, fail_on_reentrance_state 1)
   , when_returned = \<lambda> _. (ContractReturn [], fail_on_reentrance_state 0)
   , when_failed = (ContractFail, fail_on_reentrance_state 0)
   \<rparr>"
| "fail_on_reentrance_spec (Suc (Suc n)) =
   \<lparr> when_called = \<lambda> _. (ContractFail, fail_on_reentrance_state (Suc (Suc n)))
   , when_returned = \<lambda> _. (ContractFail, fail_on_reentrance_state (Suc (Suc n)))
   , when_failed = (ContractFail, fail_on_reentrance_state (Suc (Suc n))) \<rparr>"

declare fail_on_reentrance_spec.simps [simp]

declare drop_bytes.simps [simp]

lemma two [simp] : "2 = Suc (Suc 0)"
apply(auto)
done




lemma fail_on_reentrance_correct :
  "account_state_responds_to_world
    (fail_on_reentrance_state n)
    (fail_on_reentrance_spec n)
    "
apply(case_tac n)
 apply(simp)
 apply(rule AccountStep; auto)
 apply(case_tac steps; auto)
apply(case_tac nat; auto)
 apply(rule AccountStep; auto)
   apply(case_tac steps; auto)
  apply(case_tac steps; auto)
 apply(case_tac steps; auto)
apply(rule AccountStep; auto)
done
end
