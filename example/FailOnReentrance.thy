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
  Misc STOP # []"

abbreviation fail_on_reentrance_program :: "inst list"
where
"fail_on_reentrance_program ==
  Stack (PUSH_N [0]) #
  Storage SLOAD #
  Dup 1 #
  Stack (PUSH_N [2]) #
  Pc JUMP #
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
  Misc CALL #
  after_call"
  
definition fail_on_reentrance_address :: address
where
"fail_on_reentrance_address = undefined"

fun fail_on_reentrance_depth_n_state :: "uint \<Rightarrow> uint \<Rightarrow> account_state"
where
  "fail_on_reentrance_depth_n_state 0 bal =
   \<lparr> account_address = fail_on_reentrance_address
   , account_storage = \<lambda> _. 0
   , account_code = fail_on_reentrance_program
   , account_balance = bal
   , account_ongoing_calls = []
   \<rparr>"
| "fail_on_reentrance_depth_n_state 1 =
   \<lparr> account_address = fail_on_reentrance_address
   , account_storage = \<lambda> idx. if idx = 0 then 1 else 0
   , account_code = fail_on_reentrance_program
   , account_balance = bal
   , account_ongoing_calls = [ongoing]
   \<rparr>
   
    "account_code st = fail_on_reentrance_program \<Longrightarrow>
     account_storage st 0 = 1 \<Longrightarrow>
     account_address st = fail_on_reentrance_address \<Longrightarrow>
     account_ongoing_calls st = [ve] \<Longrightarrow>
     venv_prg_sfx ve = after_call \<Longrightarrow>
     venv_storage ve 0 = 0 \<Longrightarrow>
     venv_storage_at_call ve 0 = 0 \<Longrightarrow>
     fail_on_reentrance_depth_n_state 1 st"
     
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

fun call_but_fail_on_reentrance :: "uint \<Rightarrow> response_to_world"
where
"call_but_fail_on_reentrance 0 =
   \<lparr> when_called = \<lambda> _. ContractAction (ContractCall something_to_call,
                                        call_but_fail_on_r_state 1)
   , when_returned = \<lambda> _. ContractAction (ContractFail, call_but_fail_on_r_state 0)
   , when_failed = ContractAction (ContractFail, call_but_fail_on_r_state 0)
   \<rparr>
"

end
