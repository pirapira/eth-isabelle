theory AlwaysFail

imports Main "../ContractSem"

begin

definition this_address :: address
where "this_address = undefined"

definition always_fail_code :: "inst list"
where
"always_fail_code =
   Stack (PUSH_N [0]) # Pc JUMP # []"

definition always_fail_account_state :: "uint \<Rightarrow> account_state"
where
"always_fail_account_state balance =
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = always_fail_code
   , account_balance = balance
   , account_ongoing_calls = []
   \<rparr>"

end
