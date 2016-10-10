theory AlwaysFail

imports Main "../ContractSem"

begin

definition this_address :: address
where "this_address = undefined"

abbreviation always_fail_code :: "inst list"
where
"always_fail_code ==
   Stack (PUSH_N [0]) # Pc JUMP # []"

abbreviation always_fail_account_state :: "uint \<Rightarrow> account_state"
where
"always_fail_account_state balance ==
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = always_fail_code
   , account_balance = balance
   , account_ongoing_calls = []
   \<rparr>"
   
abbreviation always_fail_spec :: "uint \<Rightarrow> response_to_world"
where
" always_fail_spec initial_balance ==
  \<lparr> when_called = \<lambda> _. (ContractFail, always_fail_account_state initial_balance)
  , when_returned = \<lambda> _. (ContractFail, always_fail_account_state initial_balance)
  , when_failed = (ContractFail, always_fail_account_state initial_balance)
  \<rparr>
"

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "ev (Suc(Suc 0))"

apply(rule evSS)
apply (rule ev0)
done

lemma always_fail_correct:
"
  account_state_responds_to_world
  (always_fail_account_state initial_balance)
  (always_fail_spec initial_balance)
  (\<lambda> _ _. True)
"
apply (rule AccountStep; auto)
apply(case_tac steps)
 apply(auto)
apply(case_tac nat)
 apply(auto)
apply(simp add: word_rcat_def add: unat_def add: bin_rcat_def)
done

end
