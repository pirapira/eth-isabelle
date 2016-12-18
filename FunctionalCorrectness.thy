(*
   Copyright 2016 Yoichi Hirai

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

theory FunctionalCorrectness

imports Main "./ContractSem"

begin

subsection "Functional Correctness"

text {* The definitions in this subsection are not used in the analysis of Deed contract
currently.  They are useful when we write down the expected behavior of a contract as
a function in Isabelle/HOL, and compare the function against the actual implementation. *}

text {* To specify a contract's behavior,
we specify its action and a condition on the account state. *}

type_synonym contract_behavior = "contract_action * (account_state \<Rightarrow> bool)"

text {* A contract can be called into, returned back to, or failed back to.
The following record specifies a behavior for all these cases.
When the contract is called into or returned back to,
some data is available to the contract.  Otherwise, when
the contract is failed back to, there is no input apart from the 
fact that the inner call has failed.
*}

record response_to_world =
  when_called :: "call_env \<Rightarrow> contract_behavior"
  when_returned :: "return_result \<Rightarrow> contract_behavior"
  when_failed :: "contract_behavior"

abbreviation respond_to_call_correctly ::
  " (call_env \<Rightarrow> contract_behavior) \<Rightarrow>
       account_state \<Rightarrow> bool"
where "respond_to_call_correctly c a \<equiv>
  (\<forall> call_env initial_venv resulting_action final_state_pred.
     build_vcon_called a call_env initial_venv \<longrightarrow>
         (* The specification says the execution should result in these *)
         c call_env = (resulting_action, final_state_pred) \<longrightarrow>
         ( \<forall> steps. (* and for any number of steps *)
           ( let r = program_sem initial_venv (build_cenv a)
                      (program_length (account_code a)) steps in
             (* either more steps are necessary, or *)
             r = ProgramStepRunOut \<or>
             (* the result matches the specification *)
             (\<exists> pushed_venv st bal.
              r = ProgramToEnvironment resulting_action st bal pushed_venv \<and>
              final_state_pred
                (update_account_state a resulting_action st bal pushed_venv)))))"

abbreviation respond_to_return_correctly ::
  "(return_result \<Rightarrow> contract_behavior) \<Rightarrow>
   account_state \<Rightarrow>
   bool"
where
"respond_to_return_correctly r a \<equiv>
   (\<forall> rr initial_venv final_state_pred resulting_action.
       build_vcon_returned a rr initial_venv \<longrightarrow>
       r rr = (resulting_action, final_state_pred) \<longrightarrow>
       ( \<forall> steps.
          (let r = program_sem initial_venv (build_cenv a)
                     (program_length (account_code a)) steps in
           r = ProgramStepRunOut \<or>
           (\<exists> pushed_venv st bal.
            r = ProgramToEnvironment resulting_action st bal pushed_venv \<and>
            final_state_pred
              (update_account_state (account_state_pop_ongoing_call a)
               resulting_action st bal pushed_venv)))))"

abbreviation respond_to_fail_correctly ::
  "contract_behavior \<Rightarrow>
   account_state \<Rightarrow>
   bool"
where
"respond_to_fail_correctly f a \<equiv>
   (\<forall> initial_venv final_state_pred resulting_action.
      Some initial_venv = build_vcon_failed a \<longrightarrow>
      f = (resulting_action, final_state_pred) \<longrightarrow>
      (\<forall> steps.
        (let r = program_sem initial_venv (build_cenv a)
                   (program_length (account_code a)) steps in
         r = ProgramStepRunOut \<or>
         (\<exists> pushed_venv st bal.
            r = ProgramToEnvironment resulting_action st bal pushed_venv \<and>
            final_state_pred
              (update_account_state (account_state_pop_ongoing_call a)
                 resulting_action st bal pushed_venv)))))"

text {* The following statement summarizes everything above.
Essentially, the functional correctness holds when
the code responds to calls correctly, responds to returns correctly,
and responds to failures correctly.
The statement is parametrized with a precondition.
*}

inductive account_state_responds_to_world ::
  "(account_state \<Rightarrow> bool) \<Rightarrow> response_to_world \<Rightarrow> bool"
where
AccountStep:
  "(\<forall> a. precond a \<longrightarrow> respond_to_call_correctly c a) \<Longrightarrow>
   (\<forall> a. precond a \<longrightarrow> respond_to_return_correctly r a) \<Longrightarrow>
   (\<forall> a. precond a \<longrightarrow> respond_to_fail_correctly f a) \<Longrightarrow>
   account_state_responds_to_world precond
   \<lparr> when_called = c, when_returned = r, when_failed = f \<rparr>"

end
