theory TestSdiv

imports Main "../ContractSem"

begin

declare eval_annotation_def [simp]

definition this_address :: address
where "this_address = undefined"

abbreviation test_sdiv_code :: "inst list"
where
"test_sdiv_code ==
   Stack (PUSH_N [255])
 # Stack (PUSH_N [2])
 # Arith EXP
 # Dup 1
 # Annotation (\<lambda> aenv. length (aenv_stack aenv) = 2)
 # Stack (PUSH_N [0])
 # Bits inst_NOT
 # Swap 1
 # Annotation (\<lambda> aenv. length (aenv_stack aenv) = 3)
 # Sarith SDIV
 # Annotation (\<lambda> aenv. length (aenv_stack aenv) = 2)
 # Annotation (\<lambda> aenv. (aenv_stack aenv ! 0) = (aenv_stack aenv ! 1))
 # Misc STOP
 # []"


 
abbreviation test_sdiv_account_state :: "account_state"
where
"test_sdiv_account_state ==
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = test_sdiv_code
   , account_balance = 0
   , account_ongoing_calls = []
   \<rparr>"

abbreviation test_sdiv_spec :: "response_to_world"
where
" test_sdiv_spec ==
  \<lparr> when_called = \<lambda> _. (ContractReturn [],
                        \<lambda> a. True)
  , when_returned = \<lambda> _. (ContractFail,
                           \<lambda> a. True)
  , when_failed = (ContractFail,
                     \<lambda> a. True)
  \<rparr>
"

value "32 div sint (max_word :: uint)"

lemma test_sdiv_correct:
"
  account_state_responds_to_world
  (\<lambda> a. a = test_sdiv_account_state)
  test_sdiv_spec
"
apply(rule AccountStep; auto)
apply(case_tac steps; auto)
apply(simp add:max_word_def)
apply(simp add:max_word_def)
done

end
