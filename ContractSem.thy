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

theory ContractSem

imports Main "~~/src/HOL/Word/Word" "./ContractEnv" "./Instructions" "./KEC" "./lem/Evm"
(* If ./lem/Evm is missing, try executing `make lem-thy` *)

begin

declare venv_advance_pc_def [simp]
declare venv_next_instruction_def [simp]
declare call_def [simp]

text {* When the if-condition is known to be True, the simplifier can
proceed into the then-clause.  The \textit{simp} attribute encourages the simplifier
to use this equation from left to right whenever applicable.  *}
lemma strict_if_True [simp] :
"strict_if True a b = a True"
apply(simp add: strict_if_def)
done

text {* When the if-condition is known to be False, the simplifier
can proceed into the else-clause. *}
lemma strict_if_False [simp] :
"strict_if False a b = b True"
apply(simp add: strict_if_def)
done

text {* When the if-condition is not known to be either True or False,
the simplifier is allowed to perform computation on the if-condition.
The \textit{cong} attribute tells the simplifier to try to rewrite the
left hand side of the conclusion, using the assumption.
*}
lemma strict_if_cong [cong] :
"b0 = b1 \<Longrightarrow> strict_if b0 x y = strict_if b1 x y"
apply(auto)
done

declare empty_program_def [simp]
declare prepend_annotation_def [simp]
declare program_annotation_of_lst.simps [simp]
declare program_of_lst_def [simp]
declare program_as_memory_def [simp]
   
subsection {* The Result of an Instruction *}

declare instruction_failure_result_def [simp]

text {* When the contract returns, the result of the instruction always looks like this: *}
  
declare instruction_return_result_def [simp]
declare M_def [simp]
declare update_balance_def [simp]
declare venv_pop_stack.simps [simp]
declare venv_stack_top_def [simp]
declare venv_update_storage_def [simp]
declare stack_0_0_op_def [simp]
declare stack_0_1_op_def [simp]
declare stack_1_1_op_def [simp]
declare stack_1_2_op_def [simp]
declare stack_2_1_op_def [simp]
declare stack_3_1_op_def [simp]
declare sstore_def [simp]
declare build_aenv_def [simp]
declare jump_def [simp]

text {* When the second argument is already @{term True}, the simplification can continue.
Otherwise, the Isabelle/HOL simplifier is not allowed to expand the definition of
@{term blockedInstructionContinue}. *}
lemma unblockInstructionContinue [simp] :
"blockedInstructionContinue v True = InstructionContinue v"
apply(simp add: blockedInstructionContinue_def)
done

text {* This is another reminiscent of my struggle against the Isabelle/HOL simplifier.
Again, the simplifier is not allowed to expand the definition unless the second argument
is known to be @{term True}.*}

lemma unblock_jump [simp]:
"blocked_jump v c True = jump v c"
apply(simp add: blocked_jump_def)
done

declare jumpi_def [simp]
declare datasize_def [simp]
declare read_word_from_bytes_def [simp]
declare cut_data_def [simp]
declare cut_memory.simps [simp]
declare delegatecall_def [simp]
declare callcode_def [simp]
declare create_def [simp]
declare ret_def [simp]
declare stop_def [simp]
declare pop_def [simp]
declare store_byte_list_memory.psimps [simp]
declare store_word_memory_def [simp]
declare mstore_def [simp]
declare mload_def [simp]
declare mstore8_def [simp]
declare input_as_memory_def [simp]
declare calldatacopy_def [simp]
declare codecopy_def [simp]
declare extcodecopy_def [simp]
declare pc_def [simp]
declare log_def [simp]

declare list_swap_def [simp]

text "For testing, I prove some lemmata:"
lemma "list_swap 1 [0, 1] = Some [1, 0]"
apply(auto)
done

lemma "list_swap 2 [0, 1] = None"
apply(auto)
done

lemma "list_swap 2 [0, 1, 2] = Some [2, 1, 0]"
apply(auto)
done

lemma "list_swap 3 [0, 1, 2, 3] = Some [3, 1, 2, 0]"
apply(auto)
done

lemma"list_swap 1 [0, 1, 2, 3] = Some [1, 0, 2, 3]"
apply(auto)
done

declare swap_def [simp]

definition sha3 :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sha3 v c \<equiv>
  (case venv_stack v of
    start # len # rest \<Rightarrow>
      InstructionContinue (
        venv_advance_pc c v\<lparr> venv_stack := keccack
                                         (cut_memory start (unat len) (venv_memory v))
                                        # rest
                        , venv_memory_usage := M (venv_memory_usage v) start len
                        \<rparr>)
  | _ \<Rightarrow> instruction_failure_result v)"

declare sha3_def [simp]

declare general_dup_def [simp]

text "The SUICIDE instruction involves value transfer."
definition suicide :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"suicide v c =
  (case venv_stack v of 
     dst # _ \<Rightarrow>
       let new_balance = (venv_balance v)(cenv_this c := 0,
         ucast dst := venv_balance v (cenv_this c) + (venv_balance v (ucast dst))) in
       InstructionToWorld ContractSuicide (venv_storage v) new_balance None
    | _ \<Rightarrow> instruction_failure_result v)"

declare suicide_def [simp]

text "Finally, using the above definitions, I can define a function that operates an instruction
on the execution environments."

lemma "Word.word_rcat [(0x01 :: byte), 0x02] = (0x0102 :: w256)"
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
done
    
declare instruction_sem.simps [simp]

subsection {* Programs' Answer to the World *}

text "Execution of a program is harder than that of instructions.  The biggest difficulty is that
the length of the execution is arbitrary.  In Isabelle/HOL all functions must terminate, so I need
to prove the termination of program execution.  In priciple, I could have used gas, but I was
lazy to model gas at that moment, so I introduced an artificial step counter.  When I prove theorems
about smart contracts, the theorems are of the form ``for any value of the initial step counter,
this and that never happen.''"

text "Since our program struct contains a list of annotations for each program position,
I have a function that checks all annotations at a particular program position:"  

declare check_annotations_def [simp]

   
text {* The program execution takes two counters.
One counter is decremented for each instruction.
The other counter is decremented when a backward-jump happens.
This setup allows an easy termination proof.
Also, during the proofs, I can do case analysis on the number of backwad jumps
rather than the number of instructions.
*}

declare program_sem.simps [simp]

text {* The following lemma is just for controlling the Isabelle/HOL simplifier. *}

lemma unblock_program_sem [simp] : "blocked_program_sem v c l p True = program_sem v c l p"
apply(simp add: blocked_program_sem.psimps)
done

definition program_sem_blocked :: "variable_env \<Rightarrow> constant_env \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> program_result"
where
"program_sem_blocked v c internal external _ = program_sem v c internal external"

lemma program_sem_unblock :
"program_sem_blocked v c internal external True = program_sem v c internal external"
apply(simp add: program_sem_blocked_def)
done

subsection {* Account's State *}

text {* In the bigger picture, a contract invocation changes accounts' states.
An account has a storage, a piece of code and a balance.
Since I am interested in account states in the middle of a transaction, I also need to
keep track of the ongoing executions of a single account.  Also I need to keep track of
a flag indicating if the account has already marked for erasure.
*}

subsection {* Environment Construction before EVM Execution *}

text {* I need to connect the account state and the program execution environments.
First I construct program execution environments from an account state.
*}

text {* Given an account state and a call from the world
we can judge if a variable environment is possible or not.
The block state is arbitrary.  This means we verify properties that hold
on whatever block numbers and whatever difficulties and so on.
The origin of the transaction is also considered arbitrary.
*}
inductive build_venv_called :: "account_state \<Rightarrow> call_env \<Rightarrow> variable_env \<Rightarrow> bool"
where
venv_called:
  "bal (account_address a) =
   (* natural increase is taken care of in RelationalSem.thy *)
       account_balance a \<Longrightarrow>
   build_venv_called a env
   \<lparr> (* The stack is initialized for every invocation *)
     venv_stack = []

     (* The memory is also initialized for every invocation *)
   , venv_memory = empty_memory
   
     (* The memory usage is initialized. *)
   , venv_memory_usage = 0
   
     (* The storage is taken from the account state *)
   , venv_storage = account_storage a

     (* The program counter is initialized to zero *)
   , venv_pc = 0 

     (* The balance is arbitrary, except that the balance of this account *)
     (* is as specified in the account state plus the sent amount. *)
   , venv_balance = bal(account_address a := bal (account_address a) + callenv_value env) 

   (* the caller is specified by the world *)
   , venv_caller = callenv_caller env

   (* the sent value is specified by the world *)
   , venv_value_sent = callenv_value env 

   (* the sent data is specified by the world *)
   , venv_data_sent = callenv_data env 

   (* the snapshot of the storage is remembered in case of failure *)
   , venv_storage_at_call = account_storage a 

   (* the snapshot of the balance is remembered in case of failure *)
   , venv_balance_at_call = bal 

   (* the origin of the transaction is arbitrarily chosen *)
   , venv_origin = origin 

   (* the codes of the external programs are arbitrary. *)
   , venv_ext_program = ext 

   (* the block information is chosen arbitrarily. *)
   , venv_block = block 
   \<rparr>
   "

declare build_venv_called.simps [simp]

text {* Similarly we can construct the constant environment.
Construction of the constant environment is much simpler than that of 
a variable environment. 
*}

declare build_cenv_def [simp]

text "Next we turn to the case where the world returns back to the account after the account has
called an account.  In this case, the account should contain one ongoing execution that is waiting
for a call to return."

text "An instruction is ``call-like'' when it calls an account and waits for it to return."

declare is_call_like_def [simp]


text {* When an account returns to our contract, the variable environment is
recovered from the stack of the ongoing calls.  However, due to reentrancy,
the balance and the storage of our contract might have changed.  So the
balance and the storage are taken from the account state provided.
Moreover, the balance of
our contract might increase because some other contracts might have destroyed themselves,
transferring value to our contract.*}

function put_return_values :: "memory \<Rightarrow> byte list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> memory"
where
  "s \<le> 0 \<Longrightarrow> put_return_values orig _ _ s = orig"
| "s > 0 \<Longrightarrow> put_return_values orig [] _ s = orig"
| "s > 0 \<Longrightarrow> put_return_values orig (h # t) b s =
             put_return_values (orig(word_of_int b := h)) t (b + 1) (s - 1)"
apply(auto)
apply(case_tac "b \<le> 0"; auto?)
apply(case_tac aa; auto)
done

text {* When the control flow comes back to an account state
in the form of a return from an account,
we build a variable environment as follows.
The process is not deterministic because
the balance of our contract might have
arbitrarily increased.
*}

declare build_venv_returned.simps [simp]

text {* The situation is much simpler when an ongoing call has failed because anything 
meanwhile has no effects. *}

declare build_venv_failed_def [simp]

subsection {* Account State Update after EVM Execution *}

text {* Of course the other direction exists for constructing an account state after
the program executes. *}

text {* The first definition is about forgetting one ongoing call. *}

declare account_state_pop_ongoing_call_def [simp]

text {* Second I define the empty account, which replaces an account that has
destroyed itself. *}
declare empty_account_def [simp]

text {* And after our contract makes a move, the account state is updated as follows.
*}
                                     
text {* The above definition should be expanded automatically only when
the last argument is known to be None or Some \_.
*}
                                     
lemma update_account_state_None [simp] :
"update_account_state prev act st bal None =
   (prev \<lparr>
     account_storage := st,
     account_balance :=
       (case act of ContractFail \<Rightarrow> account_balance prev
                 |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls := account_ongoing_calls prev,
     account_killed :=
       (case act of ContractSuicide \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev) \<rparr>)"
apply(case_tac act; simp add: update_account_state_def)
done

lemma update_account_state_Some [simp] :
"update_account_state prev act st bal (Some pushed) =
   (prev \<lparr>
     account_storage := st,
     account_balance :=
       (case act of ContractFail \<Rightarrow> account_balance prev
                  |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls := pushed # account_ongoing_calls prev,
     account_killed :=
       (case act of ContractSuicide \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev)\<rparr>)"
apply(case_tac act; simp add: update_account_state_def)
done


subsection {* Controlling the Isabelle Simplifier *}

text {* This subsection contains simplification rules for the Isabelle simplifier.
The main purpose is to prevent the AVL tree implementation to compute both the
left insertion and the right insertion when actually only one of these happens.
*}

declare word_rcat_def [simp]
        unat_def [simp]
        bin_rcat_def [simp]
        word_of_bytes_def [simp]
        maybe_to_list.simps [simp]


text {* There is a common pattern for checking a predicate. *}

lemma iszero_iszero [simp] :
"((if b then (1 :: 256 word) else 0) = 0) = (\<not> b) "
apply(auto)
done

end
