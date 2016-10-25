section {* Some Data Types for EVM *}

text {* This development depends on Isabelle/HOL's machine word library.
The machine word library is one of the biggest reasons for choosing Isabelle/HOL
for this development.
The Ethereum Virtual Machine depends on 8-bit bytes and 256-bit machine words. *}

theory ContractEnv

imports Main "~~/src/HOL/Word/Word"

begin

text {* The frequently used machine words are named here.  For example, ``address''
denotes the type of
160-bit machine words.  The type ``uint'' denotes the type of EVM machine words. *}

type_synonym uint = "256 word"    -- {* 256 bit words *}
type_synonym address = "160 word" -- {* 160 bit addresses *}
type_synonym byte = "8 word"      -- {* 8 bit bytes *}

text {* In EVM, the memory contains one byte for each machine word.
The storage contains one machine word for each machine word.
As we will see, the memory is cleared for every invocation of smart contracts.
The storage is persistent for an account.
*}

type_synonym memory = "uint \<Rightarrow> byte"
type_synonym storage = "uint \<Rightarrow> uint"

text {* The storage is modelled as a function.  For example, the empty storage
is a function that returns zero for every index.  Initially all accounts come with
the empty storage. *}

definition empty_storage :: storage
where
"empty_storage = (\<lambda> _. 0)"

text {* \noindent During proofs, the definition of @{term empty_storage} is expanded
automatically. *}

declare empty_storage_def [simp]

text {* The empty memory is very similar. *}

definition empty_memory :: memory
where
"empty_memory = (\<lambda> _. 0)"

declare empty_memory_def [simp]

text {* \indent
The following record lists the information available for bytecode-inline assertions.
These assertions will be proved in Isabelle/HOL. *}

(* The environment visible for annotations *)
record aenv =
  aenv_stack :: "uint list" -- {* The current stack *}
  aenv_memory :: memory -- {* The current memory *}
  aenv_storage :: storage -- {* The current storage *}
  aenv_balance :: "address \<Rightarrow> uint" -- {* The current balance of all accounts *}
  aenv_caller :: address -- {* The caller of the current invocation. *}
  aenv_value_sent :: uint -- {* The amount of Eth sent alont the current invocation. *}
  aenv_data_sent :: "byte list" -- {* The data sent along the current invocation. *}
  aenv_storage_at_call :: storage -- {* The storage content at the time of the invocation. *}
  aenv_balance_at_call :: "address \<Rightarrow> uint"
  -- {* The balance of all accounts at the time of the invocation *}
  aenv_this :: address -- {* The address of this contract under verification. *}
  aenv_origin :: address -- {* The external account that started the transaction. *}

text {* @{term aenv_balance} field keeps track of the balance of all accounts because the contract
under verification can send some Eth to other accounts.  To capture the effect of this, I chose to
keep track of the balances of the other contracts.  *}

text {* @{term aenv_storage_at_call} and @{term aenv_balance_at_call} fields keep the states at the
time of the contract invocation.  These are used for rolling back the state after a failure.
Failures happen for example when the contract under verification jumps to a wrong destination,
or it runs out of gas. *}

text {* @{term aenv_origin} might be the same as but might be different from @{term aenv_caller}.
An Ethereum transaction is started by an external account (that is, an account which does not
have codes but owned by somebody with a secret key).  @{term aenv_origin} denotes this external
account.  During a transaction, the origin first sends a message to an account, the receiver can
in turn call other accounts as well.  When the calls nest, @{term aenv_caller} points to the
immediate caller.
*}

text {* I'm going to add more fields in the @{typ aenv} record in the near future because
it does not contain all the information available at the execution time. *}
  
end
