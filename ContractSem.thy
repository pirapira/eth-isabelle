section "A Contract Centric View of the EVM"

text {* Here is a presentation of the Ethereum Virtual Machine (EVM) in a form
suitable for formal verification of a single account.  *}

theory ContractSem

imports Main "~~/src/HOL/Word/Word" "~~/src/HOL/Data_Structures/AVL_Map" "./ContractEnv" "./Instructions" "./KEC"

begin

subsection "Utility Functions"

text {* The following function is an if sentence, but with some strict control
over the evaluation order.  By default, neither the then-clause nor the else-clause
is simplified during proofs.  This prevents the automatic simplifier from
computing the results of both the then-clause and the else-clause.
*}

definition strict_if :: "bool \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> 'a"
where
"strict_if b x y = (if b then x True else y True)"

text {* When the if-condition is known to be True, the simplifier can
proceed into the then-clause.  *}

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
the simplifier is allowed to perform computation on the if-condition. *}

lemma strict_if_cong [cong] :
"b0 = b1 \<Longrightarrow> strict_if b0 x y = strict_if b1 x y"
apply(auto)
done

subsection "The Interaction between the Contract and the World"

text "In this development, the EVM execution is seen as an interaction between the contract
and the rest of the world.  The world can call into the contract.  The contract can reply by just
finishing or failing, but it can also call an account.  When the contract calls an account,
this is seen as an action towards the world, because the world then has to decide the
result of this call.  The world can say that the call finished successfully or in an exceptional
state.  The world can also say that the call resulted in a reentrancy.  In other words,
the world can call the contract again.  The whole process is captured as a game between
the world and the contract."

subsubsection "The World's Moves"

text {* The world can call into our contract.
Then the world provides our\footnote{
The contract's behavior is controlled by a concrete code, but the world's behavior is unrestricted.
So when I get emotional I call the contract ``our'' contract.
} contract
with the following information.*}

record call_env =
  callenv_gaslimit :: w256 -- {* the current block's gas limit *}
  callenv_value :: w256 -- {* the amount of Eth sent along*}
  callenv_data :: "byte list" -- {* the data sent along *}
  callenv_caller :: address -- {* the caller's address *}
  callenv_timestamp :: w256 -- {* the timestamp of the current block *}
  callenv_blocknum :: w256 -- {* the block number of the current block *}
  callenv_balance :: "address \<Rightarrow> w256" -- {* the balances of all accounts. *}
  
text {* After our contract calls accounts, the world can make those accounts
return into our contracts.  The return value is not under control of our current
contract, so it is the world's move.  In that case, the world provides the
following information.*}

record return_result =
  return_data :: "byte list" -- {* the returned data *}
  return_balance :: "address \<Rightarrow> w256"
  -- {* the balance of all accounts at the moment of the return*}

text {* Even our account's balance (and its storage) might have changed at this moment.
@{typ return_result} type is also used when our contract returns, as we will see. *}

text {* With these definitions now we can define the world's actions.  In addition to call and return,
there is another clause for failing back to the account.  This happens when our contract calls
an account but the called account fails. *}

datatype world_action =
  WorldCall call_env -- {* the world calls into the account *}
| WorldRet return_result -- {* the world returns back to the account *}
| WorldFail -- {* the world fails back to the account. *}

subsubsection "The Contract's Moves"

text {* After being invoked, the contract can respond by calling an account, creating (or deploying
a smart contract, destroying itself, returning, or failing.  When the contract calls an account,
the contract provides the following information.*}

record call_arguments =
  callarg_gas :: w256 -- {* The portion of the remaining gas that the callee is allowed to use *}
  callarg_code :: address -- {* The code that executes during the call *}
  callarg_recipient :: address -- {* The recipient of the call, whose balance and the storage are modified. *}
  callarg_value :: w256 -- {* The amount of Eth sent along *}
  callarg_data :: "byte list" -- {* The data sent along *}
  callarg_output_begin :: w256 -- {* The beginning of the memory region where the output data should be written. *}
  callarg_output_size :: w256 -- {* The size of the memory regions where the output data should be written. *}
  
text {* When our contract deploys a smart contract, our contract should provide the following
information. *}

record create_arguments =
  createarg_value :: w256 -- {* The value sent to the account *}
  createarg_code :: "byte list" -- {* The code that deploys the runtime code. *}

text {* The contract's moves are summarized as follows. *}
  
datatype contract_action =
  ContractCall call_arguments -- {* calling an account *}
| ContractCreate create_arguments -- {* deploying a smart contract *}
| ContractFail -- {* failing back to the caller *}
| ContractSuicide -- {* destroying itself and returning back to the caller *}
| ContractReturn "byte list" -- {* normally returning back to the caller *}

subsection "Program Representation"

text "For performance reasons, the instructions are stored in an AVL tree that allows
looking up instructions from the program counters."

record program = 
  program_content :: "(int * inst) avl_tree"
  -- {* a binary search tree that allows looking up instructions from positions *}
  program_length  :: int -- {* the length of the program in bytes *}
  program_annotation :: "int \<Rightarrow> annotation list"
  -- {* a mapping from positions to annotations *}

text {* The empty program is easy to define. *}

abbreviation empty_program :: program
where
"empty_program ==
  \<lparr> program_content = \<langle>\<rangle>
  , program_length = 0
  , program_annotation = (\<lambda> _. []) \<rparr>"


subsection "Translating an Instruction List into a Program"

subsubsection {* Integers can be compared *}

text {* The AVL library requires the keys to be comparable.  We represent program positions 
by integers.  So we have to prove that integers belong to the type class cmp with the
usual comparison operators.  *}

instantiation int :: cmp
begin
definition cmp_int :: "int \<Rightarrow> int \<Rightarrow> Cmp.cmp"
where
cmp_int_def : " cmp_int x y =
  (if x < y then Cmp.LT else (if x = y then Cmp.EQ else Cmp.GT))"

instance proof
 fix x y :: int show "(cmp x y = cmp.LT) = (x < y)"
  apply(simp add: cmp_int_def)
  done
 fix x y :: int show "(cmp x y = cmp.EQ) = (x = y)"
  apply(simp add: cmp_int_def)
  done
 fix x y :: int show "(cmp x y = cmp.GT) = (x > y)"
  apply(simp add: cmp_int_def)
  done
qed

end

subsubsection {* Storing the immediate values in the AVL tree *}

text {* The data region of PUSH\_N instructions are encoded as
 Unknown instructions.  Here is a utility function that
 inserts a byte sequence after a specified index in the AVL tree. *}

fun store_byte_list_in_program ::
  "int (* initial position in the AVL *) \<Rightarrow> byte list (* the data *) \<Rightarrow>
   (int * inst) avl_tree (* original AVL *)  \<Rightarrow>
   (int * inst) avl_tree (* result *)"
where
  "store_byte_list_in_program _ [] orig = orig"
| "store_byte_list_in_program pos (h # t) orig =
     store_byte_list_in_program (pos + 1) t (update pos (Unknown h) orig)"
declare store_byte_list_in_program.simps [simp]

subsubsection {* Storing a program in the AVL tree *}

text {* Here is a function that stores a list of instructions in the AVL tree.
The initial key is specified.  The following keys are computed using the sizes
of instructions being inserted.
*}

fun program_content_of_lst ::
  "int (* initial position in the AVL *) \<Rightarrow> inst list (* instructions *)
   \<Rightarrow> (int * inst) avl_tree (* result *)"
where
  "program_content_of_lst _ [] = Leaf"
  -- {* the empty program is translated into the empty tree. *}
| "program_content_of_lst pos (Stack (PUSH_N bytes) # rest) =
   store_byte_list_in_program (pos + 1) bytes 
   (update pos (Stack (PUSH_N bytes))
          (program_content_of_lst (pos + 1 + (int (length bytes))) rest))"
  -- {* The PUSH instruction is translated together with the immediate value. *}
| "program_content_of_lst pos (Annotation _ # rest) =
    program_content_of_lst pos rest"
  -- {* Annotations are skipped because they do not belong in this AVL tree. *}
| "program_content_of_lst pos (i # rest) =
   update pos i (program_content_of_lst (pos + 1) rest)"
  -- {* The other instructions are simply inserted into the AVL tree. *}

subsubsection {* Storing annotations in a program in a mapping *}

text {* Annotations are stored in a mapping that maps positions into lists of annotations.
The rationale for this data structure is that a single position might contain multiple annotations.
Here is a function that inserts an annotation
at a specified position. *}

abbreviation prepend_annotation :: "int \<Rightarrow> annotation \<Rightarrow> (int \<Rightarrow> annotation list) \<Rightarrow> (int \<Rightarrow> annotation list)"
where
"prepend_annotation pos annot orig \<equiv> orig(pos := annot # orig pos)"
text {* Currently annotations are inserted into a mapping with Isabelle/HOL's mapping updates.
When this causes performance problems, I need to switch to AVL trees again.
*}

fun program_annotation_of_lst :: "int \<Rightarrow> inst list \<Rightarrow> int \<Rightarrow> annotation list"
where
  "program_annotation_of_lst _ [] = (\<lambda> _. [])"
| "program_annotation_of_lst pos (Annotation annot # rest) =
    prepend_annotation pos annot (program_annotation_of_lst pos rest)"
| "program_annotation_of_lst pos (i # rest) =
   (program_annotation_of_lst (pos + inst_size i) rest)"
   -- {* Ordinary instructions are skipped. *}

declare program_annotation_of_lst.simps [simp]

subsubsection {* Translating a list of instructions into a program *}

text {* The results of the above translations are packed together in a record. *}

abbreviation program_of_lst :: "inst list \<Rightarrow> program"
where
"program_of_lst lst \<equiv>
  \<lparr> program_content = program_content_of_lst 0 lst
  , program_length = int (length lst)
  , program_annotation = program_annotation_of_lst 0 lst
  \<rparr>"

subsection {* Program as a Byte Sequence *}

text {* For CODECOPY instruction, the program must be seen as a byte-indexed read-only memory. *}
text {* Such a memory is here implemented by a lookup on an AVL tree.*}

abbreviation program_as_memory :: "program \<Rightarrow> memory"
where
"program_as_memory p idx ==
   (case lookup (program_content p) (uint idx) of
     None \<Rightarrow> 0
   | Some inst \<Rightarrow> inst_code inst ! 0
   )"
   
subsection {* Execution Environments *}

text "I model an instruction as a function that takes environments and modify some parts of them."

text "The execution of an EVM program happens in a block, and the following information about
the block should be available."

record block_info =
  block_blockhash :: "w256 \<Rightarrow> w256" -- {* this captures the whole BLOCKHASH operation *}
  block_coinbase :: address -- {* the miner who validates the block *}
  block_timestamp :: w256
  block_number :: w256 -- {* the blocknumber of the block *}
  block_difficulty :: w256
  block_gaslimit :: w256 -- {* the block gas imit *}
  block_gasprice :: w256

text {* The variable environment contains information that are relatively volatile. *}

record variable_env =
  venv_stack :: "w256 list"
  venv_memory :: memory
  venv_memory_usage :: int -- {* the current memory usage *}
  venv_storage :: storage
  venv_pc :: int -- {* the program counter *}
  venv_balance :: "address \<Rightarrow> w256" -- {* balances of all accounts *}
  venv_caller :: address -- {* the caller's address *}
  venv_value_sent :: w256 -- {* the amount of Eth sent along the current invocation *}
  venv_data_sent :: "byte list" -- {* the data sent along the current invocation *}
  venv_storage_at_call :: storage -- {* the storage content at the invocation*}
  venv_balance_at_call :: "address \<Rightarrow> w256" -- {* the balances at the invocation *}
  venv_origin :: address -- {* the external account that started the current transaction *}
  venv_ext_program :: "address \<Rightarrow> program" -- {* the codes of all accounts *}
  venv_block :: block_info -- {* the current block *}

text {* The constant environment contains information that are rather stable. *}

record constant_env =
  cenv_program :: program -- {* the code in the account under verification. *}
  cenv_this :: address -- {* the address of the account under verification. *}

subsection {* The Result of an Instruction *}

text {* The result of program execution is microscopically defined by results of instruction
executions.  The execution of a single instruction can result in the following cases: *}

datatype instruction_result =
  InstructionContinue variable_env -- {* the execution should continue. *}
| InstructionAnnotationFailure -- {* the annotation turned out to be false. *}
| InstructionToWorld
-- {* the execution has stopped; either for the moment just calling out another account, or
finally finishing the current invocation.
*}  
   " contract_action   (* the contract's move *)
   * storage           (* the new storage content *)
   * (address \<Rightarrow> w256) (* the new balance of all accounts *)
   * (variable_env \<times> int \<times> int) option
     (* the variable environment to return to, *)
     (* and the memory reagion that expects the return value *)"

text {* When the contract fails, the result of the instruction always looks like this: *}
abbreviation instruction_failure_result :: "variable_env \<Rightarrow> instruction_result"
where
"instruction_failure_result v \<equiv>
  InstructionToWorld (ContractFail, venv_storage_at_call v, venv_balance_at_call v, None)"

text {* When the contract returns, the result of the instruction always looks like this: *}
abbreviation instruction_return_result :: "byte list \<Rightarrow> variable_env \<Rightarrow> instruction_result"
where
"instruction_return_result x v \<equiv>
  InstructionToWorld (ContractReturn x, venv_storage v, venv_balance v, None)"

subsection {* Useful Functions for Defining EVM Operations *}

text {* Currently the GAS instruction is modelled to return random numbers.
The random number is not known to be of any value.
However, the value is not unknown enough in this formalization because
the value is only dependent on the variable environment (which does not
keep track of the remaining gas).  This is not a problem as long as
we are analyzing a single invocation of a loopless contract, but
will be fixed.
*}

definition gas :: "variable_env \<Rightarrow> w256"
where "gas _ = undefined"

text {* This M function is defined at the end of H.1. in the yellow paper.
The purpose of this is to update the memory usage. *}

abbreviation M ::
"int (* original memory usage *) \<Rightarrow> w256 (* beginning of the used memory *)
 \<Rightarrow> w256 (* used size *) \<Rightarrow> int (* the updated memory usage *)"
where
"M s f l \<equiv>
  (if l = 0 then s else
     max s ((uint f + uint l + 31) div 32))"

text {* Updating a balance of a single account:  *}
abbreviation update_balance ::
"  address (* the updated account*)
\<Rightarrow> (w256 \<Rightarrow> w256) (* the function that updates the balance *)
\<Rightarrow> (address \<Rightarrow> w256) (* the original balance *)
\<Rightarrow> (address \<Rightarrow> w256) (* the resulting balance *)"
where
"update_balance a f orig \<equiv> orig(a := f (orig a))"

text {* Popping stack elements: *}
abbreviation venv_pop_stack ::
"nat (* how many elements to pop *) \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
 "venv_pop_stack n v ==
   v\<lparr> venv_stack := drop n (venv_stack v) \<rparr>"

text {* Peeking the topmost element of the stack: *}
abbreviation venv_stack_top :: "variable_env \<Rightarrow> w256 option"
where
"venv_stack_top v \<equiv>
  (case venv_stack v of h # _\<Rightarrow> Some h | [] \<Rightarrow> None)"

text {* Updating the storage at an index: *}

abbreviation venv_update_storage ::
" w256 (* index *) \<Rightarrow> w256 (* value *)
\<Rightarrow> variable_env (* the original variable environment *)
\<Rightarrow> variable_env (* the resulting variable environment *)"
where
"venv_update_storage idx val v \<equiv>
  v\<lparr>venv_storage := (venv_storage v)(idx := val)\<rparr>"
  
text {* Peeking the next instruction: *}
abbreviation venv_next_instruction :: "variable_env \<Rightarrow> constant_env \<Rightarrow> inst option"
where
"venv_next_instruction v c \<equiv>
   lookup (program_content (cenv_program c)) (venv_pc v)"
   
text {* Advancing the program counter: *}
abbreviation venv_advance_pc :: "constant_env \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
"venv_advance_pc c v \<equiv> 
  v\<lparr> venv_pc := venv_pc v + inst_size (the (venv_next_instruction v c))  \<rparr>"

text {* No-op, which just advances the program counter: *}
abbreviation stack_0_0_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stack_0_0_op v c \<equiv> InstructionContinue (venv_advance_pc c v)"

text {* A general pattern of operations that pushes one element onto the stack.  *}
abbreviation stack_0_1_op ::
  "variable_env \<Rightarrow> constant_env \<Rightarrow> w256 (* the pushed word *) \<Rightarrow> instruction_result"
where
"stack_0_1_op v c w \<equiv>
   InstructionContinue
      (venv_advance_pc c v\<lparr>venv_stack := w # venv_stack v\<rparr>)"

text {* A general pattern of operations that transforms the topmost element of the stack. *}
abbreviation stack_1_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow>
   (w256 \<Rightarrow> w256) (* the function that transforms a word*)
   \<Rightarrow> instruction_result"
where
"stack_1_1_op v c f \<equiv>
   (case venv_stack v of
      [] \<Rightarrow> instruction_failure_result v
      | h # t \<Rightarrow>
         InstructionContinue
           (venv_advance_pc c v\<lparr>venv_stack := f h # t\<rparr>)
      )"

text {* A general pattern of operations that consume one word and produce two rwords: *}
abbreviation stack_1_2_op ::
"variable_env \<Rightarrow> constant_env \<Rightarrow> (w256 \<Rightarrow> w256 * w256) \<Rightarrow> instruction_result"
where
"stack_1_2_op v c f \<equiv>
  (case venv_stack v of
     [] \<Rightarrow> instruction_failure_result v
   | h # t \<Rightarrow>
     (case f h of
        (new0, new1) \<Rightarrow>
          InstructionContinue
            (venv_advance_pc c
               v\<lparr>venv_stack := new0 # new1 # t \<rparr>)))"

text {* A general pattern of operations that take two words and produce one word: *}
abbreviation stack_2_1_op ::
"variable_env \<Rightarrow> constant_env \<Rightarrow> (w256 \<Rightarrow> w256 \<Rightarrow> w256) \<Rightarrow> instruction_result"
where
"stack_2_1_op v c f \<equiv>
  (case venv_stack v of
     operand0 # operand1 # rest \<Rightarrow>
       InstructionContinue
         (venv_advance_pc c
            v\<lparr>venv_stack := f operand0 operand1 # rest\<rparr>)
  | _ \<Rightarrow> instruction_failure_result v)"

text {* A general pattern of operations that take three words and produce one word: *}
abbreviation stack_3_1_op ::
"variable_env \<Rightarrow> constant_env \<Rightarrow>
 (w256 \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256) \<Rightarrow> instruction_result"
where
"stack_3_1_op v c f \<equiv>
  (case venv_stack v of
     operand0 # operand1 # operand2 # rest \<Rightarrow>
       InstructionContinue
         (venv_advance_pc c
            v\<lparr>venv_stack := f operand0 operand1 operand2 # rest\<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)"

subsection {* Definition of EVM Operations *}

text "SSTORE changes the storage so it does not fit into any of the patterns defined above."
abbreviation sstore :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sstore v c \<equiv>
  (case venv_stack v of
    addr # val # stack_tail \<Rightarrow>
      InstructionContinue
      (venv_advance_pc c
        (venv_update_storage addr val v\<lparr>venv_stack := stack_tail\<rparr>))
    | _ \<Rightarrow> instruction_failure_result v)"


text "For interpreting the annotations, I first need to construct the annotation environment
out of the current execution environments.  When I try to remove this step, I face some
circular definitions of data types."
abbreviation build_aenv :: "variable_env \<Rightarrow> constant_env \<Rightarrow> aenv"
where
"build_aenv v c \<equiv>
  \<lparr> aenv_stack = venv_stack v
  , aenv_memory = venv_memory v
  , aenv_storage = venv_storage v
  , aenv_balance = venv_balance v
  , aenv_caller = venv_caller v
  , aenv_value_sent = venv_value_sent v
  , aenv_data_sent = venv_data_sent v
  , aenv_storage_at_call = venv_storage_at_call v
  , aenv_balance_at_call = venv_balance_at_call v
  , aenv_this = cenv_this c
  , aenv_origin = venv_origin v \<rparr>"

text "In reality, EVM programs do not contain annotations so annotations never cause failures.
However, during the verification, I want to catch annotation failures.  When the annotation
evaluates to False, the execution stops and results in @{term InstructionAnnotationFailure}."
definition eval_annotation :: "annotation \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"eval_annotation anno v c =
   (if anno (build_aenv v c) then InstructionContinue (venv_advance_pc c v)
    else InstructionAnnotationFailure)"
    
text "The JUMP instruction has the following meaning.  When it cannot find the JUMPDEST instruction
at the destination, the execution fails."
abbreviation jump :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jump v c \<equiv>
  (case venv_stack_top v of
     None \<Rightarrow> instruction_failure_result v
   | Some pos \<Rightarrow>
     (let v_new = (venv_pop_stack (Suc 0) v)\<lparr> venv_pc := uint pos \<rparr>  in
     (case venv_next_instruction v_new c of
        Some (Pc JUMPDEST) \<Rightarrow>
          InstructionContinue v_new
      | Some _ \<Rightarrow> instruction_failure_result v
      | None \<Rightarrow> instruction_failure_result v )))"

text {* This function is a reminiscent of my struggle with the Isabelle/HOl simplifier.
The second argument has no meaning but to control the Isabelle/HOL simplifier.
*}
definition blockedInstructionContinue :: "variable_env \<Rightarrow> bool \<Rightarrow> instruction_result"
where
"blockedInstructionContinue v _ = InstructionContinue v"

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
definition blocked_jump :: "variable_env \<Rightarrow> constant_env \<Rightarrow> bool \<Rightarrow> instruction_result"
where
"blocked_jump v c _ = jump v c"

lemma unblock_jump [simp]:
"blocked_jump v c True = jump v c"
apply(simp add: blocked_jump_def)
done

text {* The JUMPI instruction is implemented using the JUMP instruction.
*}
abbreviation jumpi :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jumpi v c \<equiv>
  (case venv_stack v of
      pos # cond # rest \<Rightarrow>
        (strict_if (cond = 0)
           (blockedInstructionContinue
             (venv_advance_pc c (venv_pop_stack (Suc (Suc 0)) v)))
           (blocked_jump (v\<lparr> venv_stack := pos # rest \<rparr>) c))
    | _ \<Rightarrow> instruction_failure_result v)"

text {* Looking up the call data size takes this work: *}
abbreviation datasize :: "variable_env \<Rightarrow> w256"
where
"datasize v == Word.word_of_int (int (length (venv_data_sent v)))"

text {* Looking up a word from a list of bytes: *}
abbreviation read_word_from_bytes :: "nat \<Rightarrow> byte list \<Rightarrow> w256"
where
"read_word_from_bytes idx lst ==
   Word.word_rcat (take 32 (drop idx lst))"

text {* Looking up a word from the call data: *}
abbreviation cut_data :: "variable_env \<Rightarrow> w256 \<Rightarrow> w256"
where
"cut_data v idx ==
    read_word_from_bytes (Word.unat idx) (venv_data_sent v)"

text {* Looking up a number of bytes from the memory: *}
fun cut_memory :: "w256 \<Rightarrow> nat \<Rightarrow> (w256 \<Rightarrow> byte) \<Rightarrow> byte list"
where
"cut_memory idx 0 memory = []" |
"cut_memory idx (Suc n) memory =
  memory idx # cut_memory (idx + 1) n memory"
  
declare cut_memory.simps [simp]

text {* CALL instruction results in @{term ContractCall} action when successful. *}
definition call :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"call v c =
  (case venv_stack v of
    e0 # e1 # e2 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
    (if venv_balance v (cenv_this c) < e2 then
       instruction_failure_result v
     else
       InstructionToWorld (ContractCall
         (\<lparr> callarg_gas = e0
          , callarg_code = Word.ucast e1
          , callarg_recipient = Word.ucast e1
          , callarg_value = e2
          , callarg_data = cut_memory e3 (Word.unat e4) (venv_memory v)
          , callarg_output_begin = e5
          , callarg_output_size = e6 \<rparr>),
        venv_storage v,
        update_balance (cenv_this c)
          (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v),
        Some (* saving the variable environment for timing *)
          ((venv_advance_pc c v)
           \<lparr> venv_stack := rest
           , venv_balance :=
                update_balance (cenv_this c)
                  (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v)
           , venv_memory_usage :=
              M (M (venv_memory_usage v) e3 e4) e5 e6 \<rparr>, uint e5, uint e6)))
  | _ \<Rightarrow> instruction_failure_result v)"

declare call_def [simp]

text {* DELEGATECALL is slightly different. *}
definition delegatecall :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"delegatecall v c =
  (case venv_stack v of
    e0 # e1 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
    (if venv_balance v (cenv_this c) < venv_value_sent v then
       instruction_failure_result v
     else
       InstructionToWorld
         (ContractCall
           (\<lparr> callarg_gas = e0,
              callarg_code = Word.ucast e1,
              callarg_recipient = Word.ucast e1,
              callarg_value = venv_value_sent v,
              callarg_data = 
                cut_memory e3 (Word.unat e4) (venv_memory v),
              callarg_output_begin = e5,
              callarg_output_size = e6 \<rparr>),
          venv_storage v, venv_balance v,
          Some (* save the variable environment for returns *)
            ((venv_advance_pc c v)
             \<lparr> venv_stack := rest
             , venv_memory_usage :=
                M (M (venv_memory_usage v) e3 e4) e5 e6 \<rparr>, uint e5, uint e6 )))
  | _ \<Rightarrow> instruction_failure_result v
  )"

declare delegatecall_def [simp]

text {* CALLCODE is another variant. *}

abbreviation callcode :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"callcode v c ==
  (case venv_stack v of
    e0 # e1 # e2 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
    (if venv_balance v (cenv_this c) < e2 then
       instruction_failure_result v
     else
       InstructionToWorld
         (ContractCall
           (\<lparr> callarg_gas = e0,
              callarg_code = ucast e1,
              callarg_recipient = cenv_this c,
              callarg_value = e2,
              callarg_data =
                cut_memory e3 (unat e4) (venv_memory v),
              callarg_output_begin = e5,
              callarg_output_size = e6 \<rparr>),
          venv_storage v,
          update_balance (cenv_this c)
            (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v),
          Some (* saving the variable environment *)
            ((venv_advance_pc c v)
              \<lparr> venv_stack := rest
              , venv_memory_usage :=
                  M (M (venv_memory_usage v) e3 e4) e5 e6
              , venv_balance :=
                  update_balance (cenv_this c)
                    (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v) \<rparr>, uint e5, uint e6
             )))
  | _ \<Rightarrow> instruction_failure_result v)"

text "CREATE is also similar because the instruction causes execution on another account."
abbreviation create ::
  "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"create v c \<equiv>
  (case venv_stack v of
    val # code_start # code_len # rest \<Rightarrow>
      (if venv_balance v (cenv_this c) < val then
         instruction_failure_result v
       else
         let code =
            cut_memory code_start
              (unat code_len) (venv_memory v) in
         let new_balance =
            update_balance (cenv_this c)
              (\<lambda> orig. orig - val) (venv_balance v) in
         InstructionToWorld
           (ContractCreate
             (\<lparr> createarg_value = val
              , createarg_code = code \<rparr>),
            venv_storage v,
            update_balance (cenv_this c)
              (\<lambda> orig. orig - val) (venv_balance v),
            Some (* save the variable environment for returns *)
              ((venv_advance_pc c v)
               \<lparr> venv_stack := rest
               , venv_balance :=
                   update_balance (cenv_this c)
                     (\<lambda> orig. orig - val) (venv_balance v)
               , venv_memory_usage :=
                   M (venv_memory_usage v) code_start code_len \<rparr>, 0, 0)))
  | _ \<Rightarrow> instruction_failure_result v)"

  
text "For implementing RETURN, I need to cut a region from the memory
according to the stack elements:"
definition
"venv_returned_bytes v =
  (case venv_stack v of
    e0 # e1 # _ \<Rightarrow> cut_memory e0 (Word.unat e1) (venv_memory v)
  | _ \<Rightarrow> [])"

text "RETURN is modeled like this:"
abbreviation ret :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"ret v c \<equiv>
   (case venv_stack v of
      e0 # e1 # rest \<Rightarrow>
        let new_v = v\<lparr> venv_memory_usage := M (venv_memory_usage v) e0 e1 \<rparr> in
        InstructionToWorld ((ContractReturn (venv_returned_bytes new_v)),
                           venv_storage v, venv_balance v,
                           None (* No possibility of ever returning to this invocation. *))
   | _ \<Rightarrow> instruction_failure_result v)"

text "STOP is a simpler than RETURN:"
abbreviation stop ::
"variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stop v c \<equiv> InstructionToWorld (ContractReturn [], venv_storage v, venv_balance v, None)"

text "POP:"
abbreviation pop ::
"variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"pop v c \<equiv> InstructionContinue (venv_advance_pc c
             v\<lparr>venv_stack := tl (venv_stack v)\<rparr>)"

text "The DUP instructions:"
abbreviation general_dup ::
"nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"general_dup n v c \<equiv>
   (if n > length (venv_stack v) then instruction_failure_result v else
   (let duplicated = venv_stack v ! (n - 1) in
    InstructionContinue (venv_advance_pc c v\<lparr> venv_stack := duplicated # venv_stack v \<rparr>)))
"

text "A utility function for storing a list of bytes in the memory:"
fun store_byte_list_memory :: "w256 \<Rightarrow> byte list \<Rightarrow> memory \<Rightarrow> memory"
where
  "store_byte_list_memory _ [] orig = orig"
| "store_byte_list_memory pos (h # t) orig =
     store_byte_list_memory (pos + 1) t (orig(pos := h))"

declare store_byte_list_memory.simps [simp]

text "Using the function above, it is straightforward to store a byte in the memory."
abbreviation store_word_memory :: "w256 \<Rightarrow> w256 \<Rightarrow> memory \<Rightarrow> memory"
where
"store_word_memory pos val mem ==
   store_byte_list_memory pos (word_rsplit val) mem"

text "MSTRE:"
abbreviation mstore :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"mstore v c ==
   (case venv_stack v of
     [] \<Rightarrow> instruction_failure_result v
   | [_] \<Rightarrow> instruction_failure_result v
   | pos # val # rest \<Rightarrow>
       let new_memory = store_word_memory pos val (venv_memory v) in
       InstructionContinue (venv_advance_pc c
         v\<lparr> venv_stack := rest
          , venv_memory := new_memory
          , venv_memory_usage := M (venv_memory_usage v) pos 32
          \<rparr>)
   )
"

text "MLOAD:"
abbreviation mload :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"mload v c ==
  (case venv_stack v of
    pos # rest \<Rightarrow>
      let value = word_rcat (cut_memory pos 32 (venv_memory v)) in
      InstructionContinue (venv_advance_pc c
        v \<lparr> venv_stack := value # rest
          , venv_memory_usage := M (venv_memory_usage v) pos 32
          \<rparr>)
  | _ \<Rightarrow> instruction_failure_result v)"

text "MSTORE8:"
abbreviation mstore8 :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"mstore8 v c ==
  (case venv_stack v of
     pos # val # rest \<Rightarrow>
        let new_memory = (venv_memory v)(pos := ucast val) in
        InstructionContinue (venv_advance_pc c
          v\<lparr> venv_stack := rest
           , venv_memory_usage := M (venv_memory_usage v) pos 8
           , venv_memory := new_memory \<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)
           "

text "For CALLDATACOPY, I need to look at the caller's data as memory."
abbreviation input_as_memory :: "byte list \<Rightarrow> memory"
where
"input_as_memory lst idx ==
   (if length lst \<le> unat idx then 0 else
    lst ! unat idx)"

text "CALLDATACOPY:"
abbreviation calldatacopy :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"calldatacopy v c ==
  (case venv_stack v of
     (dst_start :: w256) # src_start # len # rest \<Rightarrow>
       let data = cut_memory src_start (unat len) (input_as_memory (venv_data_sent v)) in
       let new_memory = store_byte_list_memory dst_start data (venv_memory v) in
       InstructionContinue (venv_advance_pc c
         v\<lparr> venv_stack := rest, venv_memory := new_memory,
            venv_memory_usage := M (venv_memory_usage v) dst_start len
         \<rparr>))"

text "CODECOPY:"
abbreviation codecopy :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"codecopy v c ==
  (case venv_stack v of
     dst_start # src_start # len # rest \<Rightarrow>
     let data = cut_memory src_start (unat len)
                  (program_as_memory (cenv_program c)) in
     let new_memory = store_byte_list_memory dst_start data (venv_memory v) in
     InstructionContinue (venv_advance_pc c
       v\<lparr> venv_stack := rest, venv_memory := new_memory
       , venv_memory_usage := M (venv_memory_usage v) dst_start len
       \<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)"

text "EXTCODECOPY:"
abbreviation extcodecopy :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"extcodecopy v c ==
  (case venv_stack v of
     addr # dst_start # src_start # len # rest \<Rightarrow>
     let data = cut_memory src_start (unat len)
                  (program_as_memory
                    (venv_ext_program v (ucast addr))) in
     let new_memory = store_byte_list_memory dst_start data (venv_memory v) in
     InstructionContinue (venv_advance_pc c
       v\<lparr> venv_stack := rest, venv_memory := new_memory,
       venv_memory_usage := M (venv_memory_usage v) dst_start len
       \<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)"

text "PC instruction could be implemented by @{term stack_0_1_op}:"
abbreviation pc :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"pc v c ==
   InstructionContinue (venv_advance_pc c
     v\<lparr> venv_stack := word_of_int (venv_pc v) # venv_stack v \<rparr>)"

text "Logging is currently no-op, until some property about event logging is wanted."
definition log :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"log n v c =
   InstructionContinue (venv_advance_pc c
     (venv_pop_stack (Suc (Suc n)) v))"
     
declare log_def [simp]

text "For SWAP operations, I first define a swap operations on lists."
definition list_swap :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list option"
where
"list_swap n lst =
  (if length lst < n + 1 then None else
  Some (concat [[lst ! n], take (n - 1) (drop 1 lst) , [lst ! 0], drop (1 + n) lst]))"
  
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

text "Using this, I can specify the SWAP operations:"
definition swap :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"swap n v c = (* SWAP3 is modeled by swap 3 *)
   (case list_swap n (venv_stack v) of
      None \<Rightarrow> instruction_failure_result v
    | Some new_stack \<Rightarrow>
      InstructionContinue (venv_advance_pc c v\<lparr> venv_stack := new_stack \<rparr>))"

declare swap_def [simp]

text {* SHA3 instruciton in the EVM is actually Keccak 256.
In this development, Keccak256 computation is defined in KEC.thy.
*}
definition sha3 :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sha3 v c ==
  (case venv_stack v of
    start # len # rest \<Rightarrow>
      InstructionContinue (
        venv_advance_pc c v\<lparr> venv_stack := keccack
                                         (cut_memory start (unat len) (venv_memory v))
                                        # rest
                        , venv_memory_usage := M (venv_memory_usage v) start len
                        \<rparr>)
  | _ \<Rightarrow> instruction_failure_result v
  )"

declare sha3_def [simp]

text "The SUICIDE instruction involves value transfer."
definition suicide :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"suicide v c =
  (case venv_stack v of 
     dst # _ \<Rightarrow>
       let new_balance = (venv_balance v)(cenv_this c := 0,
         ucast dst := venv_balance v (cenv_this c) + (venv_balance v (ucast dst))) in
       InstructionToWorld (ContractSuicide,venv_storage v, new_balance, None)
    | _ \<Rightarrow> instruction_failure_result v)"

declare suicide_def [simp]

text "Finally, using the above definitions, I can define a function that operates an instruction
on the execution environments."

lemma "Word.word_rcat [(0x01 :: byte), 0x02] = (0x0102 :: w256)"
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
done

fun instruction_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> inst \<Rightarrow> instruction_result"
where
"instruction_sem v c (Stack (PUSH_N lst)) =
     stack_0_1_op v c (Word.word_rcat lst)"
| "instruction_sem v c (Unknown _) = instruction_failure_result v"
| "instruction_sem v c (Storage SLOAD) = stack_1_1_op v c (venv_storage v)"
| "instruction_sem v c (Storage SSTORE) = sstore v c"
| "instruction_sem v c (Pc JUMPI) = jumpi v c"
| "instruction_sem v c (Pc JUMP) = jump v c"
| "instruction_sem v c (Pc JUMPDEST) = stack_0_0_op v c"
| "instruction_sem v c (Info CALLDATASIZE) = stack_0_1_op v c (datasize v)"
| "instruction_sem v c (Stack CALLDATALOAD) = stack_1_1_op v c (cut_data v)"
| "instruction_sem v c (Info CALLER) = stack_0_1_op v c (Word.ucast (venv_caller v))"
| "instruction_sem v c (Arith ADD) = stack_2_1_op v c (\<lambda> a b. a + b)"
| "instruction_sem v c (Arith SUB) = stack_2_1_op v c (\<lambda> a b. a - b)"
| "instruction_sem v c (Arith ISZERO) = stack_1_1_op v c (\<lambda> a. if a = 0 then 1 else 0)"
| "instruction_sem v c (Misc CALL) = call v c"
| "instruction_sem v c (Misc RETURN) = ret v c"
| "instruction_sem v c (Misc STOP) = stop v c"
| "instruction_sem v c (Dup n) = general_dup n v c"
| "instruction_sem v c (Stack POP) = pop v c"
| "instruction_sem v c (Info GASLIMIT) = stack_0_1_op v c (block_gaslimit (venv_block v))"
| "instruction_sem v c (Arith inst_GT) = stack_2_1_op v c (\<lambda> a b. if a > b then 1 else 0)"
| "instruction_sem v c (Arith inst_EQ) = stack_2_1_op v c (\<lambda> a b. if a = b then 1 else 0)"
| "instruction_sem v c (Annotation a) = eval_annotation a v c"
| "instruction_sem v c (Bits inst_AND) = stack_2_1_op v c (\<lambda> a b. a AND b)"
| "instruction_sem v c (Bits inst_OR) = stack_2_1_op v c (\<lambda> a b. a OR b)"
| "instruction_sem v c (Bits inst_XOR) = stack_2_1_op v c (\<lambda> a b. a XOR b)"
| "instruction_sem v c (Bits inst_NOT) = stack_1_1_op v c (\<lambda> a. NOT a)"
| "instruction_sem v c (Bits BYTE) =
    stack_2_1_op v c (\<lambda> position w.
      if position < 32 then ucast ((word_rsplit w :: byte list) ! (unat position)) else 0)"
| "instruction_sem v c (Sarith SDIV) = stack_2_1_op v c
     (\<lambda> n divisor. if divisor = 0 then 0 else
                        word_of_int ((sint n) div (sint divisor)))"
| "instruction_sem v c (Sarith SMOD) = stack_2_1_op v c
     (\<lambda> n divisor. if divisor = 0 then 0 else
                        word_of_int ((sint n) mod (sint divisor)))"
| "instruction_sem v c (Sarith SGT) = stack_2_1_op v c
     (\<lambda> elm0 elm1. if sint elm0 > sint elm1 then 1 else 0)"
| "instruction_sem v c (Sarith SLT) = stack_2_1_op v c
     (\<lambda> elm0 elm1. if sint elm0 < sint elm1 then 1 else 0)"
| "instruction_sem v c (Sarith SIGNEXTEND) = stack_2_1_op v c
     (\<lambda> len orig.
        of_bl (List.map (\<lambda> i.
          if i \<le> 256 - 8 * ((uint len) + 1)
          then test_bit orig (nat (256 - 8 * ((uint len) + 1)))
          else test_bit orig (nat i)
        ) (List.upto 0 256))
     )"
| "instruction_sem v c (Arith MUL) = stack_2_1_op v c
     (\<lambda> a b. a * b)"
| "instruction_sem v c (Arith DIV) = stack_2_1_op v c
     (\<lambda> a divisor. (if divisor = 0 then 0 else a div divisor))"
| "instruction_sem v c (Arith MOD) = stack_2_1_op v c
     (\<lambda> a divisor. (if divisor = 0 then 0 else a mod divisor))"
| "instruction_sem v c (Arith ADDMOD) = stack_3_1_op v c
     (\<lambda> a b divisor.
         (if divisor = 0 then 0 else (a + b) mod divisor))"
| "instruction_sem v c (Arith MULMOD) = stack_3_1_op v c
     (\<lambda> a b divisor.
         (if divisor = 0 then 0 else (a * b) mod divisor))"
| "instruction_sem v c (Arith EXP) = stack_2_1_op v c
     (\<lambda> a exponent. word_of_int ((uint a) ^ (unat exponent)))"
| "instruction_sem v c (Arith inst_LT) = stack_2_1_op v c
     (\<lambda> arg0 arg1. if arg0 < arg1 then 1 else 0)"
| "instruction_sem v c (Arith SHA3) = sha3 v c"
| "instruction_sem v c (Info ADDRESS) = stack_0_1_op v c
     (ucast (cenv_this c))"
| "instruction_sem v c (Info BALANCE) = stack_1_1_op v c
      (\<lambda> addr. venv_balance v (ucast addr))"
| "instruction_sem v c (Info ORIGIN) = stack_0_1_op v c
     (ucast (venv_origin v))"
| "instruction_sem v c (Info CALLVALUE) = stack_0_1_op v c
     (venv_value_sent v)"
| "instruction_sem v c (Info CODESIZE) = stack_0_1_op v c
     (word_of_int (program_length (cenv_program c)))"
| "instruction_sem v c (Info GASPRICE) = stack_0_1_op v c
     (block_gasprice (venv_block v))"
| "instruction_sem v c (Info EXTCODESIZE) = stack_1_1_op v c
     (\<lambda> arg. (word_of_int (program_length (venv_ext_program v (ucast arg)))))"
| "instruction_sem v c (Info BLOCKHASH) = stack_1_1_op v c (block_blockhash (venv_block v))"
| "instruction_sem v c (Info COINBASE) = stack_0_1_op v c (ucast (block_coinbase (venv_block v)))"
| "instruction_sem v c (Info TIMESTAMP) = stack_0_1_op v c (block_timestamp (venv_block v))"
| "instruction_sem v c (Info NUMBER) = stack_0_1_op v c (block_number (venv_block v))"
| "instruction_sem v c (Info DIFFICULTY) = stack_0_1_op v c (block_difficulty (venv_block v))"
| "instruction_sem v c (Memory MLOAD) = mload v c"
| "instruction_sem v c (Memory MSTORE) = mstore v c"
| "instruction_sem v c (Memory MSTORE8) = mstore8 v c"
| "instruction_sem v c (Memory CALLDATACOPY) = calldatacopy v c"
| "instruction_sem v c (Memory CODECOPY) = codecopy v c"
| "instruction_sem v c (Memory EXTCODECOPY) = extcodecopy v c"
| "instruction_sem v c (Pc PC) = pc v c"
| "instruction_sem v c (Log LOG0) = log 0 v c"
| "instruction_sem v c (Log LOG1) = log 1 v c"
| "instruction_sem v c (Log LOG2) = log 2 v c"
| "instruction_sem v c (Log LOG3) = log 3 v c"
| "instruction_sem v c (Log LOG4) = log 4 v c"
| "instruction_sem v c (Swap n) = swap n v c"
| "instruction_sem v c (Misc CREATE) = create v c"
| "instruction_sem v c (Misc CALLCODE) = callcode v c"
| "instruction_sem v c (Misc SUICIDE) = suicide v c"
| "instruction_sem v c (Misc DELEGATECALL) = delegatecall v c"
| "instruction_sem v c (Info GAS) = stack_0_1_op v c (gas v)"
| "instruction_sem v c (Memory MSIZE) = stack_0_1_op v c (word_of_int (venv_memory_usage v))"

subsection {* Programs' Answer to the World *}

text "Execution of a program is harder than that of instructions.  The biggest difficulty is that
the length of the execution is arbitrary.  In Isabelle/HOL all functions must terminate, so I need
to prove the termination of program execution.  In priciple, I could have used gas, but I was
lazy to model gas at that moment, so I introduced an artificial step counter.  When I prove theorems
about smart contracts, the theorems are of the form ``for any value of the initial step counter,
this and that never happen.''"

datatype program_result =
  ProgramStepRunOut -- {* the artificial step counter has run out *}
| ProgramToWorld "contract_action * storage * (address => w256) * (variable_env \<times> int \<times> int) option"
  -- {* the program stopped execution because an instruction wants to talk to the world
  for example because the execution returned, failed, or called an account.
  *}
| ProgramInvalid -- {* An unknown instruction is found.  Maybe this should just count as
  a failing execution. *}
| ProgramAnnotationFailure -- {* An annotation turned out to be false.  This does not happen
  in reality, but this case exists for the sake of the verification. *}
| ProgramInit call_env -- {*
    This clause does not denote results of program execution.
    This denotes a state of the program that expects a particular call.
    This artificial state is used to specify that the incoming call does not overflow the balance
    of the account.  Probably there is a cleaner approach.
  *}

text "Since our program struct contains a list of annotations for each program position,
I have a function that checks all annotations at a particular program position:"  
abbreviation check_annotations :: "variable_env \<Rightarrow> constant_env \<Rightarrow> bool"
where
"check_annotations v c ==
  (let annots = program_annotation (cenv_program c) (venv_pc v) in
   List.list_all (\<lambda> annot. annot (build_aenv v c)) annots)"

   
text {* The program execution takes two counters.
One counter is decremented for each instruction.
The other counter is decremented when a backward-jump happens.
This setup allows an easy termination proof.
Also, during the proofs, I can do case analysis on the number of backwad jumps
rather than the number of instructions.
*}

function (sequential) program_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> program_result"
and blocked_program_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> program_result"
where
  "program_sem _ _ _ 0 = ProgramStepRunOut"
| "program_sem v c tiny_step (Suc remaining_steps) =
   (if tiny_step \<le> 0 then
     ProgramToWorld(ContractFail, venv_storage_at_call v, venv_balance_at_call v, None) else
   (if \<not> check_annotations v c then ProgramAnnotationFailure else
   (case venv_next_instruction v c of
      None \<Rightarrow> ProgramStepRunOut
    | Some i \<Rightarrow>
   (case instruction_sem v c i of
        InstructionContinue new_v \<Rightarrow>
          (strict_if (venv_pc new_v > venv_pc v)
             (blocked_program_sem new_v c (tiny_step - 1) (Suc remaining_steps))
             (blocked_program_sem new_v c (program_length (cenv_program c)) remaining_steps))
      | InstructionToWorld (a, st, bal, opt_pushed_v) \<Rightarrow> ProgramToWorld (a, st, bal, opt_pushed_v)
      | InstructionUnknown \<Rightarrow> ProgramInvalid
      ))))
    "
| "blocked_program_sem v c l p _ = program_sem v c l p"
by pat_completeness auto
termination by lexicographic_order

declare program_sem.psimps [simp]

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
The Yellow Paper states that an account has a storage, a piece of code and a balance.
Since I am interested in account states in the middle of a transaction, I also need to
keep track of the ongoing executions of a single account.  Also I need to keep track of
a flag indicating if the account has already marked for erasure.
*}

record account_state =
  account_address :: address
  account_storage :: storage
  account_code :: program
  account_balance :: w256
  account_ongoing_calls :: "(variable_env \<times> int \<times> int) list"
  -- {* The variable environments that are executing on this account, but waiting for calls to finish *}
  account_killed :: bool
  -- {* The boolean that indicates the account has executed SUICIDE in this transaction.
  The flag causes a destruction of the contract at the end of a transaction.
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
inductive build_venv_called :: "account_state => call_env => variable_env => bool"
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

   , venv_value_sent = callenv_value env (* the sent value is specified by the world *)

   , venv_data_sent = callenv_data env (* the sent data is specified by the world *)

   , venv_storage_at_call = account_storage a (* the snapshot of the storage is remembered in case of failure *)

   , venv_balance_at_call = bal (* the snapshot of the balance is remembered in case of failure *)

   , venv_origin = origin (* the origin of the transaction is arbitrarily chosen *)

   , venv_ext_program = ext (* the codes of the external programs are arbitrary. *)

   , venv_block = block (* the block information is chosen arbitrarily. *)
   \<rparr>
   "

declare build_venv_called.simps [simp]

text {* Similarly we can construct the constant environment.
Construction of the constant environment is much simpler than that of 
a variable environment. 
*}

abbreviation build_cenv :: "account_state \<Rightarrow> constant_env"
where
"build_cenv a \<equiv>
  \<lparr> cenv_program = account_code a,
    cenv_this = account_address a \<rparr>"
    
text "Next we turn to the case where the world returns back to the account after the account has
called an account.  In this case, the account should contain one ongoing execution that is waiting
for a call to return."

text "An instruction is ``call-like'' when it calls an account and waits for it to return."

abbreviation is_call_like :: "inst option \<Rightarrow> bool"
where
"is_call_like i \<equiv> (i = Some (Misc CALL) \<or> i = Some (Misc DELEGATECALL) 
                 \<or> i = Some (Misc CALLCODE) \<or> i = Some (Misc CREATE))"

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

inductive build_venv_returned :: "account_state \<Rightarrow> return_result \<Rightarrow> variable_env \<Rightarrow> bool"
where
venv_returned:
"  is_call_like (lookup (program_content a_code) (v_pc - 1)) \<Longrightarrow>
   new_bal \<ge> a_bal \<Longrightarrow> (* the balance might have increased *)
   build_venv_returned
     \<lparr> account_address = a_addr (* all elements are spelled out for performance *)
     , account_storage = a_storage
     , account_code = a_code
     , account_balance = a_bal
     , account_ongoing_calls =
         (\<lparr> venv_stack = v_stack
         , venv_memory = v_memory
         , venv_memory_usage = v_memory_usage
         , venv_storage = v_storage
         , venv_pc = v_pc
         , venv_balance = v_balance
         , venv_caller = v_caller
         , venv_value_sent = v_value
         , venv_data_sent = v_data
         , venv_storage_at_call = v_init_storage
         , venv_balance_at_call = v_init_balance
         , venv_origin = v_origin
         , venv_ext_program = v_ext_program
         , venv_block = v_block
         \<rparr>, mem_start, mem_size) # _
     , account_killed = _
     \<rparr>
     r
     (\<lparr>  venv_stack = 1 # v_stack (* 1 is pushed, indicating a return *)
       , venv_memory =
         put_return_values v_memory (return_data r) mem_start mem_size
       , venv_memory_usage = v_memory_usage
       , venv_storage = a_storage
       , venv_pc = v_pc
       , venv_balance = (update_balance a_addr
                            (\<lambda> _. new_bal) (return_balance r))
       , venv_caller = v_caller
       , venv_value_sent = v_value
       , venv_data_sent = v_data
       , venv_storage_at_call = v_init_storage
       , venv_balance_at_call = v_init_balance
       , venv_origin = v_origin
       , venv_ext_program = v_ext_program
       , venv_block = v_block \<rparr>)"

declare build_venv_returned.simps [simp]

text {* The situation is much simpler when an ongoing call has failed because anything 
meanwhile has no effects. *}

definition build_venv_failed :: "account_state \<Rightarrow> variable_env option"
where
"build_venv_failed a =
  (case account_ongoing_calls a of
     [] \<Rightarrow> None
   | (recovered, _, _) # _ \<Rightarrow>
      (if is_call_like (* check the previous instruction *)
        (lookup (program_content (account_code a))
         (venv_pc recovered - 1)) then
       Some (recovered
         \<lparr>venv_stack := 0 (* indicating failure *) # venv_stack recovered\<rparr>)
       else None))"

declare build_venv_failed_def [simp]

subsection {* Account State Update after EVM Execution *}

text {* Of course the other direction exists for constructing an account state after
the program executes. *}

text {* The first definition is about forgetting one ongoing call. *}

abbreviation account_state_pop_ongoing_call :: "account_state \<Rightarrow> account_state"
where
"account_state_pop_ongoing_call orig \<equiv>
   orig\<lparr> account_ongoing_calls := tl (account_ongoing_calls orig)\<rparr>"

text {* Second I define the empty account, which replaces an account that has
destroyed itself. *}
abbreviation empty_account :: "address \<Rightarrow> account_state"
where
"empty_account addr \<equiv>
 \<lparr> account_address = addr
 , account_storage = empty_storage
 , account_code = empty_program
 , account_balance = 0
 , account_ongoing_calls = []
 , account_killed = False
 \<rparr>"

text {* And after our contract makes a move, the account state is updated as follows.
*}
definition update_account_state ::
"account_state \<Rightarrow> contract_action \<Rightarrow> storage \<Rightarrow> (address \<Rightarrow> w256) \<Rightarrow> (variable_env \<times> int \<times> int) option \<Rightarrow> account_state"
where
"update_account_state prev act st bal v_opt \<equiv>
   prev \<lparr>
     account_storage := st,
     account_balance :=
       (case act of ContractFail \<Rightarrow> account_balance prev
                 |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls :=
       (case v_opt of None \<Rightarrow> account_ongoing_calls prev
                    | Some pushed \<Rightarrow> pushed # account_ongoing_calls prev),
     account_killed :=
       (case act of ContractSuicide \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev)\<rparr>"
                                     
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
     build_venv_called a call_env initial_venv \<longrightarrow>
         (* The specification says the execution should result in these *)
         c call_env = (resulting_action, final_state_pred) \<longrightarrow>
         ( \<forall> steps. (* and for any number of steps *)
           ( let r = program_sem initial_venv (build_cenv a) (program_length (account_code a)) steps in
             (* either more steps are necessary, or *)
             r = ProgramStepRunOut \<or>
             (* the result matches the specification *)
             (\<exists> pushed_venv st bal.
              r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
              final_state_pred
                (update_account_state a resulting_action st bal pushed_venv))
           )))
"

abbreviation respond_to_return_correctly ::
  "(return_result \<Rightarrow> contract_behavior) \<Rightarrow>
   account_state \<Rightarrow>
   bool"
where
"respond_to_return_correctly r a \<equiv>
   (\<forall> rr initial_venv final_state_pred resulting_action.
       build_venv_returned a rr initial_venv \<longrightarrow>
       r rr = (resulting_action, final_state_pred) \<longrightarrow>
       ( \<forall> steps.
          (let r = program_sem initial_venv (build_cenv a) (program_length (account_code a)) steps in
           r = ProgramStepRunOut \<or>
           (\<exists> pushed_venv st bal.
            r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
            final_state_pred
              (update_account_state (account_state_pop_ongoing_call a) resulting_action st bal pushed_venv))
          )))
"

abbreviation respond_to_fail_correctly ::
  "contract_behavior \<Rightarrow>
   account_state \<Rightarrow>
   bool"
where
"respond_to_fail_correctly f a \<equiv>
   (\<forall> initial_venv final_state_pred resulting_action.
      Some initial_venv = build_venv_failed a \<longrightarrow>
      f = (resulting_action, final_state_pred) \<longrightarrow>
      (\<forall> steps.
        (let r = program_sem initial_venv (build_cenv a)
                   (program_length (account_code a)) steps in
         r = ProgramStepRunOut \<or>
         (\<exists> pushed_venv st bal.
            r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
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

subsection {* Controlling the Isabelle Simplifier *}

text {* This subsection contains simplification rules for the Isabelle simplifier.
The main purpose is to prevent the AVL tree implementation to compute both the
left insertion and the right insertion when actually only one of these happens.
*}

declare word_rcat_def [simp]
        unat_def [simp]
        bin_rcat_def [simp]
        
text {* I do not allow the AVL library to perform updates at arbitrary moments,
because that causes exponentially expensive computation (as measured with
the number of elements *) *}
declare update.simps [simp del]
declare lookup.simps [simp del]

text {* Instead, I only allow the following operations to happen (from left to right). *}

lemma updateL [simp] : "update x y Leaf = Node 1 Leaf (x,y) Leaf"
apply(simp add: update.simps)
done

lemma updateN_EQ [simp]: "cmp x a = EQ \<Longrightarrow> update x y (Node h l (a, b) r) = Node h l (x, y) r"
apply(simp add: update.simps)
done

lemma updateN_GT [simp]: "cmp x a = GT \<Longrightarrow> update x y (Node h l (a, b) r) = balR l (a, b) (update x y r)"
apply(simp add: update.simps)
done

lemma updateN_LT [simp]: "cmp x a = LT \<Longrightarrow> update x y (Node h l (a, b) r) = balL (update x y l) (a, b) r"
apply(simp add: update.simps)
done

lemma lookupN_EQ [simp]: "cmp x a = EQ \<Longrightarrow> lookup (Node h l (a, b) r) x = Some b"
apply(simp add: lookup.simps)
done

lemma lookupN_GT [simp]: "cmp x a = GT \<Longrightarrow> lookup (Node h l (a, b) r) x = lookup r x"
apply(simp add: lookup.simps)
done

lemma lookupN_LT [simp]: "cmp x a = LT \<Longrightarrow> lookup (Node h l (a, b) r) x = lookup l x"
apply(simp add: lookup.simps)
done

lemma lookupL [simp]: "lookup Leaf x = None"
apply(simp add: lookup.simps)
done

lemma nodeLL [simp] : "node Leaf a Leaf == Node 1 Leaf a Leaf"
apply(simp add:node_def)
done

lemma nodeLN [simp] : "node Leaf a (Node rsize rl rv rr) == Node (rsize + 1) Leaf a (Node rsize rl rv rr)"
apply(simp add:node_def)
done

lemma nodeNL [simp] : "node \<langle>lsize, ll, lv, lr\<rangle> a \<langle>\<rangle> == Node (lsize + 1) (Node lsize ll lv lr) a Leaf"
apply(simp add: node_def)
done

lemma nodeNN [simp] : "node (Node lsize ll lv lr) a (Node rsize rl rv rr) == Node (max lsize rsize + 1) (Node lsize ll lv lr) a (Node rsize rl rv rr)"
apply(simp add: node_def)
done

lemma balL_neq_NL [simp]:
  "lh \<noteq> Suc (Suc 0) \<Longrightarrow>
   balL (Node lh ll b lr) a Leaf = node (Node lh ll b lr) a Leaf"
apply(simp add: balL_def)
done

lemma balL_neq_Lr [simp]:
  "balL Leaf a r = node Leaf a r"
apply(simp add: balL_def)
done

lemma balL_neq_NN [simp]:
  "lh \<noteq> Suc (Suc rh) \<Longrightarrow>
   balL (Node lh ll lx lr) a (Node rh rl rx rr) = node (Node lh ll lx lr) a (Node rh rl rx rr)"
apply(simp add: balL_def)
done

lemma balL_eq_heavy_r_rL [simp]:
  "ht bl < ch \<Longrightarrow>
   balL (Node (Suc (Suc 0)) bl b (Node ch cl c cr)) a Leaf = node (node bl b cl) c (node cr a Leaf)
   "
apply(simp add: balL_def)
done

lemma balL_eq_heavy_r_rN [simp]:
  "hl = Suc (Suc rh) \<Longrightarrow>
   ht bl < ch \<Longrightarrow>
   balL (Node hl bl b (Node ch cl c cr)) a (Node rh rl rx rr) = node (node bl b cl) c (node cr a (Node rh rl rx rr))
   "
apply(simp add: balL_def)
done

lemma balL_eq_heavy_l [simp]:
  "hl = ht r + 2 \<Longrightarrow>
   ht bl \<ge> ht br \<Longrightarrow>
   balL (Node hl bl b br) a r = node bl b (node br a r)"
apply(simp add: balL_def)
done

lemma balR_neq_xL [simp]:
  "balR l a Leaf = node l a Leaf"
apply(simp add: balR_def)
done

lemma balR_neq_LN [simp]:
  "rh \<noteq> Suc (Suc 0) \<Longrightarrow>
   balR Leaf a (Node rh rl rx rr) = node Leaf a (Node rh rl rx rr)"
apply(simp add: balR_def)
done

lemma balR_neq_NN [simp]:
  "rh \<noteq> Suc (Suc lh) \<Longrightarrow>
   balR (Node lh ll lx lr) a (Node rh rl rx rr) = node (Node lh ll lx lr) a (Node rh rl rx rr)"
apply(simp add: balR_def)
done

lemma balR_eq_heavy_l [simp]:
  "bh = ht l + 2 \<Longrightarrow>
   ch > ht br \<Longrightarrow>
   balR l a (Node bh (Node ch cl c cr) b br) =
   node (node l a cl) c (node cr b br)"
apply(simp add: balR_def)
done

lemma balR_eq_heavy_r [simp]:
  "bh = ht l + 2 \<Longrightarrow>
   ht bl \<le> ht br \<Longrightarrow>
   balR l a (Node bh bl b br) = node (node l a bl) b br"
apply(simp add: balR_def)
done


text {* There is a common pattern for checking a predicate. *}

lemma iszero_iszero [simp] :
"((if b then (1 :: 256 word) else 0) = 0) = (\<not> b) "
apply(auto)
done

end
