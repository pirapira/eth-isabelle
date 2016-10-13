text "This is a port of ContractSem.v in pirapira/evmverif"

text "The main difficulty is to avoid the use of coinduction"

text "One way is, in the specification, talk about some concrete state."
text "Maybe that's fine."

theory ContractSem

imports Main "~~/src/HOL/Word/Word" "./ContractEnv" "./Instructions" "./KEC"

begin

definition bool_to_uint :: "bool \<Rightarrow> uint"
where
"bool_to_uint b = (if b then 1 else 0)"

abbreviation "drop_one_element == tl"

record call_arguments =
  callarg_gaslimit :: uint
  callarg_code :: address
  callarg_recipient :: address
  callarg_value :: uint
  callarg_data :: "byte list"
  callarg_output_begin :: uint
  callarg_output_size :: uint

record create_arguments =
  createarg_value :: uint
  createarg_code :: "byte list"

record return_result =
  return_data :: "byte list"
  return_balance :: "address \<Rightarrow> uint"

record call_env =
  callenv_gaslimit :: uint
  callenv_value :: uint
  callenv_data :: "byte list"
  callenv_caller :: address
  callenv_timestamp :: uint
  callenv_blocknum :: uint
  callenv_balane :: "address \<Rightarrow> uint"

datatype contract_action =
  ContractCall call_arguments
| ContractCreate create_arguments
| ContractFail
| ContractSuicide
| ContractReturn "byte list"

text "response_to_world is not ported"
text "We will be checking the resulting state"

datatype world_action =
  WorldCall call_env
| WorldRet return_result
| WorldFail

type_synonym world = "world_action list"

datatype action =
  ActionByWorld world_action
| ActionByContract contract_action

type_synonym history = "action list"

type_synonym program = "inst list"

fun drop_bytes :: "program \<Rightarrow> nat \<Rightarrow> program"
where
  "drop_bytes prg 0 = prg"
| "drop_bytes (Stack (PUSH_N v) # rest) bytes = drop_bytes rest (bytes - 1 - length v)"
| "drop_bytes (Annotation _ # rest) bytes = drop_bytes rest bytes"
| "drop_bytes (_ # rest) bytes = drop_bytes rest (bytes - 1)"
| "drop_bytes [] (Suc v) = []"

declare drop_bytes.simps [simp]

fun program_size :: "program \<Rightarrow> nat"
where
  "program_size (Stack (PUSH_N v) # rest) = length v + 1 + program_size rest"
| "program_size (Annotation _ # rest) = program_size rest"
| "program_size (_ # rest) = 1 + program_size rest"
| "program_size [] = 0"

definition empty_memory :: memory
where
"empty_memory _ = 0"

record block_info =
  block_blockhash :: "uint \<Rightarrow> uint" (* This captures the whole BLOCKHASH operation *)
  block_coinbase :: address
  block_timestamp :: uint
  block_number :: uint
  block_difficulty :: uint


record variable_env =
  venv_stack :: "uint list"
  venv_memory :: memory
  venv_memory_usage :: int
  venv_storage :: storage
  venv_prg_sfx :: program
  venv_balance :: "address \<Rightarrow> uint"
  venv_caller :: address
  venv_value_sent :: uint
  venv_data_sent :: "byte list"
  venv_storage_at_call :: storage
  venv_balance_at_call :: "address \<Rightarrow> uint"
  venv_origin :: address
  venv_gasprice :: uint
  venv_ext_program :: "address \<Rightarrow> program"
  venv_block :: block_info


record constant_env =
  cenv_program :: program
  cenv_this :: address

(* TODO: keep track of the gas consumption in variable_env.  This is issue #7 *)
definition gas_limit :: "variable_env \<Rightarrow> uint"
where "gas_limit = undefined"

(* This M function is defined at the end of H.1. in the yellow paper.
 * The purpose of this is to update the memory usage.
 *)
abbreviation M :: "int \<Rightarrow> uint \<Rightarrow> uint \<Rightarrow> int"
where
"M s f l ==

  (if l = 0 then s else
     max s ((uint f + uint l + 31) div 32))
"

definition update_balance :: "address \<Rightarrow> (uint \<Rightarrow> uint) \<Rightarrow> (address \<Rightarrow> uint) \<Rightarrow> (address \<Rightarrow> uint)"
where
"update_balance a newbal orig = orig(a := newbal (orig a))"

datatype instruction_result =
  InstructionUnknown
| InstructionContinue variable_env
| InstructionAnnotationFailure
| InstructionToWorld "contract_action * storage * (address \<Rightarrow> uint) * variable_env option"

abbreviation instruction_result_continuing :: "instruction_result => bool"
where
"instruction_result_continuing r ==
  (case r of
     InstructionContinue _ => True
   | _ => False)"

abbreviation instruction_failure_result :: "variable_env \<Rightarrow> instruction_result"
where
"instruction_failure_result v == InstructionToWorld (ContractFail, venv_storage_at_call v, venv_balance_at_call v, None)"

abbreviation instruction_return_result :: "byte list \<Rightarrow> variable_env \<Rightarrow> instruction_result"
where
"instruction_return_result x v == InstructionToWorld (ContractReturn x, venv_storage v, venv_balance v, None)"

(* venv_update_x functions are not useful in Isabelle/HOL,
 * where field updates are supported already. *)

fun venv_pop_stack :: "nat \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
  "venv_pop_stack 0 v = v"
| "venv_pop_stack (Suc n) v =
   venv_pop_stack n v\<lparr> venv_stack := tl (venv_stack v) \<rparr>"

abbreviation venv_stack_top :: "variable_env \<Rightarrow> uint option"
where
"venv_stack_top v ==
  (case venv_stack v of
     h # _\<Rightarrow> Some h
   | [] \<Rightarrow> None)"

abbreviation venv_change_sfx :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> variable_env"
where
"venv_change_sfx pos v c ==
   v\<lparr>
     venv_prg_sfx := drop_bytes (cenv_program c) pos
   \<rparr>"

(* function_update is already provided in Main library *)

abbreviation venv_update_storage :: "uint \<Rightarrow> uint \<Rightarrow> variable_env \<Rightarrow> variable_env"
where
"venv_update_storage idx val v ==
  v\<lparr>venv_storage := (venv_storage v)(idx := val)\<rparr>"

abbreviation venv_first_instruction :: "variable_env \<Rightarrow> inst option"
where
"venv_first_instruction v ==
   (case venv_prg_sfx v of
      [] \<Rightarrow> None
    | h # _ \<Rightarrow> Some h)"

abbreviation venv_advance_pc :: "variable_env \<Rightarrow> variable_env"
where
"venv_advance_pc v \<equiv> v\<lparr> venv_prg_sfx := drop_one_element (venv_prg_sfx v)\<rparr>"

    
abbreviation stack_0_0_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stack_0_0_op v c == InstructionContinue (venv_advance_pc v)"

abbreviation stack_0_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> uint \<Rightarrow> instruction_result"
where
"stack_0_1_op v c w ==
   InstructionContinue
      (venv_advance_pc v\<lparr>venv_stack := w # venv_stack v\<rparr>)"

abbreviation stack_1_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint) \<Rightarrow> instruction_result"
where
"stack_1_1_op v c f \<equiv>
   (case venv_stack v of
      [] \<Rightarrow> instruction_failure_result v
      | h # t \<Rightarrow>
         InstructionContinue
           (venv_advance_pc v\<lparr>venv_stack := f h # t\<rparr>)
      )"

abbreviation stack_1_2_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint * uint) \<Rightarrow> instruction_result"
where
"stack_1_2_op v c f ==
  (case venv_stack v of
     [] \<Rightarrow> instruction_failure_result v
   | h # t \<Rightarrow>
     (case f h of
        (new0, new1) \<Rightarrow>
          InstructionContinue
            (venv_advance_pc v\<lparr>venv_stack := new0 # new1 # venv_stack v\<rparr>)))"

abbreviation stack_2_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint \<Rightarrow> uint) \<Rightarrow> instruction_result"
where
"stack_2_1_op v c f \<equiv>
  (case venv_stack v of
     operand0 # operand1 # rest \<Rightarrow>
       InstructionContinue
         (venv_advance_pc
            v\<lparr>venv_stack := f operand0 operand1 # rest\<rparr>)
  | _ \<Rightarrow> instruction_failure_result v
  )"
  
abbreviation stack_3_1_op :: "variable_env \<Rightarrow> constant_env \<Rightarrow> (uint \<Rightarrow> uint \<Rightarrow> uint \<Rightarrow> uint) \<Rightarrow>
  instruction_result"
where
"stack_3_1_op v c f ==
  (case venv_stack v of
     operand0 # operand1 # operand2 # rest \<Rightarrow>
       InstructionContinue
         (venv_advance_pc
            v\<lparr>venv_stack := f operand0 operand1 operand2 # rest\<rparr>)
   | _ \<Rightarrow> instruction_failure_result v
   )"

abbreviation sload :: "variable_env \<Rightarrow> uint \<Rightarrow> uint"
where
"sload v idx == venv_storage v idx"

abbreviation sstore :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sstore v c ==
  (case venv_stack v of
    addr # val # stack_tail \<Rightarrow>
      InstructionContinue
      (venv_advance_pc
        (venv_update_storage addr val v\<lparr>venv_stack := stack_tail\<rparr>))
    | _ \<Rightarrow> instruction_failure_result v)"

abbreviation build_aenv :: "variable_env \<Rightarrow> constant_env \<Rightarrow> aenv"
where
"build_aenv v c ==
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

definition eval_annotation :: "annotation \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"eval_annotation anno v c =
   (if anno (build_aenv v c) then InstructionContinue (venv_advance_pc v)
    else InstructionAnnotationFailure)"

abbreviation jump :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jump v c \<equiv>
  (case venv_stack_top v of
     None \<Rightarrow> instruction_failure_result v
   | Some pos \<Rightarrow>
     (let v_new = venv_change_sfx (Word.unat pos) (venv_pop_stack 1 v) c in
     (case venv_first_instruction v_new of
        Some (Pc JUMPDEST) \<Rightarrow>
          InstructionContinue v_new
      | Some _ \<Rightarrow> instruction_failure_result v
      | None \<Rightarrow> instruction_failure_result v )))"
      
abbreviation jumpi :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"jumpi v c ==
  (case venv_stack v of
      pos # cond # rest \<Rightarrow>
        (if cond = 0 then
           InstructionContinue
             (venv_advance_pc (venv_pop_stack 2 v))
         else
           jump (v\<lparr> venv_stack := pos # rest \<rparr>) c)
    | _ \<Rightarrow> instruction_failure_result v)"

abbreviation datasize :: "variable_env \<Rightarrow> uint"
where
"datasize v == Word.word_of_int (int (length (venv_data_sent v)))"

abbreviation read_word_from_bytes :: "nat \<Rightarrow> byte list \<Rightarrow> uint"
where
"read_word_from_bytes idx lst ==
   Word.word_rcat (take 32 (drop idx lst))"

abbreviation cut_data :: "variable_env \<Rightarrow> uint \<Rightarrow> uint"
where
"cut_data v idx ==
    read_word_from_bytes (Word.unat idx) (venv_data_sent v)"

fun cut_memory :: "uint \<Rightarrow> nat \<Rightarrow> (uint \<Rightarrow> byte) \<Rightarrow> byte list"
where
"cut_memory idx 0 memory = []" |
"cut_memory idx (Suc n) memory =
  memory idx # cut_memory (idx + 1) n memory"

definition call :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"call v c =
  (case venv_stack v of
    e0 # e1 # e2 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
    (if venv_balance v (cenv_this c) < e2 then
       instruction_failure_result v
     else
       InstructionToWorld
         (ContractCall
           (\<lparr> callarg_gaslimit = e0,
              callarg_code = Word.ucast e1,
              callarg_recipient = Word.ucast e1,
              callarg_value = e2,
              callarg_data = cut_memory e3 (Word.unat e4) (venv_memory v),
              callarg_output_begin = e5,
              callarg_output_size = e6 \<rparr>),
          venv_storage v, update_balance (cenv_this c) (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v),
          Some
            (v\<lparr> venv_stack := rest,
                venv_prg_sfx := drop_one_element (venv_prg_sfx v),
                venv_balance := update_balance (cenv_this c) (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v)
              , venv_memory_usage := M (M (venv_memory_usage v) e3 e4) e5 e6 \<rparr>
              )))
  | _ \<Rightarrow> instruction_failure_result v
  )"

declare call_def [simp]

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
           (\<lparr> callarg_gaslimit = e0,
              callarg_code = Word.ucast e1,
              callarg_recipient = Word.ucast e1,
              callarg_value = venv_value_sent v,
              callarg_data = cut_memory e3 (Word.unat e4) (venv_memory v),
              callarg_output_begin = e5,
              callarg_output_size = e6 \<rparr>),
          venv_storage v, venv_balance v,
          Some
            (v\<lparr> venv_stack := rest
              , venv_prg_sfx := drop_one_element (venv_prg_sfx v)
              , venv_memory_usage := M (M (venv_memory_usage v) e3 e4) e5 e6 \<rparr>
              )))
  | _ \<Rightarrow> instruction_failure_result v
  )"

declare delegatecall_def [simp]

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
           (\<lparr> callarg_gaslimit = e0,
              callarg_code = ucast e1,
              callarg_recipient = cenv_this c,
              callarg_value = e2,
              callarg_data = cut_memory e3 (unat e4) (venv_memory v),
              callarg_output_begin = e5,
              callarg_output_size = e6 \<rparr>),
          venv_storage v, update_balance (cenv_this c) (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v),
          Some
            (v\<lparr> venv_stack := rest
              , venv_prg_sfx := drop_one_element (venv_prg_sfx v)
              , venv_memory_usage := M (M (venv_memory_usage v) e3 e4) e5 e6
              , venv_balance := update_balance (cenv_this c) (\<lambda> orig \<Rightarrow> orig - e2) (venv_balance v) \<rparr>
             )))
  | _ \<Rightarrow> instruction_failure_result v
  )"


abbreviation create :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"create v c \<equiv>
  (case venv_stack v of
    val # code_start # code_len # rest \<Rightarrow>
      (if venv_balance v (cenv_this c) < val then
         instruction_failure_result v
       else
         let code = cut_memory code_start (unat code_len) (venv_memory v) in
         let new_balance = update_balance (cenv_this c) (\<lambda> orig. orig - val) (venv_balance v) in
         InstructionToWorld
           (ContractCreate
             (\<lparr> createarg_value = val
              , createarg_code = code \<rparr>),
            venv_storage v, update_balance (cenv_this c) (\<lambda> orig. orig - val) (venv_balance v),
            Some
              (v\<lparr> venv_stack := rest
                , venv_prg_sfx := drop_one_element (venv_prg_sfx v)
                , venv_balance := update_balance (cenv_this c) (\<lambda> orig. orig - val) (venv_balance v)
                , venv_memory_usage := M (venv_memory_usage v) code_start code_len \<rparr>
              )))
  | _ \<Rightarrow> instruction_failure_result v)"

definition
"venv_returned_bytes v =
  (case venv_stack v of
    e0 # e1 # _ \<Rightarrow> cut_memory e0 (Word.unat e1) (venv_memory v)
  | _ \<Rightarrow> []
)"

abbreviation ret :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"ret v c \<equiv>
   (case venv_stack v of
      e0 # e1 # rest \<Rightarrow>
        let new_v = v\<lparr> venv_memory_usage := M (venv_memory_usage v) e0 e1 \<rparr> in
        InstructionToWorld ((ContractReturn (venv_returned_bytes new_v)),
                           venv_storage v, venv_balance v, None)
   | _ \<Rightarrow> instruction_failure_result v)"

abbreviation stop :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"stop v c \<equiv> InstructionToWorld (ContractReturn [], venv_storage v, venv_balance v, None)"

abbreviation pop :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"pop v c \<equiv> InstructionContinue (venv_advance_pc
             v\<lparr>venv_stack := tl (venv_stack v)\<rparr>)"
             
abbreviation general_dup :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"general_dup n v c ==
   (if n > length (venv_stack v) then instruction_failure_result v else
   (let duplicated = venv_stack v ! (n - 1) in
    InstructionContinue (venv_advance_pc v\<lparr> venv_stack := duplicated # venv_stack v \<rparr>)))
"

fun store_byte_list_memory :: "uint \<Rightarrow> byte list \<Rightarrow> memory \<Rightarrow> memory"
where
  "store_byte_list_memory _ [] orig = orig"
| "store_byte_list_memory pos (h # t) orig =
     store_byte_list_memory (pos + 1) t (orig(pos := h))"

declare store_byte_list_memory.simps [simp]

abbreviation store_word_memory :: "uint \<Rightarrow> uint \<Rightarrow> memory \<Rightarrow> memory"
where
"store_word_memory pos val mem ==
   store_byte_list_memory pos (word_rsplit val) mem"

abbreviation mstore :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"mstore v c ==
   (case venv_stack v of
     [] \<Rightarrow> instruction_failure_result v
   | [_] \<Rightarrow> instruction_failure_result v
   | pos # val # rest \<Rightarrow>
       let new_memory = store_word_memory pos val (venv_memory v) in
       InstructionContinue (venv_advance_pc
         v\<lparr> venv_stack := rest
          , venv_memory := new_memory
          , venv_memory_usage := M (venv_memory_usage v) pos 32
          \<rparr>, 0)
   )
"

abbreviation mload :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"mload v c ==
  (case venv_stack v of
    pos # rest \<Rightarrow>
      let value = word_rcat (cut_memory pos 32 (venv_memory v)) in
      InstructionContinue (venv_advance_pc
        v \<lparr> venv_stack := value # rest
          , venv_memory_usage := M (venv_memory_usage v) pos 32
          \<rparr>)
  | _ \<Rightarrow> instruction_failure_result v)"

abbreviation mstore8 :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"mstore8 v c ==
  (case venv_stack v of
     pos # val # rest \<Rightarrow>
        let new_memory = (venv_memory v)(pos := ucast val) in
        InstructionContinue (venv_advance_pc
          v\<lparr> venv_stack := rest
           , venv_memory_usage := M (venv_memory_usage v) pos 8
           , venv_memory := new_memory \<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)
           "

abbreviation input_as_memory :: "byte list \<Rightarrow> memory"
where
"input_as_memory lst idx ==
   (if length lst \<le> unat idx then 0 else
    lst ! unat idx)"

abbreviation calldatacopy :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"calldatacopy v c ==
  (case venv_stack v of
     (dst_start :: uint) # src_start # len # rest \<Rightarrow>
       let data = cut_memory src_start (unat len) (input_as_memory (venv_data_sent v)) in
       let new_memory = store_byte_list_memory dst_start data (venv_memory v) in
       InstructionContinue (venv_advance_pc
         v\<lparr> venv_stack := rest, venv_memory := new_memory,
            venv_memory_usage := M (venv_memory_usage v) dst_start len
         \<rparr>))"

abbreviation codecopy :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"codecopy v c ==
  (case venv_stack v of
     dst_start # src_start # len # rest \<Rightarrow>
     let data = cut_memory src_start (unat len)
                  (input_as_memory
                    (program_code (cenv_program c))) in
     let new_memory = store_byte_list_memory dst_start data (venv_memory v) in
     InstructionContinue (venv_advance_pc
       v\<lparr> venv_stack := rest, venv_memory := new_memory
       , venv_memory_usage := M (venv_memory_usage v) dst_start len
       \<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)"

abbreviation extcodecopy :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"extcodecopy v c ==
  (case venv_stack v of
     addr # dst_start # src_start # len # rest \<Rightarrow>
     let data = cut_memory src_start (unat len)
                  (input_as_memory
                    (program_code (venv_ext_program v (ucast addr)))) in
     let new_memory = store_byte_list_memory dst_start data (venv_memory v) in
     InstructionContinue (venv_advance_pc
       v\<lparr> venv_stack := rest, venv_memory := new_memory,
       venv_memory_usage := M (venv_memory_usage v) dst_start len
       \<rparr>)
   | _ \<Rightarrow> instruction_failure_result v)"

abbreviation pc :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"pc v c ==
  (let pc = program_size (cenv_program c) - program_size (venv_prg_sfx v) in
   InstructionContinue (venv_advance_pc
     v\<lparr> venv_stack := word_of_int (int pc) # venv_stack v \<rparr>))"

abbreviation log :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"log n v c ==
   InstructionContinue (venv_advance_pc
     (venv_pop_stack (n + 2) v))"

value "[0, 1]"

abbreviation list_swap :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list option"
where
"list_swap n lst \<equiv>
  if length lst < n + 1 then None else
  Some (concat [[lst ! n], take (n - 1) (drop 1 lst) , [lst ! 0], drop (1 + n) lst])"

value "list_swap 1 [0, 1]"
value "list_swap 2 [0, 1]"
value "list_swap 2 [0, 1, 2]"
value "list_swap 3 [0, 1, 2, 3]"
value "list_swap 1 [0, 1, 2, 3]"

abbreviation swap :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"swap n v c ==
   (case list_swap n (venv_stack v) of
      None \<Rightarrow> instruction_failure_result v
    | Some new_stack \<Rightarrow>
      InstructionContinue (venv_advance_pc v\<lparr> venv_stack := new_stack \<rparr>, 0))"

abbreviation sha3 :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"sha3 v c ==
  (case venv_stack v of
    start # len # rest \<Rightarrow>
      InstructionContinue (
        venv_advance_pc v\<lparr> venv_stack := keccack
                                         (cut_memory start (unat len) (venv_memory v))
                                        # rest
                        , venv_memory_usage := M (venv_memory_usage v) start len
                        \<rparr>)
  | _ \<Rightarrow> instruction_failure_result v
  )"

abbreviation suicide :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where
"suicide v c ==
  (case venv_stack v of 
     dst # _ \<Rightarrow>
       let new_balance = (venv_balance v)(cenv_this c := 0, ucast dst := venv_balance v (cenv_this c)) in
       InstructionToWorld (ContractSuicide,venv_storage v, new_balance, None)
    | _ \<Rightarrow> instruction_failure_result v)"


fun instruction_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> inst \<Rightarrow> instruction_result"
where
"instruction_sem v c (Stack (PUSH_N lst)) =
     stack_0_1_op v c (Word.word_rcat lst)"
| "instruction_sem v c (Unknown _) = InstructionUnknown"
| "instruction_sem v c (Storage SLOAD) = stack_1_1_op v c (sload v)"
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
| "instruction_sem v c (Info GASLIMIT) = stack_0_1_op v c (gas_limit v)"
| "instruction_sem v c (Arith GT) = stack_2_1_op v c (\<lambda> a b. if a > b then 1 else 0)"
| "instruction_sem v c (Arith EQ) = stack_2_1_op v c (\<lambda> a b. if a = b then 1 else 0)"
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
| "instruction_sem v c (Arith LT) = stack_2_1_op v c
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
     (word_of_int (int (program_size (cenv_program c))))"
| "instruction_sem v c (Info GASPRICE) = stack_0_1_op v c
     (venv_gasprice v)"
| "instruction_sem v c (Info EXTCODESIZE) = stack_1_1_op v c
     (\<lambda> arg. (word_of_int (int (program_size (venv_ext_program v (ucast arg))))))"
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
| "instruction_sem v c (Info GAS) = stack_0_1_op v c (gas_limit v)"
| "instruction_sem v c (Memory MSIZE) = stack_0_1_op v c (word_of_int (venv_memory_usage v))"

datatype program_result =
  ProgramStepRunOut
| ProgramToWorld "contract_action * storage * (address => uint) * variable_env option"
| ProgramInvalid
| ProgramAnnotationFailure

definition decrease :: "((variable_env * constant_env * nat) * (variable_env * constant_env * nat)) set"
where
"decrease =
  Collect (\<lambda> x.
     (let ((av, _, an), (bv, _, bn)) = x in
      an < bn \<or> (an = bn \<and> length (venv_prg_sfx av) < length (venv_prg_sfx bv))))
"

fun program_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> program_result"
where
  "program_sem _ _ _ 0 = ProgramStepRunOut"
| "program_sem v c prg (Suc remaining_steps) =
    (case prg of
      [] \<Rightarrow> ProgramStepRunOut
    | i # rest \<Rightarrow>
      (case instruction_sem v c i of
        InstructionContinue new_v \<Rightarrow>
          (if venv_prg_sfx new_v = rest then
             program_sem new_v c rest (Suc remaining_steps)
           else
             program_sem new_v c (venv_prg_sfx new_v) remaining_steps)
      | InstructionToWorld (a, st, bal, opt_pushed_v) \<Rightarrow>
        ProgramToWorld (a, st, bal, opt_pushed_v)
      | InstructionUnknown \<Rightarrow> ProgramInvalid
      | InstructionAnnotationFailure \<Rightarrow> ProgramAnnotationFailure
      )
    )"

declare program_sem.simps [simp]

record account_state =
  account_address :: address
  account_storage :: storage
  account_code :: "inst list"
  account_balance :: uint (* TODO: model the fact that this can be
                             increased at any moment *)
  account_ongoing_calls :: "variable_env list"

(* account_state_update_storage is not particularly useful in
 * Isabelle/HOL where fields of records can be updated. *)
 
(* Currently it's shown as if the variable_env is determinined by
 * the other arguments but in reality the balance might increase.
 * This mistake will be kept until we try the managed_account_with_accumulated_income_and_spending
 * and we compare Coq and Isabelle/HOL on the same target.
 *)

inductive build_venv_called :: "account_state => call_env => variable_env => bool"
where
venv_called:
  "venv_stack venv = [] \<Longrightarrow>
   venv_memory venv = empty_memory \<Longrightarrow>
   venv_prg_sfx venv = account_code a \<Longrightarrow>
   venv_storage venv = account_storage a \<Longrightarrow>
   venv_balance venv \<ge>
     update_balance (account_address a)
       (\<lambda> _. account_balance a + callenv_value env)
       (callenv_balance env) \<Longrightarrow>
   venv_caller venv = callenv_caller env \<Longrightarrow>
   venv_value_sent venv = callenv_value env \<Longrightarrow>
   venv_storage_at_call venv = account_storage a \<Longrightarrow>
   venv_balance_at_call venv = venv_balance venv \<Longrightarrow>
   build_venv_called a env venv"
   
declare build_venv_called.simps [simp]
   
abbreviation build_cenv :: "account_state \<Rightarrow> constant_env"
where
"build_cenv a \<equiv>
  \<lparr> cenv_program = account_code a,
           cenv_this = account_address a \<rparr>"

inductive build_venv_returned :: "account_state \<Rightarrow> return_result \<Rightarrow> variable_env \<Rightarrow> bool"
where
venv_returned:
"  account_ongoing_calls a = recovered # _ \<Longrightarrow>
   new_bal \<ge> account_balance a \<Longrightarrow>
   build_venv_returned a r
     (
              recovered \<lparr>
                venv_stack := 1 # venv_stack recovered
              , venv_storage := account_storage a
              , venv_balance := (update_balance (account_address a)
                                   (\<lambda> _. new_bal) (return_balance r))
            \<rparr>)"

declare build_venv_returned.simps [simp]

definition build_venv_fail :: "account_state \<Rightarrow> variable_env option"
where
"build_venv_fail a =
  (case account_ongoing_calls a of
     [] \<Rightarrow> None
   | recovered # _ \<Rightarrow>
      Some (recovered \<lparr>venv_stack := 0 # venv_stack recovered\<rparr>)
  )"

declare build_venv_fail_def [simp]


abbreviation account_state_pop_ongoing_call :: "account_state \<Rightarrow> account_state"
where
"account_state_pop_ongoing_call orig ==
   orig\<lparr> account_ongoing_calls := tl (account_ongoing_calls orig)\<rparr>"
 
abbreviation update_account_state :: "account_state \<Rightarrow> contract_action \<Rightarrow> storage \<Rightarrow> (address \<Rightarrow> uint) \<Rightarrow> variable_env option \<Rightarrow> account_state"
where
"update_account_state prev act st bal v_opt \<equiv>
  (case v_opt of
    None \<Rightarrow>
      prev\<lparr>
        account_storage := st \<rparr>
  | Some pushed \<Rightarrow>
      prev\<lparr>
        account_storage := st,
        account_balance := bal (account_address prev),
        account_ongoing_calls := pushed # (account_ongoing_calls prev)
      \<rparr>
  )
"

(* Replace the coinductional future of the 
 * contract_behavior with just a condition on
 * the resulting account_state *)

type_synonym contract_behavior = "contract_action * (account_state \<Rightarrow> bool)"

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
           ( let r = program_sem initial_venv (build_cenv a) (venv_prg_sfx initial_venv) steps in
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
          (let r = program_sem initial_venv (build_cenv a) (venv_prg_sfx initial_venv) steps in
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
      Some initial_venv = build_venv_fail a \<longrightarrow>
      f = (resulting_action, final_state_pred) \<longrightarrow>
      ( \<forall> steps.
        ( let r = program_sem initial_venv (build_cenv a) (venv_prg_sfx initial_venv) steps in
          r = ProgramStepRunOut \<or>
          (\<exists> pushed_venv st bal.
             r = ProgramToWorld (resulting_action, st, bal, pushed_venv) \<and>
             final_state_pred (update_account_state (account_state_pop_ongoing_call a) resulting_action st bal pushed_venv)))))"


inductive account_state_responds_to_world ::
  "(account_state \<Rightarrow> bool) \<Rightarrow> response_to_world \<Rightarrow> bool"
where
AccountStep:
  "(\<forall> a. precond a \<longrightarrow> respond_to_call_correctly c a) \<Longrightarrow>
   (\<forall> a. precond a \<longrightarrow> respond_to_return_correctly r a) \<Longrightarrow>
   (\<forall> a. precond a \<longrightarrow> respond_to_fail_correctly f a) \<Longrightarrow>
   account_state_responds_to_world precond
   \<lparr> when_called = c, when_returned = r, when_failed = f \<rparr>"

declare word_rcat_def [simp]
        unat_def [simp]
        bin_rcat_def [simp]

end
