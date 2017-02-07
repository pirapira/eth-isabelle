theory "InstructionAux" 

imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl"
  "../lem/Evm"
begin


fun get_bits :: "inst option \<Rightarrow> bits_inst" where
  "get_bits (Some (Bits i)) = i"

fun get_sarith :: "inst option \<Rightarrow> sarith_inst" where
  "get_sarith (Some (Sarith i)) = i"

fun get_arith :: "inst option \<Rightarrow> arith_inst" where
  "get_arith (Some (Arith i)) = i"


fun get_info :: "inst option \<Rightarrow> info_inst" where
  "get_info (Some (Info i)) = i"

fun get_memory :: "inst option \<Rightarrow> memory_inst" where
  "get_memory (Some (Memory i)) = i"

fun get_storage :: "inst option \<Rightarrow> storage_inst" where
  "get_storage (Some (Storage i)) = i"

fun get_misc :: "inst option \<Rightarrow> misc_inst" where
  "get_misc (Some (Misc i)) = i"

fun get_log :: "inst option \<Rightarrow> log_inst" where
  "get_log (Some (Log i)) = i"

fun get_pc :: "inst option \<Rightarrow> pc_inst" where
  "get_pc (Some (Pc i)) = i"

fun get_dup :: "inst option \<Rightarrow> 4 word" where
  "get_dup (Some (Dup i)) = i"

fun get_swap :: "inst option \<Rightarrow> 4 word" where
  "get_swap (Some (Swap i)) = i"

fun get_stack :: "inst \<Rightarrow> stack_inst" where
  "get_stack (Stack i) = i"


fun get_some :: "'a option \<Rightarrow> 'a" where
"get_some (Some a) = a"

definition instruction_aux  :: " variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> inst \<Rightarrow> instruction_result "  where 
     " instruction_aux v c inst = (
  ((case  inst of
    Stack (PUSH_N lst) => stack_0_1_op v c (Word.word_rcat (constant_mark lst))
  | Unknown _ => instruction_failure_result v [ShouldNotHappen]
  | Storage SLOAD => stack_1_1_op v c(vctx_storage   v)
  | Storage SSTORE => sstore v c
  | Pc JUMPI => jumpi v c
  | Pc JUMP => jump v c
  | Pc JUMPDEST => stack_0_0_op v c
  | Info CALLDATASIZE => stack_0_1_op v c (datasize v)
  | Stack CALLDATALOAD => stack_1_1_op v c (cut_data v)
  | Info CALLER => stack_0_1_op v c (Word.ucast(vctx_caller   v))
  | Arith ADD => stack_2_1_op v c (\<lambda> a b .  a + b)
  | Arith SUB => stack_2_1_op v c (\<lambda> a b .  a - b)
  | Arith ISZERO => stack_1_1_op v c (\<lambda> a .  if a =((word_of_int 0) ::  256 word) then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word))
  | Misc CALL => call v c
  | Misc RETURN => ret v c
  | Misc STOP => stop v c
  | Dup n => general_dup n v c
  | Stack POP => pop v c
  | Info GASLIMIT => stack_0_1_op v c(block_gaslimit  (vctx_block   v))
  | Arith inst_GT => stack_2_1_op v c (\<lambda> a b .  if a > b then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word))
  | Arith inst_EQ => stack_2_1_op v c (\<lambda> a b .  if a = b then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word))
  | Bits inst_AND => stack_2_1_op v c (\<lambda> a b .  a AND b)
  | Bits inst_OR => stack_2_1_op v c (\<lambda> a b .  a OR b)
  | Bits inst_XOR => stack_2_1_op v c (\<lambda> a b .  a XOR b)
  | Bits inst_NOT => stack_1_1_op v c (\<lambda> a .  (NOT a))
  | Bits BYTE =>
      stack_2_1_op v c get_byte
  | Sarith SDIV => stack_2_1_op v c
       (\<lambda> n divisor .  if divisor =((word_of_int 0) ::  256 word) then((word_of_int 0) ::  256 word) else
                         (let divisor = (sintFromW256 divisor) in
                         (let n = (sintFromW256 n) in
                         (let min_int :: int = (- (( 2 :: int) ^( 255 :: nat))) in
                         if (n = min_int) \<and> (divisor = - (( 1 :: int))) then (\<lambda> i .  word_of_int ( i)) min_int else
                         if divisor <( 0 :: int) then
                           (if n <( 0 :: int) then
                              (\<lambda> i .  word_of_int ( i)) ((- (( 1 :: int)) * n) div (- (( 1 :: int)) * divisor))
                            else
                              (\<lambda> i .  word_of_int ( i)) (- (( 1 :: int)) * (n div (- (( 1 :: int)) * divisor)))
                           )
                         else
                           (if n <( 0 :: int) then
                              (\<lambda> i .  word_of_int ( i)) (- (( 1 :: int)) * ((- (( 1 :: int)) * n) div divisor))
                            else
                              (\<lambda> i .  word_of_int ( i)) (n div divisor)))))
                           )
  | Sarith SMOD => stack_2_1_op v c
       (\<lambda> n divisor .  if divisor =((word_of_int 0) ::  256 word) then((word_of_int 0) ::  256 word) else
                         (let divisor = (sintFromW256 divisor) in
                         (let n = (sintFromW256 n) in
                         if divisor <( 0 :: int) then
                           (if n <( 0 :: int) then
                              (\<lambda> i .  word_of_int ( i)) (- (( 1 :: int)) * ((- (( 1 :: int)) * n) mod (- (( 1 :: int)) * divisor)))
                            else
                              (\<lambda> i .  word_of_int ( i)) (n mod (- (( 1 :: int)) * divisor))
                           )
                         else
                           (if n <( 0 :: int) then
                              (\<lambda> i .  word_of_int ( i)) (- (( 1 :: int)) * ((- (( 1 :: int)) * n) mod divisor))
                            else
                              (\<lambda> i .  word_of_int ( i)) (n mod divisor))))
                           )
  | Sarith SGT => stack_2_1_op v c
       (\<lambda> elm0 elm1 .  if word_sless elm1 elm0 then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word))
  | Sarith SLT => stack_2_1_op v c
       (\<lambda> elm0 elm1 .  if word_sless elm0 elm1 then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word))
  | Sarith SIGNEXTEND => stack_2_1_op v c signextend
  | Arith MUL => stack_2_1_op v c
       (\<lambda> a b .  a * b)
  | Arith DIV => stack_2_1_op v c
       (\<lambda> a divisor .  (if divisor =((word_of_int 0) ::  256 word) then((word_of_int 0) ::  256 word) else (\<lambda> i .  word_of_int ( i)) ((Word.uint a) div (Word.uint divisor))))
  | Arith MOD => stack_2_1_op v c
       (\<lambda> a divisor .  (if divisor =((word_of_int 0) ::  256 word) then((word_of_int 0) ::  256 word) else
            (\<lambda> i .  word_of_int ( i)) ((Word.uint a) mod (Word.uint divisor))
        ))
  | Arith ADDMOD => stack_3_1_op v c
       (\<lambda> a b divisor . 
           (if divisor =((word_of_int 0) ::  256 word) then((word_of_int 0) ::  256 word) else (\<lambda> i .  word_of_int ( i)) ((Word.uint a + Word.uint b) mod (Word.uint divisor))))
  | Arith MULMOD => stack_3_1_op v c
       (\<lambda> a b divisor . 
           (if divisor =((word_of_int 0) ::  256 word) then((word_of_int 0) ::  256 word) else (\<lambda> i .  word_of_int ( i)) ((Word.uint a * Word.uint b) mod (Word.uint divisor))))
  | Arith EXP => stack_2_1_op v c (\<lambda> a exponent . 
      (\<lambda> i .  word_of_int ( i))
       (word_exp (Word.uint a) (unat exponent)))
  | Arith inst_LT => stack_2_1_op v c (\<lambda> arg0 arg1 .  if arg1 > arg0 then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word))
  | Arith SHA3 => sha3 v c
  | Info ADDRESS => stack_0_1_op v c (Word.ucast(cctx_this   c))
  | Info BALANCE => stack_1_1_op v c (\<lambda> addr . (vctx_balance   v) (Word.ucast addr))
  | Info ORIGIN => stack_0_1_op v c (Word.ucast(vctx_origin   v))
  | Info CALLVALUE => stack_0_1_op v c(vctx_value_sent   v)
  | Info CODESIZE => stack_0_1_op v c ((\<lambda> i .  word_of_int ( i))(program_length  (cctx_program   c)))
  | Info GASPRICE => stack_0_1_op v c(block_gasprice  (vctx_block   v))
  | Info EXTCODESIZE => stack_1_1_op v c
       (\<lambda> arg .  (\<lambda> i .  word_of_int ( i))(program_length   ((vctx_ext_program   v) (Word.ucast arg))))
  | Info BLOCKHASH => stack_1_1_op v c(block_blockhash  (vctx_block   v))
  | Info COINBASE => stack_0_1_op v c (Word.ucast(block_coinbase  (vctx_block   v)))
  | Info TIMESTAMP => stack_0_1_op v c(block_timestamp  (vctx_block   v))
  | Info NUMBER => stack_0_1_op v c(block_number  (vctx_block   v))
  | Info DIFFICULTY => stack_0_1_op v c(block_difficulty  (vctx_block   v))
  | Memory MLOAD => mload v c
  | Memory MSTORE => mstore v c
  | Memory MSTORE8 => mstore8 v c
  | Memory CALLDATACOPY => calldatacopy v c
  | Memory CODECOPY => codecopy v c
  | Memory EXTCODECOPY => extcodecopy v c
  | Pc PC => pc v c
  | Log LOG0 => Evm.log(( 0 :: nat)) v c
  | Log LOG1 => Evm.log(( 1 :: nat)) v c
  | Log LOG2 => Evm.log(( 2 :: nat)) v c
  | Log LOG3 => Evm.log(( 3 :: nat)) v c
  | Log LOG4 => Evm.log(( 4 :: nat)) v c
  | Swap n => swap (unat n) v c
  | Misc CREATE => create v c
  | Misc CALLCODE => callcode v c
  | Misc SUICIDE => suicide v c
  | Misc DELEGATECALL => delegatecall v c
  | Info GAS => stack_0_1_op v c (gas v -((word_of_int 2) ::  256 word))
  | Memory MSIZE => stack_0_1_op v c (((word_of_int 32) ::  256 word) * (\<lambda> i .  word_of_int ( i))(vctx_memory_usage   v))
  )))"

lemma inst_gas :
  "instruction_sem v c inst =
   subtract_gas (predict_gas inst v c) (instruction_aux v c inst)"
by (simp add: instruction_aux_def)

end
