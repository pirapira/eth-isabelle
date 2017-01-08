theory Hoare

imports Main "./lem/Evm"

begin

(* Following Magnus Myreen's thesis "Formal verification of machine-code programs" 3.2.4 *)  

datatype state_element =
    StackHeightElm "nat"  (* considering making it int *)
  | StackElm "nat * w256" (* position, value *)
    (* The position is counted from the bottom *)
    (* StackElement (0, 300) says the oldest element on the stack is 300 *)
  | StorageElm "w256 * w256" (* index, value *)
  | MemoryElm "w256 * byte" (* address, value *)
  | LogElm "nat * log_entry" (* position, log *)
    (* Log (0, entry) says that the first recorded log entry is 0 *)
  | PcElm "int" (* program counter *)
  | GasElm "int" (* remaining gas *)
  | MemoryUsageElm "int" (* current memory usage *)
  | CodeElm "int * inst" (* a position containing an instruction *)
  | ThisAccountElm "address" (* The address of this account *)
  | BalanceElm "address * w256" (* address, amount *)
  | BlockInfoElm "block_info" (* the current block.  This might be broken down to more elements. *)
  | CallerElm "address"
  | OriginElm "address"
  | SentValueElm "w256"
  | SentDataLengthElm "nat" (* considering making it int *)
  | SentDataElm "nat * byte" (* position, content.  Considering making position an int *)
  | ExtProgramSizeElm "address * int" (* address, size.  Considering making size an int *)
  | ExtProgramElm "address * nat * byte" (* address, position, byte.  Considering making position an int *)
  | ActionToEnvironmentElm "contract_action option" (* None indicates continued execution *)


definition memory_as_set :: "memory \<Rightarrow> state_element set"
  where
    "memory_as_set m == { MemoryElm (a, v) | a v. m a = v }"
    
definition storage_as_set :: "storage \<Rightarrow> state_element set"
  where
    "storage_as_set s == { StorageElm (i, v) | i v. s i = v}"

definition balance_as_set :: "(address \<Rightarrow> w256) \<Rightarrow> state_element set"
  where
    "balance_as_set b == { BalanceElm (a, v) | a v. b a = v }"

definition stack_as_set :: "w256 list \<Rightarrow> state_element set"
  where
    "stack_as_set s == { StackHeightElm (length s) } \<union>
                       { StackElm (idx, v) | idx v. s ! idx = v }"

definition data_sent_as_set :: "byte list \<Rightarrow> state_element set"
  where
    "data_sent_as_set lst == { SentDataLengthElm (length lst) } \<union>
                             { SentDataElm (idx, v) | idx v. lst ! idx = v }"

definition ext_program_as_set :: "(address \<Rightarrow> program) \<Rightarrow> state_element set"
  where
    "ext_program_as_set ext ==
      { ExtProgramSizeElm (adr, s) | adr s. program_length (ext adr) = s } \<union>
      { ExtProgramElm (adr, pos, b) | adr pos b. program_as_natural_map (ext adr) pos = b }
    "

definition log_as_set :: "log_entry list \<Rightarrow> state_element set"
  where
    "log_as_set logs ==
      { LogElm (pos, l) | pos l. logs ! pos = l}
    "

definition program_as_set :: "program \<Rightarrow> state_element set"
  where
    "program_as_set prg ==
      { CodeElm (pos, i) | pos i. program_content prg pos = Some i  } \<union>
      { CodeElm (pos, Misc STOP) | pos. program_content prg pos = None }
    "

definition context_as_set :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> state_element set"
  where
    "context_as_set v c ==
       stack_as_set (vctx_stack v)
    \<union> memory_as_set (vctx_memory v)
    \<union> storage_as_set (vctx_storage v)
    \<union> balance_as_set (vctx_balance v)
    \<union> log_as_set (vctx_logs v)
    \<union> program_as_set (cctx_program c)
    \<union> { MemoryUsageElm (vctx_memory_usage v)
      , CallerElm (vctx_caller v)
      , SentValueElm (vctx_value_sent v)
      , OriginElm (vctx_origin v)
      , BlockInfoElm (vctx_block v)
      , GasElm (vctx_gas v)
      , ThisAccountElm (cctx_this c)
      }
    "

(* From Magnus Myreen's thesis, Section 3.3 *)
definition sep :: "(state_element set \<Rightarrow> bool) \<Rightarrow> (state_element set \<Rightarrow> bool) \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "sep p q s == \<exists> u v. p u \<and> q v \<and> u \<union> v = s \<and> u \<inter> v = {} "

notation sep (infixr "*" 60)

definition emp :: "state_element set \<Rightarrow> bool"
  where
    "emp s == (s = {})"

definition pure :: "bool \<Rightarrow> state_element set \<Rightarrow> bool"
  where
    "pure b s == emp s \<and> b"

notation pure ("\<langle> _ \<rangle>")

  

(* Some rules about this if-then-else should be derivable. *)

definition if_then_else :: "int \<Rightarrow> inst list \<Rightarrow> inst list \<Rightarrow> inst list \<Rightarrow> inst list"
where
"if_then_else beginning cond then_case else_case =
 cond
 @ (* beginning + length cond *)
 [Stack (PUSH_N (word_rsplit (word_of_int (beginning + int (length cond) + 8 + int (length else_case)) :: 16 word))), Pc JUMPI] 
 @ (* beginning + length cond + 4 *)
 else_case
 @ (* beginning + length cond + length else_case + 4 *)
 [Stack (PUSH_N (word_rsplit (word_of_int (beginning + int (length cond) + int (length else_case) + 9 + int (length then_case)) :: 16 word))), Pc JUMP]
 @ (* beginning + length cond + length else_case + 8 *)
 [Pc JUMPDEST]
 @ (* beginning + length cond + length else_case + 9 *)
 then_case
 @ (* beginning + length cond + length else_case + 9 + length then_case *)
 [Pc JUMPDEST]
"

(* example of if_then_else *)

(* loop *)

  
(* precondition / post condition pair *)

(* What would be the type of precondition? *)
(* instruction_result \<Rightarrow> bool
 * In the precondition, the program counter is overwritten.
 *)

(* validity of pre, program, post triples.
 * Failures are considered as success.
 *)

end
