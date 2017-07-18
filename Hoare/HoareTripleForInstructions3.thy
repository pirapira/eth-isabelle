(*
   Copyright 2017 Myriam Begel

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

theory "HoareTripleForInstructions3"

imports "HoareTripleForInstructions"
"../attic/BasicBlocks"
"../EvmFacts"

begin
type_synonym pred = "(state_element set \<Rightarrow> bool)"

(* We define here the program logic for BLOCKSs *)
(* We start with Hoare triples valid for the execution of one instruction *)

(* We have to add more instructions here *)
definition iszero_stack :: "w256 \<Rightarrow> w256" where
"iszero_stack w = (if w = 0 then (word_of_int 1) else (word_of_int 0))"

inductive triple_inst_arith :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_iszero :
    "triple_inst_arith 
      (\<langle> h \<le> 1023 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Arith ISZERO)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (iszero_stack w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"

inductive triple_inst_pc :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_jumpdest :
    "triple_inst_pc
      (\<langle> h \<le> 1024 \<and> Gjumpdest \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Pc JUMPDEST)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred (g - Gjumpdest) \<and>* rest)"
| inst_pc :
    "triple_inst_pc
      (\<langle> h \<le> 1023 \<and> Gbase \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Pc PC)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (word_of_int n) \<and>*
       gas_pred (g - Gbase) \<and>* rest)"

inductive triple_inst_stack :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_push_n :
    "triple_inst_stack
      (\<langle> h \<le> 1023 \<and> length lst > 0 \<and> 32 \<ge> length lst \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* program_counter n \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred g \<and>* rest)
      (n, Stack (PUSH_N lst))
      (continuing \<and>* memory_usage m \<and>*
       program_counter (n + 1 + int (length lst)) \<and>*
       stack_height (Suc h) \<and>* gas_pred (g - Gverylow) \<and>*
       stack h (word_rcat lst) \<and>* rest)"

inductive triple_inst_misc :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
 inst_stop :
    "triple_inst_misc
      (\<langle> h \<le> 1024 \<and> 0 \<le> g \<and> m \<ge> 0\<rangle> \<and>* continuing \<and>* memory_usage m \<and>*
       program_counter n \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Misc STOP)
      (stack_height h \<and>* not_continuing \<and>* memory_usage m \<and>*
       program_counter n \<and>* action (ContractReturn []) \<and>*
       gas_pred g \<and>* rest)"

inductive triple_inst :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_arith :
    "triple_inst_arith p (n, Arith i) q \<Longrightarrow> triple_inst p (n, Arith i) q"
| inst_misc :
    "triple_inst_misc p (n, Misc i) q \<Longrightarrow> triple_inst p (n, Misc i) q"
| inst_pc :
    "triple_inst_pc p (n, Pc i) q \<Longrightarrow> triple_inst p (n, Pc i) q"
| inst_stack :
    "triple_inst_stack p (n, Stack i) q \<Longrightarrow> triple_inst p (n, Stack i) q"
| inst_strengthen_pre:
    "triple_inst p i q \<Longrightarrow> (\<And>s. r s \<longrightarrow> p s) \<Longrightarrow> triple_inst r i q"
| inst_false_pre:
    "triple_inst \<langle>False\<rangle> i post"
end