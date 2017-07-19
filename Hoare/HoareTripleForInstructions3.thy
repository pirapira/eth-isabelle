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

fun arith_2_1_low:: "arith_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "arith_2_1_low MUL = (\<lambda> a b .  a * b) "
| "arith_2_1_low DIV =
	(\<lambda> a divisor .
		(if divisor =(((word_of_int 0) ::  256 word))
			then(((word_of_int 0) ::  256 word))
			else (\<lambda> i .  word_of_int ( i)) ((Word.uint a) div (Word.uint divisor))))"
| "arith_2_1_low MOD =
  (\<lambda> a divisor .  (if divisor =(((word_of_int 0) ::  256 word)) then(((word_of_int 0) ::  256 word)) else
            (\<lambda> i .  word_of_int ( i)) ((Word.uint a) mod (Word.uint divisor))))"
| "arith_2_1_low _ = (\<lambda> a b . 0)"

fun arith_2_1_verylow:: "arith_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "arith_2_1_verylow ADD = (\<lambda> a b .  a + b) "
| "arith_2_1_verylow SUB = (\<lambda> a b .  a - b) "
| "arith_2_1_verylow inst_GT =
	(\<lambda> a b .  if a > b then(((word_of_int 1) ::  256 word)) else(((word_of_int 0) ::  256 word)))"
| "arith_2_1_verylow inst_EQ =
	(\<lambda> a b .  if a = b then(((word_of_int 1) ::  256 word)) else(((word_of_int 0) ::  256 word)))"
| "arith_2_1_verylow inst_LT =
	(\<lambda> a b .  if b > a then(((word_of_int 1) ::  256 word)) else(((word_of_int 0) ::  256 word)))"
| "arith_2_1_verylow _ = (\<lambda> a b . 0)"

fun arith_3_1:: "arith_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "arith_3_1 ADDMOD =
		(\<lambda> a b divisor .
     (if divisor =(((word_of_int 0) ::  256 word)) then(((word_of_int 0) ::  256 word))
			else (\<lambda> i .  word_of_int ( i)) ((Word.uint a + Word.uint b) mod (Word.uint divisor))))"
| "arith_3_1 MULMOD =
		(\<lambda> a b divisor .
     (if divisor =(((word_of_int 0) ::  256 word)) then(((word_of_int 0) ::  256 word))
			else (\<lambda> i .  word_of_int ( i)) ((Word.uint a * Word.uint b) mod (Word.uint divisor))))"
| "arith_3_1 _ = (\<lambda> a b c . 0)"

inductive triple_inst_arith :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_arith_2_1_low :
    "i \<in> {MUL, DIV, MOD} \<Longrightarrow>
		triple_inst_arith 
      (\<langle> h \<le> 1022 \<and> Glow \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith i)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_low i v w) \<and>*
       gas_pred (g - low) \<and>* rest)"
|  inst_arith_2_1_verylow :
    "i \<in> {ADD, SUB, inst_GT, inst_EQ, inst_LT} \<Longrightarrow>
		 triple_inst_arith 
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith i)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_verylow i v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_arith_3_1 :
    "i \<in> {ADDMOD, MULMOD} \<Longrightarrow>
		 triple_inst_arith 
      (\<langle> h \<le> 1021 \<and> Gmid \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc (Suc h))) \<and>* stack (Suc (Suc h)) u \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith i)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_3_1 i u v w) \<and>*
       gas_pred (g - Gmid) \<and>* rest)"
| inst_iszero :
    "triple_inst_arith 
      (\<langle> h \<le> 1023 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Arith ISZERO)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (iszero_stack w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"

fun bits_2_1_verylow:: "bits_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "bits_2_1_verylow BYTE = get_byte"
| "bits_2_1_verylow inst_AND = (\<lambda> a b .  a AND b)"
| "bits_2_1_verylow inst_OR = (\<lambda> a b .  a OR b)"
| "bits_2_1_verylow inst_XOR = (\<lambda> a b .  a XOR b)"
| "bits_2_1_verylow _ = (\<lambda> a b  . 0)"

inductive triple_inst_bits :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_instNOT :
    "triple_inst_bits
      (\<langle> h \<le> 1023 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Bits inst_NOT)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (NOT w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_bits_2_1_verylow :
    "i \<in> {inst_AND, inst_OR, inst_XOR, BYTE} \<Longrightarrow>
		 triple_inst_bits 
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Bits i)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (bits_2_1_verylow i v w) \<and>*
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
| inst_pop :
    "triple_inst_stack
      (\<langle> h \<le> 1023 \<and> Gbase \<le> g \<and> m \<ge> 0\<rangle> **
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Stack POP)
      (continuing \<and>* program_counter (n + 1) \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred (g - Gbase) \<and>* rest)"

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
| inst_bits :
    "triple_inst_misc p (n, Bits i) q \<Longrightarrow> triple_inst p (n, Bits i) q"
| inst_misc :
    "triple_inst_misc p (n, Misc i) q \<Longrightarrow> triple_inst p (n, Misc i) q"
| inst_pc :
    "triple_inst_pc p (n, Pc i) q \<Longrightarrow> triple_inst p (n, Pc i) q"
| inst_stack :
    "triple_inst_stack p (n, Stack i) q \<Longrightarrow> triple_inst p (n, Stack i) q"
| inst_swap :
		"triple_inst 
			(\<langle> h \<le> 1024 \<and> Suc (unat n) < h \<and> g \<ge> Gverylow \<and> m \<ge> 0\<rangle> **
			 stack_height h ** stack (h - 1) w ** stack (h - (unat n) - 2) v **
			 program_counter k ** gas_pred g ** memory_usage m **
			 continuing ** rest)
			(k, Swap n)
			(stack_height h ** stack (h - 1) v ** stack (h - (unat n) - 2) w **
			 program_counter (k + 1) ** gas_pred (g - Gverylow) **
			 memory_usage m ** continuing ** rest)"
| inst_strengthen_pre:
    "triple_inst p i q \<Longrightarrow> (\<And>s. r s \<longrightarrow> p s) \<Longrightarrow> triple_inst r i q"
| inst_false_pre:
    "triple_inst \<langle>False\<rangle> i post"
end