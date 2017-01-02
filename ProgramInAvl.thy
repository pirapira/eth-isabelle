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

theory ProgramInAvl

imports Main "~~/src/HOL/Data_Structures/AVL_Map" "./ContractSem"

begin

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

fun program_avl_of_lst ::
  "int (* initial position in the AVL *) \<Rightarrow> inst list (* instructions *)
   \<Rightarrow> (int * inst) avl_tree (* result *)"
where
  "program_avl_of_lst _ [] = Leaf"
  -- {* the empty program is translated into the empty tree. *}
| "program_avl_of_lst pos (Stack (PUSH_N bytes) # rest) =
   store_byte_list_in_program (pos + 1) bytes 
   (update pos (Stack (PUSH_N bytes))
          (program_avl_of_lst (pos + 1 + (int (length bytes))) rest))"
  -- {* The PUSH instruction is translated together with the immediate value. *}
| "program_avl_of_lst pos (Annotation _ # rest) =
    program_avl_of_lst pos rest"
  -- {* Annotations are skipped because they do not belong in this AVL tree. *}
| "program_avl_of_lst pos (i # rest) =
   update pos i (program_avl_of_lst (pos + 1) rest)"
  -- {* The other instructions are simply inserted into the AVL tree. *}
  
abbreviation program_content_of_lst :: "inst list \<Rightarrow> (int \<Rightarrow> inst option)"
where
"program_content_of_lst lst \<equiv>
   (lookup (program_avl_of_lst 0 lst))"

text {* I do not allow the AVL library to perform updates at arbitrary moments,
because that causes exponentially expensive computation (as measured with
the number of elements *) *}
declare update.simps [simp del]
declare lookup.simps [simp del]

text {* Instead, I only allow the following operations to happen (from left to right). *}

lemma updateL [simp] : "update x y Leaf = Node 1 Leaf (x,y) Leaf"
apply(simp add: update.simps)
done

lemma updateN_EQ [simp]: "cmp x a = Cmp.EQ \<Longrightarrow> update x y (Node h l (a, b) r) = Node h l (x, y) r"
apply(simp add: update.simps)
done

lemma updateN_GT [simp]: "cmp x a = Cmp.GT \<Longrightarrow> update x y (Node h l (a, b) r) = balR l (a, b) (update x y r)"
apply(simp add: update.simps)
done

lemma updateN_LT [simp]: "cmp x a = Cmp.LT \<Longrightarrow> update x y (Node h l (a, b) r) = balL (update x y l) (a, b) r"
apply(simp add: update.simps)
done

lemma lookupN_EQ [simp]: "cmp x a = Cmp.EQ \<Longrightarrow> lookup (Node h l (a, b) r) x = Some b"
apply(simp add: lookup.simps)
done

lemma lookupN_GT [simp]: "cmp x a = Cmp.GT \<Longrightarrow> lookup (Node h l (a, b) r) x = lookup r x"
apply(simp add: lookup.simps)
done

lemma lookupN_LT [simp]: "cmp x a = Cmp.LT \<Longrightarrow> lookup (Node h l (a, b) r) x = lookup l x"
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

end