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

theory "BasicBlocks"

imports "../lem/Evm"
"Apply_Trace_Cmd"

begin
(* Types definitions *)
datatype tblock =
Next | Jump | Jumpi | No

type_synonym position = "int"
type_synonym pos_inst = "position * inst"
type_synonym vert = "pos_inst list * tblock"
type_synonym vertex = "int * vert"
type_synonym vertices = "vertex list"

type_synonym stack_value = "w256 option"

record basic_blocks =
blocks_indexes :: "int list"
blocks_list :: "int \<Rightarrow> vert option"

(* Auxiliary functions *)

abbreviation v_ind :: "vertex \<Rightarrow> int" where
"v_ind v == fst v"

abbreviation v_ty :: "vertex \<Rightarrow> tblock" where
"v_ty v == snd (snd v)"

abbreviation v_insts :: "vertex \<Rightarrow> pos_inst list" where
"v_insts v == fst (snd v)"

definition byteListInt :: "8 word list \<Rightarrow> int" where
"byteListInt l = uint ((word_rcat l):: 32 word)"

definition next_i :: "vertices \<Rightarrow> int \<Rightarrow> int" where
 "next_i v n = v_ind (hd (dropWhile (\<lambda>u. (v_ind u)\<le>n) v))"
(*  "next_i (i#j#l) n = (if fst i=n then fst j else next_i (j#l) n)"*)

definition find_block :: "int \<Rightarrow> vertex \<Rightarrow> bool" where
"find_block n bl ==  n=v_ind bl"

fun good_dest :: "int \<Rightarrow> vertices \<Rightarrow> bool" where
  "good_dest m [] = False"
| "good_dest m ((n,[],_)#l) = good_dest m l"
| "good_dest m ((n,(_,i)#inst,_)#l) = (if m = n then (i = Pc JUMPDEST) else good_dest m l )"

definition extract_indexes :: "vertices \<Rightarrow> int list" where
"extract_indexes xs = map v_ind xs"

fun extract_blocks :: "vertices \<Rightarrow> int \<Rightarrow> vert option" where
"extract_blocks [] = Map.empty"
|"extract_blocks (x#xs) = (extract_blocks xs)(fst x:= Some (snd x))"

fun rebuild_vertices :: "int list \<Rightarrow> (int \<Rightarrow> vert option) \<Rightarrow> vertices" where
"rebuild_vertices [] m = []"
|"rebuild_vertices (x#xs) m = (x,the (m x)) # (rebuild_vertices xs m)"

(* Stack manipulations *)

definition stack_swap :: "stack_value list \<Rightarrow> nat \<Rightarrow> stack_value list" where
"stack_swap st n = (let first = hd st in
  let unchanged = take (n -2) (tl st) in
  let to_swap = hd (drop (max (n-1) 1) st) in
  (to_swap # unchanged) @ (first # (drop n st))
)"

value "stack_swap [Value 1, Value 2, Value 3, Value 4] 2"

definition stack_dup :: "stack_value list \<Rightarrow> nat \<Rightarrow> stack_value list" where
"stack_dup st n = (st ! (n-1)) # st"

value "stack_dup [Value 1, Value 2, Value 3, Value 4] 2"

definition block_pt :: "pos_inst list \<Rightarrow> pos_inst \<Rightarrow> int" where
 "block_pt bl pt = (case bl of
   [] \<Rightarrow> fst pt
  | _ \<Rightarrow> fst (hd bl))"

(* Main functions *)

(* Add the address of each instruction *)

fun add_address' :: "inst list \<Rightarrow> int \<Rightarrow> pos_inst list" where
"add_address' [] n = []"
| "add_address' (x#xs) n = (n,x)#(add_address' xs (n + inst_size x))"

definition add_address :: "inst list \<Rightarrow> pos_inst list" where
"add_address xs = add_address' xs 0"

(* The execution of a basic block must be sequential. *)
(* We remove JUMP and JUMPI instructions and cut after them or a stopping instruction *)
(* and before a Jump destination. *)
fun aux_basic_block :: "pos_inst list \<Rightarrow> pos_inst list \<Rightarrow> vertices" where
 "aux_basic_block [] [] = []"
|"aux_basic_block [] block = [(fst (hd block), block, Next)]"
|"aux_basic_block ((i)#tl1) block =
	(let bl_pt = block_pt block i in
  (case snd i of
    Pc JUMPDEST \<Rightarrow> (if block = [] then (aux_basic_block tl1 [i])
    else (bl_pt, block, Next) # (aux_basic_block tl1 [i]))
  | Pc JUMP \<Rightarrow>(bl_pt, block, Jump) # ( aux_basic_block tl1 [])
  | Pc JUMPI \<Rightarrow>(bl_pt, block, Jumpi) # ( aux_basic_block tl1 [])
  | Misc RETURN \<Rightarrow>(bl_pt, block @ [i], No) # ( aux_basic_block tl1 [])
  | Misc SUICIDE \<Rightarrow>(bl_pt, block @ [i], No) # ( aux_basic_block tl1 [])
  | Misc STOP \<Rightarrow>(bl_pt, block @ [i], No) # ( aux_basic_block tl1 [])
  | _ \<Rightarrow> aux_basic_block tl1 (block@[i])))"
declare aux_basic_block.simps[simp del]

definition build_vertices :: "inst list \<Rightarrow> vertices" where
"build_vertices prog == aux_basic_block (add_address prog) []"

definition build_blocks :: "inst list \<Rightarrow> basic_blocks" where
"build_blocks prog = (let blocks = build_vertices prog in
(let ind = (extract_indexes blocks) in
(|blocks_indexes = ind,
  blocks_list = map_of blocks|)
))"

(* Verification *)
lemmas reg_inst_splits = inst.splits misc_inst.splits pc_inst.splits

(* Check that we can rebuild the initial list of instructions from basic blocks *)
fun reconstruct_bytecode :: "vertices \<Rightarrow> inst list" where
 "reconstruct_bytecode [] = []"
| "reconstruct_bytecode ((n,b,Jump)#q) = (map snd b)@[Pc JUMP] @ (reconstruct_bytecode q)"
| "reconstruct_bytecode ((n,b,Jumpi)#q) = (map snd b)@[Pc JUMPI] @ (reconstruct_bytecode q)"
| "reconstruct_bytecode ((n,b,_)#q) = (map snd b) @ (reconstruct_bytecode q)"

lemma rev_basic_blocks: "reconstruct_bytecode (aux_basic_block i b) = (map snd b)@(map snd i)"
apply(induction i arbitrary: b)
apply(case_tac b)
apply(auto simp: Let_def aux_basic_block.simps split: reg_inst_splits)
done

lemma remove_address:
"map snd (add_address' i k) = i"
by(induction i arbitrary: k; simp)

theorem reverse_basic_blocks: "reconstruct_bytecode (build_vertices i) = i"
apply(simp add: rev_basic_blocks build_vertices_def add_address_def remove_address)
done

(* Define how BLOCKSs should be for the program logic to be sound *)

fun reg_inst :: "inst \<Rightarrow> bool" where
 "reg_inst (Pc JUMP) = False"
| "reg_inst (Pc JUMPI) = False"
|"reg_inst (Pc _) = True"
|"reg_inst (Misc STOP) = False"
|"reg_inst (Misc RETURN) = False"
|"reg_inst (Misc SUICIDE) = False"
|"reg_inst (Misc _) = True"
|"reg_inst _ = True"

definition reg_block :: "pos_inst list \<Rightarrow> bool" where
"reg_block xs = list_all reg_inst (map snd xs)"

definition reg_vertex :: "vertex \<Rightarrow> bool" where
"reg_vertex v = (case v_ty v of
No \<Rightarrow> reg_block (butlast (v_insts v))
| _ \<Rightarrow> reg_block (v_insts v))"

definition reg_vertices :: "vertices \<Rightarrow> bool" where
"reg_vertices xs = list_all reg_vertex xs"

fun seq_block :: "pos_inst list \<Rightarrow> bool" where 
"seq_block [] = True"
| "seq_block [x] = True"
| "seq_block (x#y#ys) = (fst y = fst x + inst_size (snd x) \<and> seq_block (y#ys))"
declare seq_block.simps[simp del]

definition last_no::"pos_inst list \<Rightarrow> bool" where
"last_no insts == snd (last insts) \<in> {Misc STOP, Misc RETURN, Misc SUICIDE}"

(* Define a 'program' from a BLOCKS *)

fun blocks_insts_aux :: "basic_blocks \<Rightarrow> int list \<Rightarrow> pos_inst list" where
  "blocks_insts_aux c [] = []"
| "blocks_insts_aux c (x#xs) = (case blocks_list c x of
    None \<Rightarrow> blocks_insts_aux c xs
  | Some (b,_) \<Rightarrow> b @ (blocks_insts_aux c xs))"

definition blocks_insts :: "basic_blocks \<Rightarrow> pos_inst set" where
"blocks_insts c = set (blocks_insts_aux c (blocks_indexes c))"

fun inst_size_list::"pos_inst list \<Rightarrow> int" where
"inst_size_list [] = 0"
| "inst_size_list (x#xs) = inst_size (snd x) + inst_size_list xs"

fun blocks_pos_insts :: "vertices \<Rightarrow> pos_inst list" where
 "blocks_pos_insts [] = []"
| "blocks_pos_insts ((n,b,Jump)#q) = b@[(n+inst_size_list b,Pc JUMP)] @ (blocks_pos_insts q)"
| "blocks_pos_insts ((n,b,Jumpi)#q) = b@[(n+inst_size_list b,Pc JUMPI)] @ (blocks_pos_insts q)"
| "blocks_pos_insts ((n,b,_)#q) = b @ (blocks_pos_insts q)"

fun blocks_vertices:: "basic_blocks \<Rightarrow> int list \<Rightarrow> vertex list" where
"blocks_vertices c [] = []"
| "blocks_vertices c (x#xs) = (case blocks_list c x of
  None \<Rightarrow> blocks_vertices c xs
  | Some b \<Rightarrow> (x,b) # (blocks_vertices c xs))"

definition blocks_content ::"basic_blocks \<Rightarrow> int \<Rightarrow> inst option " where
"blocks_content c  = map_of (blocks_pos_insts (blocks_vertices c (blocks_indexes c)))"

definition blocks_length :: "basic_blocks \<Rightarrow> int " where
"blocks_length c =
  (case blocks_list c (last (blocks_indexes c)) of
    None \<Rightarrow> 0 (*Should not happen*)
  | Some (i,Jump) \<Rightarrow> fst (last i) +  inst_size (snd (last i))
  | Some (i,Jumpi) \<Rightarrow> fst (last i) + inst_size (snd (last i))
  | Some (i,_) \<Rightarrow> fst (last i))"

definition program_from_blocks:: "basic_blocks \<Rightarrow> program" where
"program_from_blocks c = ( (|
  program_content = blocks_content c,
  program_length = blocks_length c,
  program_annotation = (\<lambda> _ .  [])
|) )"

definition wf_blocks:: "basic_blocks \<Rightarrow> bool" where
"wf_blocks c == 
(\<forall>n insts ty.
(blocks_list c n = Some (insts, ty) \<longrightarrow>
	n \<in> set (blocks_indexes c) \<and> reg_vertex (n, insts, ty) \<and>
  (insts \<noteq> [] \<longrightarrow> (fst (hd insts) = n)) \<and> seq_block insts \<and>
  0 \<le> n \<and> n < 2 ^ 256) \<and>
(blocks_list c n = Some (insts, Next) \<longrightarrow>
	 insts \<noteq> []) \<and>
(blocks_list c n = Some (insts, Jump) \<longrightarrow>
	program_content (program_from_blocks c) (n + inst_size_list insts) = Some (Pc JUMP)) \<and>
(blocks_list c n = Some (insts, Jumpi) \<longrightarrow>
	program_content (program_from_blocks c) (n + inst_size_list insts) = Some (Pc JUMPI)) \<and>
(blocks_list c n = Some (insts, No) \<longrightarrow>
	 insts \<noteq> [] \<and> last_no insts)
)"

(* Proof that we build well formed BLOCKSs *)

lemma index_have_blocks:
"c = build_blocks bytecode \<Longrightarrow>
 \<not> blocks_list c n = None \<Longrightarrow>
 n \<in> set (blocks_indexes c)"
by(simp add: Let_def build_blocks_def extract_indexes_def map_of_eq_None_iff)

lemma index_block_eq:
"(n, (j,i)#b, t)#xs = aux_basic_block insts block \<Longrightarrow>
j=n"
apply(induction insts arbitrary: block n j i t xs b)
 apply(case_tac block)
  apply(simp add: aux_basic_block.simps block_pt_def split:if_splits list.splits)
  apply(clarsimp)
 apply(simp add: aux_basic_block.simps block_pt_def split:if_splits list.splits)
 apply(clarsimp)
apply(simp add: aux_basic_block.simps Let_def)
apply(simp split: inst.splits add: inst_size_def inst_code.simps)
 apply(clarsimp simp add: block_pt_def split: pc_inst.splits list.splits if_splits)
apply(clarsimp simp add: block_pt_def split: misc_inst.splits list.splits)
done

lemma seq_block_compose:
"seq_block bl \<Longrightarrow>
 \<forall>i j. bl \<noteq> [] \<longrightarrow> last bl = (j, i) \<longrightarrow> m = j + inst_size i \<Longrightarrow>
 seq_block (bl @ [(m, a)])"
apply(induction bl)
 apply(simp add: seq_block.simps)
apply(case_tac bl; simp)
 apply(simp add: seq_block.simps)
apply(simp add: seq_block.simps)
done

lemma in_aux_bb_intermediate:
"(n, b, t) \<in> set (aux_basic_block insts block) \<Longrightarrow>
\<exists>ys bl xs. (n, b, t)#xs = aux_basic_block ys bl"
apply(induction insts arbitrary: block)
 apply(rule_tac x="[]" in exI)
 apply(case_tac block)
 apply(simp add: aux_basic_block.simps split: if_splits)+
 apply(rule_tac x=block in exI, simp add: aux_basic_block.simps)
apply(subgoal_tac "(n, b, t) \<in> set
			(aux_basic_block (a # insts) block)")
 apply(drule subst[OF aux_basic_block.simps(3)])
 apply(simp add: Let_def)
  apply(clarsimp split: inst.splits simp add: inst_size_def inst_code.simps)
  apply(simp split: pc_inst.splits if_splits add: inst_size_def inst_code.simps;
				erule disjE, rule_tac x="(a,Pc x9) # insts" in exI, rule_tac x=block in exI,
				simp add: aux_basic_block.simps Let_def, fastforce)
 apply(simp split: misc_inst.splits if_splits add: inst_size_def inst_code.simps;
				erule disjE, rule_tac x="(a,Misc x13) # insts" in exI, rule_tac x=block in exI,
				simp add: aux_basic_block.simps Let_def, fastforce)
apply(assumption)
done

(* Lemmas to show that build blocks are regular *)
lemma list_all_in:
"x \<in> set xs \<Longrightarrow> list_all P xs \<Longrightarrow> P x"
 apply(induction xs)
  apply(simp)
 apply(case_tac "x=a"; simp)
done

lemma reg_block_butlast:
"reg_block xs \<Longrightarrow> reg_block (butlast xs)"
 apply(induction xs)
  apply(simp)
 apply(simp add: reg_block_def List.List.list.pred_map)
done

lemmas reg_simps =
reg_vertices_def reg_vertex_def reg_block_def

lemma reg_aux_bb:
"reg_block block \<Longrightarrow>
 reg_vertices (aux_basic_block insts block)"
 apply(induction insts arbitrary: block)
  apply(case_tac block)
   apply(simp add: reg_simps aux_basic_block.simps)
  apply(simp add: reg_vertices_def reg_vertex_def aux_basic_block.simps)
 apply(simp add:Let_def aux_basic_block.simps)
 apply(case_tac block; clarsimp)
  apply(simp split: inst.split pc_inst.split misc_inst.split)
  apply(simp add:reg_simps)
 apply(simp split: inst.split pc_inst.split misc_inst.split)
 apply(simp add:reg_simps)
done

lemma reg_bb:
"reg_vertices (build_vertices insts)"
 apply(simp add: build_vertices_def)
 apply(rule reg_aux_bb)
 apply(simp add: reg_simps)
done
value "sum_list (map inst_size [Pc JUMP, Pc PC])"

lemma seq_block_tl:
"seq_block (x#xs) \<Longrightarrow> seq_block xs"
apply(case_tac xs)
 apply(simp add: seq_block.simps)+
done

lemma seq_block_append:
"seq_block bl \<Longrightarrow>
bl \<noteq> [] \<longrightarrow> fst a = fst (last bl) + inst_size (snd (last bl))\<Longrightarrow>
seq_block (bl@[a])"
apply(induction bl; simp add: seq_block.simps)
apply(simp add: seq_block_tl)
apply(case_tac bl; simp add: seq_block.simps)
done

lemma seq_block_tl':
"seq_block (xs@ys) \<Longrightarrow> seq_block ys"
apply(induction xs; simp add: seq_block.simps)
apply(simp add: seq_block_tl)
done

lemma inst_size_pos:
"inst_size x > 0"
apply(simp add: inst_size_def)
apply(case_tac x; clarsimp simp add: inst_code.simps)
apply(case_tac x10; clarsimp simp add: stack_inst_code.simps)
apply(simp split: if_splits)
done

abbreviation bound where
"bound mini maxi n == mini \<le> (fst n) \<and> (fst n) < maxi"

lemma sequential_basic_blocks:
"seq_block ys \<Longrightarrow>
 seq_block bl \<Longrightarrow>
 list_all (bound 0 m) ys \<Longrightarrow>
 list_all (bound 0 m) bl \<Longrightarrow>
 ys \<noteq> [] \<and> bl \<noteq> [] \<longrightarrow> fst (hd ys) = fst (last bl) + inst_size (snd (last bl))\<Longrightarrow>
 (n, insts, ty) \<in> set (aux_basic_block ys bl) \<Longrightarrow>
 seq_block insts \<and> 0 \<le> n \<and> n < m"
apply(induction ys arbitrary: bl)
 apply(case_tac bl; simp add: aux_basic_block.simps)
apply(simp add: aux_basic_block.simps Let_def)
 apply(case_tac "reg_inst (snd a) \<and> (snd a) \<noteq> Pc JUMPDEST")
 apply(drule_tac x="bl@[a]" in meta_spec)
 apply(simp add: seq_block_tl seq_block_append)
 apply(drule meta_mp; clarsimp; case_tac ys; simp add: seq_block.simps;
       simp split: reg_inst_splits)
apply(case_tac "(snd a) = Pc JUMPDEST")
 apply(clarsimp)
 apply(drule_tac x="[(a, Pc JUMPDEST)]" in meta_spec)
 apply(simp add: seq_block_tl seq_block.simps)
 apply(drule meta_mp; case_tac ys; simp add: seq_block.simps)
  apply(case_tac "bl=[]"; simp split: if_splits)
  apply(erule disjE; clarsimp simp add: block_pt_def split: list.splits)
 apply(case_tac "bl=[]"; simp split: if_splits)
 apply(erule disjE; clarsimp simp add: block_pt_def split: list.splits)
apply(drule meta_spec[where x="[]"])
apply(simp add: seq_block_tl seq_block_append seq_block.simps)
apply(simp split: reg_inst_splits)
    apply(erule disjE; clarsimp simp add: block_pt_def seq_block_append split: list.splits)+
done

lemma seq_block_add_address:
"seq_block (add_address' insts k)"
apply(induction insts arbitrary:k)
 apply(simp add: seq_block.simps)
apply(simp)
apply(case_tac insts; simp add: seq_block.simps)
done

lemma bound_add_address':
"(x,y) \<in> set (add_address' xs k) \<Longrightarrow>
k \<le> x \<and> x \<le> fst (last (add_address' xs k))"
apply(induction xs arbitrary: k x y)
 apply(simp)
apply(simp)
apply(erule disjE; simp)
 apply(case_tac "add_address' xs (k + inst_size a)"; clarsimp)
 apply(drule_tac x="k + inst_size a" in meta_spec; drule_tac x="aa" and y="b" in meta_spec2)
 apply(simp split: list.splits if_splits)
  apply(case_tac xs; simp)
  apply(drule conjunct1; drule sym[where s="_ + _"]; simp add: inst_size_pos Orderings.order_class.order.strict_implies_order)
 apply(erule conjE)
 apply(subgoal_tac "k \<le> k + inst_size a"; simp)
 apply(simp add: inst_size_pos Orderings.order_class.order.strict_implies_order)
apply(drule_tac x="k + inst_size a" in meta_spec; drule_tac x="x" and y="y" in meta_spec2)
apply(simp)
apply(erule conjE)
apply(rule conjI; clarsimp)
apply(subgoal_tac "k \<le> k + inst_size a"; simp)
apply(simp add: inst_size_pos Orderings.order_class.order.strict_implies_order)
done

lemma non_empty_block_next:
"(n, [], Next) # xs = aux_basic_block ys bl \<Longrightarrow> False"
apply(induction ys arbitrary:bl)
 apply(case_tac bl; simp add: aux_basic_block.simps)
apply(simp add: aux_basic_block.simps Let_def)
apply(simp split: reg_inst_splits if_splits; fastforce)
done

lemma block_no:
"(n, insts, No) \<in> set (aux_basic_block ys bl) \<Longrightarrow>
 reg_block bl \<Longrightarrow>
 insts \<noteq> [] \<and> last_no insts"
apply(induction ys arbitrary:bl)
 apply(case_tac bl; simp add: aux_basic_block.simps last_no_def)
apply(simp add: aux_basic_block.simps Let_def)
apply(case_tac "reg_inst (snd a) \<and> snd a \<noteq> Pc JUMPDEST")
 apply(drule_tac x="bl @ [a]" in meta_spec; simp add: reg_block_def)
 apply(simp split: reg_inst_splits if_splits)
apply(case_tac "snd a = Pc JUMPDEST")
 apply(simp; case_tac bl; simp split: if_splits)
  apply(drule_tac x="[a]" in meta_spec; simp add: reg_block_def)
 apply(drule_tac x="[a]" in meta_spec; simp add: reg_block_def)
apply(drule_tac x="[]" in meta_spec; simp add: reg_block_def)
apply(simp split: reg_inst_splits if_splits)
  apply(erule disjE; simp add: last_no_def)+
done

(*Draft*)
lemma seq_block_sumC:
"seq_block ((i,j) # list @ (a, b) # xs) \<Longrightarrow>
 i + (inst_size j + inst_size_list list) = a"
apply(induction list arbitrary: i j; clarsimp)
 apply(simp add: seq_block.simps)
apply(simp add: seq_block.simps)
apply(fastforce)
done

lemma rev_basic_blocks_add:
"seq_block (b@i) \<Longrightarrow> 
blocks_pos_insts (aux_basic_block i b) = b@i"
apply(induction i arbitrary: b)
 apply(case_tac b)
  apply(simp add: aux_basic_block.simps)
 apply(simp add: aux_basic_block.simps)
apply(simp add: aux_basic_block.simps Let_def)
apply(case_tac b; clarsimp)
 apply(case_tac "reg_inst b")
  apply(drule_tac x="[(a, b)]" in meta_spec; simp)
  apply(case_tac b; simp; rename_tac x; case_tac x; simp)
 apply(drule_tac x="[]" in meta_spec; simp)
 apply(case_tac b; simp; rename_tac x; case_tac x; simp add: block_pt_def seq_block_tl)
apply(case_tac "reg_inst b \<and> b \<noteq> Pc JUMPDEST")
 apply(drule_tac x="(((aa, bb) # list) @ [(a, b)])" in meta_spec; simp)
 apply(case_tac b; simp; rename_tac x; case_tac x; simp)
apply(case_tac "b=Pc JUMPDEST")
 apply(drule_tac x="[(a, b)]" in meta_spec; simp)
 apply(drule meta_mp)
  apply(simp add: seq_block_tl'[where xs="_ # _"])
 apply(assumption)
apply(drule_tac x="[]" in meta_spec; simp)
apply(subgoal_tac "seq_block ((a, b) # i)")
apply(case_tac b; simp; rename_tac x; case_tac x; simp add: block_pt_def seq_block_tl seq_block_sumC)
apply(simp add: seq_block_tl'[where xs="_ # _"])
done

lemma reverse_basic_blocks_add: 
 "blocks_pos_insts (aux_basic_block (add_address i) []) = (add_address i)"
apply(subst rev_basic_blocks_add)
 apply(simp add: seq_block_add_address add_address_def)
apply(simp)
done

(* Draft Jump *)

lemma blocks_vert_rebuild_one:
"distinct (map fst zs) \<Longrightarrow>
(n,i) \<in> set zs \<Longrightarrow>
 blocks_vertices
  \<lparr>blocks_indexes = (map fst zs), blocks_list = map_of zs\<rparr>
  [n] = [(n,i)]"
by simp

lemma blocks_vert_rebuild_subset:
"distinct (map fst zs) \<Longrightarrow>
 set xs \<subseteq> set zs \<Longrightarrow>
 blocks_vertices
  \<lparr>blocks_indexes = (map fst zs), blocks_list = map_of zs\<rparr>
  (map fst xs) = xs"
apply(induction xs; simp)
apply(erule conjE)
apply(split option.split; rule conjI; simp)
 apply(rule_tac x="v_insts a" in exI; rule_tac x="v_ty a" in exI)
 apply(clarsimp)
apply(clarsimp)
apply(simp add: distinct_map inj_on_def)
apply(fastforce)
done

lemma blocks_vert_rebuild:
"distinct (map fst zs) \<Longrightarrow>
 blocks_vertices
  \<lparr>blocks_indexes = (map fst zs), blocks_list = map_of zs\<rparr>
  (map fst zs) = zs"
by(simp add: blocks_vert_rebuild_subset)

lemma add_address_greater:
"(n,m) \<in> set (add_address' xs k) \<Longrightarrow>
n \<ge> k"
apply(induction xs arbitrary: k)
 apply(simp)
apply(simp; erule disjE)
 apply(simp)
apply(drule_tac x="k + inst_size a" in meta_spec)
apply(simp add: inst_size_pos)
apply(subgoal_tac "k + inst_size a \<ge> k")
 apply(simp)
apply(simp add: inst_size_pos Orderings.order_class.order.strict_implies_order)
done

lemma remdups_id_add_address:
"remdups (add_address' xs n) = (add_address' xs n)"
apply(induction xs arbitrary: n)
 apply(simp)
apply(clarsimp)
apply(drule add_address_greater; simp)
apply(drule linorder_class.leD; simp add: inst_size_pos)
done

lemma distinct_add_address:
"distinct (map fst (add_address' xs n))"
apply(simp add: distinct_map)
apply(rule conjI)
 apply(insert remdups_id_add_address[where xs=xs and n=n]; simp)
apply(clarsimp simp add: inj_on_def)
apply(induction xs arbitrary: n)
 apply(simp)
apply(simp)
apply(erule disjE; erule disjE)
   apply(fastforce)
  apply(drule add_address_greater; simp)
  apply(drule linorder_class.leD; simp add: inst_size_pos)
 apply(drule add_address_greater; simp)
 apply(drule linorder_class.leD; simp add: inst_size_pos)
apply(fastforce)
done

lemma hd_inst_in_aux_bb:
"(n,(n,x)#zs,t) \<in> set (aux_basic_block xs ys) \<Longrightarrow>
(n, x) \<in> set ys \<or> (n, x) \<in> set xs"
apply(induction xs arbitrary: ys)
 apply(case_tac ys; clarsimp simp add: aux_basic_block.simps)
apply(simp add: aux_basic_block.simps Let_def)
apply(case_tac "reg_inst (snd a) \<and> (snd a) \<noteq> Pc JUMPDEST")
 apply(simp split: reg_inst_splits; fastforce)
apply(case_tac "snd a = Pc JUMPDEST")
 apply(simp split: reg_inst_splits if_splits)
  apply(fastforce)
 apply(erule disjE)
  apply(drule conjunct2; rule disjI1; clarsimp)
 apply(fastforce)
apply(drule meta_spec[where x="[]"])
apply(simp split: reg_inst_splits if_splits)
    apply(erule disjE; clarsimp; case_tac ys; clarsimp)+
done

lemma inst_size_list_pos:
"inst_size_list xs \<ge> 0"
apply(induction xs; simp)
apply(insert inst_size_pos)
apply(drule_tac x="snd a" in meta_spec)
apply(fastforce)
done

lemma seq_block_smaller:
"seq_block (a # list @ (m, j) # xs) \<Longrightarrow>
fst a < m "
 apply(case_tac a; clarsimp)
 apply(drule seq_block_sumC)
 apply(drule sym[where s="_+_"]; simp)
 apply(subgoal_tac "inst_size b + inst_size_list list \<ge> inst_size b")
  apply(drule Orderings.order_class.dual_order.strict_trans1[where c=0])
   apply(simp add: inst_size_pos)
  apply(assumption)
 apply(simp add: inst_size_list_pos)
done

lemma seq_block_smaller_all:
"seq_block (a # list @ (m, j) # xs) \<Longrightarrow>
fst a < m \<and> (\<forall>x \<in> set xs. fst a < fst x)"
apply(rule conjI)
 apply(simp add: seq_block_smaller)
apply(clarsimp)
apply(subgoal_tac "\<exists>ys zs. xs = ys @ (aa, b) # zs")
 apply(clarify)
 apply(simp add: seq_block_smaller[where list="list @ (m,j)#_"])
apply(thin_tac "seq_block _")
apply(induction xs; simp)
apply(erule disjE)
 apply(fastforce)
apply(drule_tac x="aa" and y=b in meta_spec2; clarsimp)
apply(rule_tac x="(a, b) # ys" in exI; simp)
done

lemma seq_block_smaller_all':
"seq_block (a # xs) \<Longrightarrow>
(\<forall>x \<in> set xs. fst a < fst x)"
apply(clarsimp)
apply(subgoal_tac "\<exists>ys zs. xs = ys @ (aa, b) # zs")
 apply(clarify)
 apply(simp add: seq_block_smaller)
apply(thin_tac "seq_block _")
apply(induction xs; simp)
apply(erule disjE)
 apply(fastforce)
apply(drule_tac x="aa" and y=b in meta_spec2; clarsimp)
apply(rule_tac x="(a, b) # ys" in exI; simp)
done

lemma ind_in_para_aux_bb:
"(n,js,t) \<in> set (aux_basic_block xs ys) \<Longrightarrow>
\<exists>x\<in>set(ys@xs). fst x = n"
apply(induction xs arbitrary: ys)
 apply(case_tac ys; simp add: aux_basic_block.simps)
apply(simp add: aux_basic_block.simps Let_def)
apply(clarsimp; rename_tac nx ni xs ys)
apply(case_tac "reg_inst ni \<and> ni \<noteq> Pc JUMPDEST")
 apply(simp split: reg_inst_splits; fastforce)
apply(case_tac "ni = Pc JUMPDEST")
 apply(simp split: reg_inst_splits; case_tac ys; simp add: block_pt_def)
  apply(fastforce)
 apply(drule_tac x="[(nx, Pc JUMPDEST)]" in meta_spec; simp)
apply(drule meta_spec[where x="[]"])
apply(case_tac ys; simp add: block_pt_def split: reg_inst_splits)
apply(erule disjE; simp)+
done

lemma remdups_id_aux_bb:
"distinct (map fst (ys@xs)) \<Longrightarrow>
remdups (aux_basic_block xs ys) = (aux_basic_block xs ys)"
apply(induction xs arbitrary: ys)
 apply(case_tac ys; simp add: aux_basic_block.simps)
apply(case_tac ys; simp add: aux_basic_block.simps Let_def)
 apply(erule conjE)+
 apply(case_tac "reg_inst (snd a)")
  apply(simp split: reg_inst_splits; fastforce)
 apply(cut_tac x="fst a" and xys=xs in map_of_eq_None_iff, drule sym, simp)
 apply(case_tac "snd a"; simp split: reg_inst_splits;
			rename_tac x; case_tac x; simp add: block_pt_def; rule notI)
      apply(drule_tac ys="[]" and xs="xs" and n="fst a" and js="[]" in ind_in_para_aux_bb; clarsimp)+
     apply(drule_tac ys="[]" and xs="xs" and n="fst a" and js="[a]" in ind_in_para_aux_bb; clarsimp)+
apply(erule conjE)+
apply(clarsimp)
apply(rename_tac n i xs ny iy yss)
apply(case_tac "reg_inst i \<and> i \<noteq> Pc JUMPDEST")
 apply(simp split: reg_inst_splits; fastforce)
apply(case_tac "i = Pc JUMPDEST")
 apply(clarsimp split: reg_inst_splits if_splits)
 apply(simp add: block_pt_def)
 apply(cut_tac x="ny" and xys=xs in map_of_eq_None_iff, drule sym, simp)
 apply(drule ind_in_para_aux_bb; clarsimp)
apply(cut_tac x="ny" and xys=xs in map_of_eq_None_iff, drule sym, simp)
apply(case_tac i; simp split: reg_inst_splits;
			rename_tac x; case_tac x; simp add: block_pt_def; rule notI)
     apply(drule_tac ys="[]" and xs="xs" and n="ny" and js="(ny, iy) # yss" in ind_in_para_aux_bb; clarsimp)+
   apply(cut_tac ys="[]" and xs="xs" and n="ny" and js="(ny, iy) # yss @ [(n, i)]" and t=No in ind_in_para_aux_bb; clarsimp)+
done

lemma distinct_fst_aux_bb:
"distinct (map fst (ys@xs)) \<Longrightarrow>
 seq_block (ys@xs) \<Longrightarrow>
 distinct (map v_ind (aux_basic_block xs ys))"
apply(subst distinct_map)
apply(rule conjI)
 apply(insert remdups_id_aux_bb[where xs=xs and ys=ys]; simp)
apply(clarsimp simp add: inj_on_def)
apply(induction xs arbitrary: ys)
 apply(case_tac ys; simp add: aux_basic_block.simps)
apply(clarsimp)
apply(rename_tac m i xs is1 t1 n is2 t2 ys)
apply(simp add: aux_basic_block.simps Let_def)
apply(case_tac "reg_inst i \<and> i \<noteq> Pc JUMPDEST")
 apply(drule_tac x=is1 and y=t1 in meta_spec2; drule_tac x=n in meta_spec)
 apply(drule_tac x=is2 and y=t2 in meta_spec2; drule_tac x="ys @ [(m, i)]" in meta_spec)
 apply(simp split: reg_inst_splits)
apply(case_tac "i = Pc JUMPDEST")
 apply(clarsimp split: reg_inst_splits if_splits)
  apply(drule_tac x=is1 and y=t1 in meta_spec2; drule_tac x=n in meta_spec)
  apply(drule_tac x=is2 and y=t2 in meta_spec2; drule_tac x="[(m, Pc JUMPDEST)]" in meta_spec)
  apply(simp)
 apply(erule disjE; erule disjE)
		apply(simp)
	 apply(erule conjE)+
	 apply(case_tac ys; simp add: block_pt_def)
	 apply(drule ind_in_para_aux_bb; drule seq_block_smaller_all)
	 apply(fastforce)
	apply(erule conjE)+
	apply(case_tac ys; simp add: block_pt_def)
	apply(drule ind_in_para_aux_bb; drule seq_block_smaller_all)
	apply(fastforce)
 apply(drule_tac x=is1 and y=t1 in meta_spec2; drule_tac x=n in meta_spec)
 apply(drule_tac x=is2 and y=t2 in meta_spec2; drule_tac x="[(m, Pc JUMPDEST)]" in meta_spec)
 apply(simp add: seq_block_tl')
apply(subgoal_tac "\<exists>t zs. (n, is1, t1) \<in> set ((block_pt ys (m, i), ys @zs, t) #
                 aux_basic_block xs []) \<and>
								 (n, is2, t2) \<in> set ((block_pt ys (m, i), ys@zs, t) #
                 aux_basic_block xs [])")
  defer
  apply(clarsimp split: reg_inst_splits; fastforce)
apply(thin_tac "(_,_,_)\<in>set (_)")
apply(thin_tac "(_,_,_)\<in>set (_)")
apply(clarsimp)
 apply(erule disjE; erule disjE)
		apply(clarsimp)
	 apply(erule conjE)+
	 apply(case_tac ys; simp add: block_pt_def)
	  apply(drule ind_in_para_aux_bb; drule seq_block_smaller_all')
	  apply(fastforce)
	 apply(drule ind_in_para_aux_bb; drule seq_block_smaller_all'; clarsimp)
	 apply(subgoal_tac "\<forall>x\<in>set xs. a < fst x")
		apply(fastforce)
	 apply(simp)
	apply(erule conjE)+
	apply(case_tac ys; simp add: block_pt_def)
	  apply(drule ind_in_para_aux_bb; drule seq_block_smaller_all')
	  apply(fastforce)
	 apply(drule ind_in_para_aux_bb; drule seq_block_smaller_all'; clarsimp)
	 apply(subgoal_tac "\<forall>x\<in>set xs. a < fst x")
		apply(fastforce)
	 apply(simp)
 apply(drule_tac x=is1 and y=t1 in meta_spec2; drule_tac x=n in meta_spec)
 apply(drule_tac x=is2 and y=t2 in meta_spec2; drule_tac x="[]" in meta_spec; simp)
 apply(simp add: seq_block_tl'[where xs="_@[_]"])
done

lemma re_build_bb:
"blocks_vertices (build_blocks xs) (blocks_indexes (build_blocks xs)) = build_vertices xs"
apply(simp add: build_blocks_def Let_def extract_indexes_def)
apply(rule blocks_vert_rebuild)
apply(simp add: build_vertices_def add_address_def)
apply(rule distinct_fst_aux_bb)
 apply(simp add: distinct_add_address)
apply(simp add: seq_block_add_address)
done

lemma re_build_address:
"blocks_pos_insts (blocks_vertices (build_blocks xs) (blocks_indexes (build_blocks xs))) = add_address xs"
apply(simp add: re_build_bb)
apply(simp add: build_vertices_def reverse_basic_blocks_add)
done

lemma jump_i_ends_block:
"seq_block (ys@xs) \<Longrightarrow>
 (t=Jump \<and> i=JUMP) \<or> (t=Jumpi \<and> i=JUMPI) \<Longrightarrow>
 (n, insts, t) \<in> set (aux_basic_block xs ys) \<Longrightarrow>
 (n + inst_size_list insts, Pc i) \<in> set xs"
 apply(induction xs arbitrary: ys)
  apply(case_tac ys; simp add: aux_basic_block.simps)
 apply(clarsimp simp add: aux_basic_block.simps Let_def)
 apply(case_tac "reg_inst b \<and> b \<noteq> Pc JUMPDEST")
  apply(drule_tac x="ys @ [(a, b)]" in meta_spec)
  apply(simp split: reg_inst_splits)
 apply(case_tac "b=Pc JUMPDEST")
  apply(case_tac ys)
	 apply(simp; drule_tac x="[(a, b)]" in meta_spec; simp)
  apply(simp; drule_tac x="[(a, b)]" in meta_spec; simp add: seq_block_tl'[where xs="_#_"])
  apply(erule disjE; simp)
 apply(drule_tac x="[]" in meta_spec)
 apply(drule meta_mp)
  apply(subgoal_tac "seq_block ((a, b) # xs)")
	 apply(simp add: seq_block_tl)
  apply(simp add: seq_block_tl')
 apply(simp split: reg_inst_splits; erule disjE; simp)
  apply(erule disjE; simp)
  apply(case_tac ys; simp add: block_pt_def seq_block_sumC)
 apply(erule disjE; simp)
 apply(case_tac ys; simp add: block_pt_def seq_block_sumC)
done

lemma jumps_end_block:
"(t=Jump \<and> i=JUMP) \<or> (t=Jumpi \<and> i=JUMPI) \<Longrightarrow>
 blocks_list (build_blocks bytecode) n = Some (insts, t) \<Longrightarrow>
 program_content (program_from_blocks (build_blocks bytecode))
  (n + inst_size_list insts) =
 Some (Pc i)"
 apply(simp add: program_from_blocks_def blocks_content_def)
 apply(simp add: re_build_address)
 apply(simp add: build_blocks_def Let_def)
 apply(simp add: build_vertices_def)
 apply(insert map_of_eq_Some_iff[where xys="add_address bytecode" and x="n + inst_size_list insts"
 and y="Pc i"])
 apply(drule meta_mp)
  apply(simp add: add_address_def distinct_add_address)
 apply(simp add: add_address_def)
 apply(drule map_of_SomeD)
	apply(subst jump_i_ends_block[where ys="[]"]; simp)
  apply(simp add: seq_block_add_address)
done

(* Main theorem *)

lemma wf_build_blocks:
"fst (last (add_address bytecode)) < 2^256 \<Longrightarrow>
wf_blocks (build_blocks bytecode)"
 apply(simp add: wf_blocks_def)
 apply(clarsimp)
 apply(rule conjI)
  apply(clarsimp; rule conjI)
   apply(case_tac "\<not> blocks_list (build_blocks bytecode) n = None")
    apply(simp add: index_have_blocks)
   apply(simp)
  apply(simp add: build_blocks_def Let_def)
  apply(drule map_of_SomeD)
  apply(rule conjI)
    apply(cut_tac reg_bb[where insts=bytecode])
     apply(simp add: reg_vertices_def list_all_in)
  apply(rule conjI)
	 apply(simp add: build_vertices_def)
	 apply(drule in_aux_bb_intermediate, clarify)
	 apply(case_tac insts; clarsimp simp add: index_block_eq)
	apply(simp add: build_vertices_def)
  apply(rule_tac ty=ty in sequential_basic_blocks[where ys="add_address bytecode" and bl="[]"])
       apply(simp add: seq_block_add_address add_address_def)
      apply(simp add: seq_block.simps)
     apply(clarsimp simp add: list_all_def add_address_def)
     apply(cut_tac x=a and y=b in bound_add_address'[where xs=bytecode and k=0]; simp)
    apply(simp)+
 apply(thin_tac "_ < _")
 apply(simp add: jumps_end_block)
 apply(rule conjI)
  apply(simp add: build_blocks_def Let_def build_vertices_def)
  apply(rule impI)
  apply(drule map_of_SomeD)
  apply(drule in_aux_bb_intermediate, clarify)
  apply(drule non_empty_block_next; simp)
 apply(rule impI)
 apply(simp add: build_blocks_def Let_def build_vertices_def)
 apply(drule map_of_SomeD)
 apply(drule block_no; simp add: reg_block_def)
done

end
