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

theory "CFG"

imports "../lem/Evm"

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

record cfg =
cfg_indexes :: "int list"
cfg_blocks :: "int \<Rightarrow> vert option"

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

definition block_pt :: "pos_inst list \<Rightarrow> int \<Rightarrow> int" where
 "block_pt bl pt = (case bl of
   [] \<Rightarrow> pt
  | _ \<Rightarrow> fst (hd bl))"

(* Main functions *)

(* The execution of a basic block must be sequential. *)
(* We remove JUMP and JUMPI instructions and cut after them or a stopping instruction *)
(* and before a Jump destination. *)
fun aux_basic_block :: "inst list \<Rightarrow> int \<Rightarrow> pos_inst list \<Rightarrow> vertices" where
 "aux_basic_block [] pointer block = (if block = [] then [] else
    [(block_pt (rev block) pointer, rev block, No)])"
|"aux_basic_block ((i)#tl1) pointer block =
  (let newpointer = pointer + (inst_size i) in
	(let bl = rev block in
	(let bl_pt = block_pt bl pointer in
  (case i of
    Pc JUMPDEST \<Rightarrow> (if block = [] then (aux_basic_block tl1 newpointer [(pointer,i)])
    else (bl_pt, bl, Next) # (aux_basic_block tl1 newpointer [(pointer,i)]))
  | Pc JUMP \<Rightarrow>(bl_pt, bl, Jump) # ( aux_basic_block tl1 newpointer [])
  | Pc JUMPI \<Rightarrow>(bl_pt, bl, Jumpi) # ( aux_basic_block tl1 newpointer [])
  | Misc RETURN \<Rightarrow>(bl_pt, bl @ [(pointer,i)], No) # ( aux_basic_block tl1 newpointer [])
  | Misc SUICIDE \<Rightarrow>(bl_pt, bl @ [(pointer,i)], No) # ( aux_basic_block tl1 newpointer [])
  | Misc STOP \<Rightarrow>(bl_pt, bl @ [(pointer,i)], No) # ( aux_basic_block tl1 newpointer [])
  | _ \<Rightarrow> aux_basic_block tl1 newpointer ((pointer,i)#block)))))"
declare aux_basic_block.simps[simp del]

definition build_basic_blocks :: "inst list \<Rightarrow> vertices" where
"build_basic_blocks prog == aux_basic_block prog 0 []"

definition build_cfg :: "inst list \<Rightarrow> cfg" where
"build_cfg prog = (let blocks = build_basic_blocks prog in
(let ind = (extract_indexes blocks) in
(|cfg_indexes = ind,
  cfg_blocks = map_of blocks|)
))"

(* Verification *)

(* Check that we can rebuild the initial list of instructions from basic blocks *)
fun reconstruct_bytecode :: "vertices \<Rightarrow> inst list" where
 "reconstruct_bytecode [] = []"
| "reconstruct_bytecode ((n,b,Jump)#q) = (map snd b)@[Pc JUMP] @ (reconstruct_bytecode q)"
| "reconstruct_bytecode ((n,b,Jumpi)#q) = (map snd b)@[Pc JUMPI] @ (reconstruct_bytecode q)"
| "reconstruct_bytecode ((n,b,_)#q) = (map snd b) @ (reconstruct_bytecode q)"

lemma rev_basic_blocks: "reconstruct_bytecode (aux_basic_block i p b) = (map snd (rev b))@i"
apply(induction i arbitrary: p b)
apply(auto simp: Let_def aux_basic_block.simps split: inst.split misc_inst.split pc_inst.split)
done

theorem reverse_basic_blocks: "reconstruct_bytecode (build_basic_blocks i) = i"
apply(simp add: rev_basic_blocks build_basic_blocks_def)
done

(* Define a 'program' from a CFG *)

fun cfg_insts_aux :: "cfg \<Rightarrow> int list \<Rightarrow> pos_inst list" where
  "cfg_insts_aux c [] = []"
| "cfg_insts_aux c (x#xs) = (case cfg_blocks c x of
    None \<Rightarrow> cfg_insts_aux c xs
  | Some (b,_) \<Rightarrow> b @ (cfg_insts_aux c xs))"

definition cfg_insts :: "cfg \<Rightarrow> pos_inst set" where
"cfg_insts c = set (cfg_insts_aux c (cfg_indexes c))"

fun inst_size_list::"pos_inst list \<Rightarrow> int" where
"inst_size_list [] = 0"
| "inst_size_list (x#xs) = inst_size (snd x) + inst_size_list xs"

fun cfg_pos_insts :: "vert list \<Rightarrow> pos_inst list" where
 "cfg_pos_insts [] = []"
| "cfg_pos_insts ((b,Jump)#q) = (case last b of
  (n,i) \<Rightarrow> b@[(n + inst_size i, Pc JUMP)] @ (cfg_pos_insts q))"
| "cfg_pos_insts ((b,Jumpi)#q) = (case last b of
  (n,i) \<Rightarrow> b@[(n + inst_size i, Pc JUMPI)] @ (cfg_pos_insts q))"
| "cfg_pos_insts ((b,_)#q) = b@ (cfg_pos_insts q)"

fun cfg_vertices:: "cfg \<Rightarrow> int list \<Rightarrow> vert list" where
"cfg_vertices c [] = []"
| "cfg_vertices c (x#xs) = (case cfg_blocks c x of
  None \<Rightarrow> cfg_vertices c xs
  | Some b \<Rightarrow> b # (cfg_vertices c xs))"

definition cfg_content ::"cfg \<Rightarrow> int \<Rightarrow> inst option " where
"cfg_content c i = (case find (\<lambda>u. fst u = i) (cfg_pos_insts (cfg_vertices c (cfg_indexes c))) of
  None \<Rightarrow> None
| Some u \<Rightarrow> Some (snd u))"

definition cfg_length :: "cfg \<Rightarrow> int " where
"cfg_length c =
  (case cfg_blocks c (last (cfg_indexes c)) of
    None \<Rightarrow> 0 (*Should not happen*)
  | Some (i,Jump) \<Rightarrow> fst (last i) +  inst_size (snd (last i))
  | Some (i,Jumpi) \<Rightarrow> fst (last i) + inst_size (snd (last i))
  | Some (i,_) \<Rightarrow> fst (last i))"

definition program_from_cfg:: "cfg \<Rightarrow> program" where
"program_from_cfg c = ( (|
  program_content = cfg_content c,
  program_length = cfg_length c,
  program_annotation = (\<lambda> _ .  [])
|) )"

(* Define how CFGs should be for the program logic to be sound *)

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

definition wf_cfg:: "cfg \<Rightarrow> bool" where
"wf_cfg c == 
(\<forall>n insts ty.
(cfg_blocks c n = Some (insts, ty) \<longrightarrow>
	n \<in> set (cfg_indexes c) \<and> reg_vertex (n, insts, ty) \<and>
  (insts \<noteq> [] \<longrightarrow> (fst (hd insts) = n)) \<and> seq_block insts \<and>
  0 < n \<and> n < 2 ^ 256) \<and>
(cfg_blocks c n = Some (insts, Next) \<longrightarrow>
	 insts \<noteq> []) \<and>
(cfg_blocks c n = Some (insts, Jump) \<longrightarrow>
	program_content (program_from_cfg c) (n + inst_size_list insts) = Some (Pc JUMP)) \<and>
(cfg_blocks c n = Some (insts, Jumpi) \<longrightarrow>
	program_content (program_from_cfg c) (n + inst_size_list insts) = Some (Pc JUMPI)) \<and>
(cfg_blocks c n = Some (insts, No) \<longrightarrow>
	 insts \<noteq> [] \<and> last_no insts)
)"

(* Proof that we build well formed CFGs *)

lemma index_have_blocks:
"c = build_cfg bytecode \<Longrightarrow>
 \<not> cfg_blocks c n = None \<Longrightarrow>
 n \<in> set (cfg_indexes c)"
by(simp add: Let_def build_cfg_def extract_indexes_def map_of_eq_None_iff)

lemma index_block_eq:
"(n, (j,i)#b, t)#xs = aux_basic_block insts m block \<Longrightarrow>
j=n"
apply(induction insts arbitrary: m block n j i t xs b)
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

lemma aux_rev_cond:
"\<forall>i j. (\<exists>zs. bl = (j, i) # zs) \<longrightarrow> m = j + inst_size i \<Longrightarrow>
    bl \<noteq> [] \<longrightarrow> (\<forall>i j. last (rev bl) = (j, i) \<longrightarrow> m = j + inst_size i)"
apply(clarsimp)
apply(drule_tac x=i and y=j in spec2)
apply(simp add: last_rev)
apply(case_tac bl; simp)
done

lemma seq_blocks:
"seq_block (rev bl) \<Longrightarrow>
\<forall>i j zs. bl = (j,i)#zs \<longrightarrow> m = j + inst_size i \<Longrightarrow>
(n, insts, ty) # xs = aux_basic_block ys m bl \<Longrightarrow>
seq_block insts"
apply(induction ys arbitrary: m bl)
 apply(simp add: aux_basic_block.simps block_pt_def split:if_splits list.splits)
apply(drule subst[OF aux_basic_block.simps(2), where P="\<lambda>u. _ = u"])
apply(simp add: Let_def)
apply(case_tac "a \<in> {Misc STOP, Misc RETURN, Misc SUICIDE}")
defer
 apply(drule_tac x="m + inst_size a" and y="(m,a)#bl" in meta_spec2)
 apply(drule meta_mp)
  apply(simp, subst seq_block_compose; simp add: aux_rev_cond)
 apply(simp split: inst.splits)
 apply(simp split: pc_inst.splits if_splits)
 apply(simp split: misc_inst.splits)
apply(thin_tac "\<And>ma bla. _ bla \<Longrightarrow> _ bla ma \<Longrightarrow> _ bla ma \<Longrightarrow> seq_block _")
apply(simp split: inst.splits misc_inst.splits; subst seq_block_compose; simp)
apply(clarsimp simp add: last_rev; drule_tac x=i and y=j in spec2; case_tac bl; simp)+
done

lemma in_aux_seq_block:
"(n, b, t) \<in> set (aux_basic_block insts k block) \<Longrightarrow>
seq_block (rev block) \<Longrightarrow>
(\<forall>i j zs. block = (j,i)#zs \<longrightarrow> k = j + inst_size i) \<Longrightarrow>
\<exists>ys m bl xs. (n, b, t)#xs = aux_basic_block ys m bl \<and> seq_block (rev bl) \<and>
(\<forall>i j zs. bl = (j,i)#zs \<longrightarrow> m = j + inst_size i)"
apply(induction insts arbitrary: k block)
 apply(rule_tac x="[]" in exI)
 apply(simp add: aux_basic_block.simps split: if_splits)
 apply(rule_tac x=k in exI, rule_tac x=block in exI, simp)
apply(subgoal_tac "(n, b, t) \<in> set
			(aux_basic_block (a # insts) k block)")
apply(drule subst[OF aux_basic_block.simps(2)])
apply(simp add: Let_def)
apply(case_tac "reg_inst a \<and> a \<noteq> Pc JUMPDEST")
  apply(drule_tac x="k + inst_size a" and y="(k, a) # block" in meta_spec2)
  apply(drule meta_mp)
   apply(clarsimp split: inst.splits pc_inst.splits misc_inst.splits)
  apply(drule meta_mp; simp)
  apply(subst seq_block_compose; simp add: aux_rev_cond)
 apply(simp split: inst.splits pc_inst.splits)
     apply(erule disjE)
      apply(clarsimp)
      apply(rule_tac x="Pc JUMP # insts" in exI, rule_tac x="k" in exI, rule_tac x="block" in exI,
            simp add: aux_basic_block.simps Let_def)
     apply(drule_tac x="k + inst_size a" and y="[]" in meta_spec2)
     apply(drule meta_mp; simp add: seq_block.simps)
    apply(erule disjE)
     apply(clarsimp)
     apply(rule_tac x="Pc JUMPI # insts" in exI, rule_tac x="k" in exI, rule_tac x="block" in exI,
            simp add: aux_basic_block.simps Let_def)
    apply(drule_tac x="k + inst_size a" and y="[]" in meta_spec2)
    apply(drule meta_mp; simp add: seq_block.simps)
   apply(case_tac block; simp)
    apply(drule_tac x="k + inst_size (Pc JUMPDEST)" and y="[(k, Pc JUMPDEST)]" in meta_spec2)
    apply(drule meta_mp; simp; simp add: seq_block.simps)
   apply(erule disjE)
    apply(rule_tac x="Pc JUMPDEST # insts" in exI, rule_tac x="k" in exI, rule_tac x="block" in exI, 
            simp add: aux_basic_block.simps Let_def)
   apply(drule_tac x="k + inst_size (Pc JUMPDEST)" and y="[(k, Pc JUMPDEST)]" in meta_spec2)
   apply(drule meta_mp; simp; simp add: seq_block.simps)
  apply(subgoal_tac "(n, b, t)
       \<in> set ((block_pt (rev block) k, rev block @ [(k, a)], No) #
                 aux_basic_block insts (k + inst_size a) [])")
   apply(thin_tac "(n,b,t) \<in> set (case _ of STOP \<Rightarrow> _ | RETURN \<Rightarrow> _ | SUICIDE \<Rightarrow> _ |_ \<Rightarrow> _)")
   apply(simp; erule disjE)
    apply(rule_tac x="Misc x13 # insts" in exI, rule_tac x="k" in exI, rule_tac x="block" in exI)
    apply(subst aux_basic_block.simps; simp add: Let_def split: misc_inst.splits; fastforce)
   apply(drule_tac x="k + inst_size a" and y="[]" in meta_spec2)
   apply(drule meta_mp; simp add: seq_block.simps)
  apply(simp split: misc_inst.splits)
 apply(assumption)
done

lemma in_aux_bb_intermediate:
"(n, b, t) \<in> set (aux_basic_block insts k block) \<Longrightarrow>
\<exists>ys m bl xs. (n, b, t)#xs = aux_basic_block ys m bl"
apply(induction insts arbitrary: k block)
 apply(rule_tac x="[]" in exI)
 apply(simp add: aux_basic_block.simps split: if_splits)
 apply(rule_tac x=k in exI, rule_tac x=block in exI, simp)
apply(subgoal_tac "(n, b, t) \<in> set
			(aux_basic_block (a # insts) k block)")
 apply(drule subst[OF aux_basic_block.simps(2)])
 apply(simp add: Let_def)
  apply(clarsimp split: inst.splits simp add: inst_size_def inst_code.simps)
  apply(simp split: pc_inst.splits if_splits add: inst_size_def inst_code.simps;
				erule disjE, rule_tac x="Pc x9 # insts" in exI, rule_tac x=k in exI, rule_tac x=block in exI,
				simp add: aux_basic_block.simps Let_def, fastforce)
 apply(simp split: misc_inst.splits if_splits add: inst_size_def inst_code.simps;
				erule disjE, rule_tac x="Misc x13 # insts" in exI, rule_tac x=k in exI, rule_tac x=block in exI,
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

lemma reg_block_rev:
"reg_block xs \<Longrightarrow> reg_block (rev xs)"
 apply(induction xs)
  apply(simp)
 apply(simp add: reg_block_def)
done

lemmas reg_simps =
reg_vertices_def reg_vertex_def reg_block_def

lemma reg_aux_bb:
"reg_block block \<Longrightarrow>
 reg_vertices (aux_basic_block insts pointer block)"
 apply(induction insts arbitrary: pointer  block)
  apply(simp add: reg_vertex_def reg_vertices_def reg_block_rev reg_block_butlast  aux_basic_block.simps)
 apply(simp add:Let_def aux_basic_block.simps)
 apply(simp split: inst.split pc_inst.split misc_inst.split)
 apply(simp add:reg_simps)
 apply(simp add: List.List.list.pred_map)
done

lemma reg_bb:
"reg_vertices (build_basic_blocks insts)"
 apply(simp add: build_basic_blocks_def)
 apply(rule reg_aux_bb)
 apply(simp add: reg_simps)
done

(* Main theorem *)

lemma wf_build_cfg:
"wf_cfg (build_cfg bytecode)"
 apply(simp add: wf_cfg_def)
 apply(clarsimp)
 apply(rule conjI)
  apply(clarsimp; rule conjI)
   apply(case_tac "\<not> cfg_blocks (build_cfg bytecode) n = None")
    apply(simp add: index_have_blocks)
   apply(simp)
  apply(rule conjI)
   apply(simp add: build_cfg_def Let_def)
   apply(drule map_of_SomeD)
    apply(cut_tac reg_bb[where insts=bytecode])
     apply(simp add: reg_vertices_def list_all_in)
  apply(rule conjI)
   apply(simp add: build_cfg_def Let_def; clarify)
   apply(drule map_of_SomeD)
	 apply(simp add: build_basic_blocks_def)
	 apply(drule in_aux_bb_intermediate, clarify)
	 apply(case_tac insts; clarsimp simp add: index_block_eq)
  apply(rule conjI)
   apply(simp add: build_cfg_def Let_def)
   apply(drule map_of_SomeD)
	 apply(simp add: build_basic_blocks_def)
   apply(drule in_aux_seq_block)
     apply(simp add: seq_block.simps)
    apply(simp split: list.splits)
   apply(clarsimp simp add: seq_blocks)
sorry

end
