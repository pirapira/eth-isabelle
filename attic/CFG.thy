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
type_synonym edge = "int * (int option)"
type_synonym edges = "int \<Rightarrow> edge option"

type_synonym stack_value = "w256 option"

type_synonym edges_status = "string option"
typ "stack_value list + string"
type_synonym edges_return = "edges * edges_status"

record cfg =
cfg_indexes :: "int list"
cfg_blocks :: "int \<Rightarrow> vert option"
cfg_edges :: "edges"
cfg_status :: "edges_status"

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

definition not_complete :: "edges_return \<Rightarrow> char list \<Rightarrow> edges_return " where
  "not_complete res debug= (fst res, Some debug)"

definition update_edges :: "edges_return \<Rightarrow> int \<Rightarrow> edge \<Rightarrow> edges_return" where
"update_edges e i v = ((fst e)(i:= Some v), snd e)"

definition concat_map :: "int \<Rightarrow> edge \<Rightarrow> edges_return \<Rightarrow> edges_return \<Rightarrow> edges_return" where
 "concat_map n v m1 m2 = 
  ((fst m1 ++ fst m2)(n:= Some v),(case (snd m1, snd m2) of
    (Some str1, _) \<Rightarrow> Some str1
   |(_, Some str1) \<Rightarrow> Some str1
   |_ \<Rightarrow> None
))"

definition extract_indexes :: "vertices \<Rightarrow> int list" where
"extract_indexes xs = map v_ind xs"

fun print_edges_aux ::"int list \<Rightarrow> edges \<Rightarrow> (int * edge) list" where
"print_edges_aux [] e = []"
| "print_edges_aux (n#q) e = (case e n of None \<Rightarrow> print_edges_aux q e | Some i \<Rightarrow> (n,i) # (print_edges_aux q e))"

abbreviation print_edges :: "vertices \<Rightarrow> edges_return \<Rightarrow> (int * edge) list" where
"print_edges v e == print_edges_aux (extract_indexes v) (fst e)"

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

(* Main functions *)

(* The execution of a basic block must be sequential. *)
(* We remove JUMP and JUMPI instructions and cut after them or a stopping instruction *)
(* and before a Jump destination. *)
fun aux_basic_block :: "inst list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> pos_inst list \<Rightarrow> vertices" where
 "aux_basic_block [] pointer block_pt block = (if block = [] then [] else
    [(block_pt, rev block, No)])"
|"aux_basic_block ((i)#tl1) pointer block_pt block =
  (let newpointer = pointer + (inst_size i) in
  (case i of
    Pc JUMPDEST \<Rightarrow> (if block = [] then (aux_basic_block tl1 newpointer pointer [(pointer,i)])
    else (block_pt, rev block, Next) # (aux_basic_block tl1 newpointer pointer [(pointer,i)]))
  | Pc JUMP \<Rightarrow>(block_pt, rev block, Jump) # ( aux_basic_block tl1 newpointer newpointer [])
  | Pc JUMPI \<Rightarrow>(block_pt, rev block, Jumpi) # ( aux_basic_block tl1 newpointer newpointer [])
  | Misc RETURN \<Rightarrow>(block_pt, rev ((pointer,i)#block), No) # ( aux_basic_block tl1 newpointer newpointer [])
  | Misc SUICIDE \<Rightarrow>(block_pt, rev ((pointer,i)#block), No) # ( aux_basic_block tl1 newpointer newpointer [])
  | Misc STOP \<Rightarrow>(block_pt, rev ((pointer,i)#block), No) # ( aux_basic_block tl1 newpointer newpointer [])
  | _ \<Rightarrow> aux_basic_block tl1 newpointer block_pt ((pointer,i)#block)))"

definition build_basic_blocks :: "inst list \<Rightarrow> vertices" where
"build_basic_blocks prog == aux_basic_block prog 0 0 []"

(* Read a block and simulate stack operations - only store push values *)
fun edge_one_block :: "tblock \<Rightarrow> pos_inst list \<Rightarrow> stack_value list \<Rightarrow> (stack_value list + string)" where
  "edge_one_block Next [] st = Inl st"
| "edge_one_block No [] st = Inl st"
| "edge_one_block Jump [] [] = Inr ''JUMP : Empty stack''"
| "edge_one_block Jump [] (a#st) = (case a of
      Some add \<Rightarrow> Inl (a#st)
    | None \<Rightarrow> Inr ''JUMP : Data on top of the stack'')"
| "edge_one_block Jumpi [] [] = Inr ''JUMPI : Empty stack''"
| "edge_one_block Jumpi [] [a] = Inr ''JUMPI : Just 1 elet on stack''"
| "edge_one_block Jumpi [] (a#b#st) = (case a of
      Some add \<Rightarrow> Inl (a#b#st)
    | None \<Rightarrow> Inr ''JUMPI : Data on top of the stack'')"
| "edge_one_block t ((_,(Stack (PUSH_N data)))#bl) st = 
    edge_one_block t bl ((Some (Word.word_rcat (constant_mark data)))#st)"
| "edge_one_block t ((_,Swap i)#bl) st = (case list_swap (unat i + 1) st of
    None \<Rightarrow> Inr ''Swap : stack too small''
  | Some st \<Rightarrow> edge_one_block t bl st)"
| "edge_one_block t ((_,Dup i)#bl) st = ( (case index st (unat i) of
    None => Inr ''Dup : stack too small''
  | Some duplicated => edge_one_block t bl (duplicated # st)))"
| "edge_one_block t ((_,i)#bl) st = (let st_nb= (inst_stack_numbers i) in
    (if (nat (fst st_nb))>length st
     then Inr ''Stack too small''
     else edge_one_block t bl ((replicate (nat (snd st_nb)) None)@(drop (nat (fst st_nb)) st))))"

(* Compute the edges of a block *)
fun edges_blocks :: "int list \<Rightarrow> int \<Rightarrow> stack_value list \<Rightarrow> vertices \<Rightarrow> edges_return " where
"edges_blocks to_do n st vertices = 
  (if n \<in> set to_do then
   (case find (find_block n) vertices of
      None \<Rightarrow> (Map.empty, Some ''Block not found'')
    | Some bl \<Rightarrow> (let new_to_do = removeAll n to_do in
      (case edge_one_block (v_ty bl) (v_insts bl) st of
        Inr str \<Rightarrow> (Map.empty, Some str)
       |Inl st \<Rightarrow> (case v_ty bl of
          No \<Rightarrow> (Map.empty, None)
        | Next \<Rightarrow> let m = next_i vertices n in
           update_edges (edges_blocks new_to_do m st vertices) n (m, None)
        | Jump \<Rightarrow> (case st of 
            (Some a)#sta \<Rightarrow> 
            (if good_dest (uint a) vertices
            then update_edges (edges_blocks new_to_do (uint a) sta vertices) n (uint a, None)
            else (Map.empty, Some ''Bad destination for JUMP''))
            |_ \<Rightarrow> (Map.empty, Some ''Bad stack for JUMP''))
        | Jumpi \<Rightarrow> (case st of
            (Some a)#b#sta \<Rightarrow> (let m = next_i vertices n in
              (if good_dest (uint a) vertices
              then concat_map n ((uint a), Some m) (edges_blocks new_to_do m sta vertices) (edges_blocks new_to_do (uint a) sta vertices)
              else (fst (update_edges (edges_blocks new_to_do m sta vertices) n ((uint a), Some m)), Some ''Bad destination for JUMPI'')))
            | _ \<Rightarrow> (Map.empty, Some ''Bad stack for JUMPI''))
  ))))
  else (Map.empty, None))"

definition build_cfg :: "inst list \<Rightarrow> cfg" where
"build_cfg prog = (let blocks = build_basic_blocks prog in
(let ind = (extract_indexes blocks) in
(let edges = edges_blocks ind 0 [] blocks in
(|cfg_indexes = ind,
  cfg_blocks = map_of blocks,
  cfg_edges = fst edges,
  cfg_status = snd edges |)
)))"

(* Verification *)

(* Check that we can rebuild the initial list of instructions from basic blocks *)
fun reconstruct_bytecode :: "vertices \<Rightarrow> inst list" where
 "reconstruct_bytecode [] = []"
| "reconstruct_bytecode ((n,b,Jump)#q) = (map snd b)@[Pc JUMP] @ (reconstruct_bytecode q)"
| "reconstruct_bytecode ((n,b,Jumpi)#q) = (map snd b)@[Pc JUMPI] @ (reconstruct_bytecode q)"
| "reconstruct_bytecode ((n,b,_)#q) = (map snd b) @ (reconstruct_bytecode q)"

lemma rev_basic_blocks: "reconstruct_bytecode (aux_basic_block i p bp b) = (map snd (rev b))@i"
apply(induction i arbitrary: p bp b)
apply(auto simp: Let_def split: inst.split misc_inst.split pc_inst.split)
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

fun seq_block :: "pos_inst list \<Rightarrow> bool" where 
"seq_block [] = True"
| "seq_block [x] = True"
| "seq_block (x#y#xs) = (fst y = fst x + inst_size (snd x) \<and> seq_block (y#xs))"

definition last_no::"pos_inst list \<Rightarrow> bool" where
"last_no insts == snd (last insts) \<in> {Misc STOP, Misc RETURN, Misc SUICIDE}"

definition wf_cfg:: "cfg \<Rightarrow> bool" where
"wf_cfg c == cfg_status c = None \<longrightarrow>
(\<forall>n insts ty m i j.
(cfg_blocks c n = Some (insts, ty) \<longrightarrow>
	n \<in> set (cfg_indexes c) \<and> reg_vertex (n, insts, ty) \<and>
  insts \<noteq> [] \<and> (fst (hd insts) = n) \<and> seq_block insts \<and>
  0 < n \<and> n < 2 ^ 256) \<and>
(cfg_blocks c n = Some (insts, Next) \<longrightarrow>
	cfg_edges c n = Some (m, None) \<longrightarrow>
	(m = n + inst_size_list insts)) \<and>
(cfg_blocks c n = Some (insts, Jump) \<longrightarrow>
	i = n + inst_size_list insts \<longrightarrow>
	cfg_edges c n = Some (m, None) \<longrightarrow>
	(program_content (program_from_cfg c) m = Some (Pc JUMPDEST) \<and>
	 program_content (program_from_cfg c) i = Some (Pc JUMP))) \<and>
(cfg_blocks c n = Some (insts, Jumpi) \<longrightarrow>
	i = n + inst_size_list insts \<longrightarrow>
	cfg_edges c n = Some (m, Some j) \<longrightarrow>
	(program_content (program_from_cfg c) m = Some (Pc JUMPDEST) \<and>
	 program_content (program_from_cfg c) i = Some (Pc JUMPI) \<and>
	 j = i + 1)) \<and>
(cfg_blocks c n = Some (insts, No) \<longrightarrow>
	(cfg_edges c n = None \<and>
   last_no insts))
)"

end