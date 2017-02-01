theory ProgramList

imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl"

begin
  
(* Instead of map, make a list first *)
fun  program_list_of_lst  :: "inst list \<Rightarrow> inst list"  where 
 " program_list_of_lst [] = []"
|" program_list_of_lst (Stack (PUSH_N bytes) # rest) =
    [Stack (PUSH_N bytes)] @
    map(\<lambda>x. Unknown x) bytes @ 
   program_list_of_lst rest"
|" program_list_of_lst (i # rest) = i # program_list_of_lst rest" 

theorem program_list_append :
  "program_list_of_lst (a@b) =
   program_list_of_lst a @ program_list_of_lst b"
apply(induction a rule:program_list_of_lst.induct)
apply(auto)
done

definition map_tree_eq :: "(nat, inst) map \<Rightarrow> (int*inst) avl_tree \<Rightarrow> bool" where
"map_tree_eq m tree = (\<forall>x. x \<ge> 0 \<longrightarrow> m (nat x) = lookup tree x)"

lemma empty_eq : "map_tree_eq empty Leaf"
apply(auto simp:map_tree_eq_def)
done

(*
lemma wot_lst :
  "map_of (upd_list x y lst) x = Some y"
  by (simp add: map_of_ins_list)

lemma wot :
 "sorted1(inorder m) \<Longrightarrow>
  lookup (update x t (m::(int*inst) avl_tree)) =
  (lookup m)(x := Some t)"
  by (simp add: AVL_Map.map_update)
*)

lemma update_eq :
  "sorted1(inorder tree) \<Longrightarrow> n \<ge> 0 \<Longrightarrow> map_tree_eq m tree \<Longrightarrow>
   map_tree_eq (m(n:=Some t)) (update n t tree)"
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update)
  by (simp add: AVL_Map.map_update nat_eq_iff)


fun store_byte_list_in_map ::
  "nat (* initial position in the AVL *) \<Rightarrow> byte list (* the data *) \<Rightarrow>
   (nat,inst) map (* original AVL *) \<Rightarrow>
   (nat,inst) map (* result *)"
where
  "store_byte_list_in_map _ [] orig = orig"
| "store_byte_list_in_map pos (h # t) orig =
     store_byte_list_in_map (pos + 1) t
       (orig(pos := Some (Unknown h)))"

lemma nat_suc : "n \<ge> 0 \<Longrightarrow> Suc (nat n) = nat (n+1)"
apply(auto)
done

lemma store_bytes_eq :
  "sorted1(inorder tree) \<Longrightarrow> n \<ge> 0 \<Longrightarrow> map_tree_eq m tree \<Longrightarrow>
   map_tree_eq (store_byte_list_in_map (nat n) lst m)
               (store_byte_list_in_program n lst tree)"
apply(induction lst arbitrary:tree n m)
apply(simp add:map_tree_eq_def)
apply(auto)
apply(subst nat_suc)
apply(auto)
using update_eq
proof -
  fix a :: "8 word" and lsta :: "8 word list" and treea :: "(int \<times> inst, nat) tree" and na :: int and ma :: "nat \<Rightarrow> inst option"
  assume a1: "sorted1 (inorder treea)"
  assume a2: "map_tree_eq ma treea"
  assume a3: "\<And>tree n m. \<lbrakk>sorted1 (inorder tree); 0 \<le> n; map_tree_eq m tree\<rbrakk> \<Longrightarrow> map_tree_eq (store_byte_list_in_map (nat n) lsta m) (store_byte_list_in_program n lsta tree)"
  assume a4: "0 \<le> na"
  have f5: "sorted1 (inorder (update na (Unknown a) treea))"
    using a1 by (metis invar_update)
  have "0 \<le> nat na"
    by (metis not_le not_less_zero)
  then have "map_tree_eq (ma(nat na \<mapsto> Unknown a)) (update na (Unknown a) treea)"
  using a4 a2 a1 by (metis (no_types) nat_0_le update_eq)
  then show "map_tree_eq (store_byte_list_in_map (nat (na + 1)) lsta (ma(nat na \<mapsto> Unknown a))) (store_byte_list_in_program (na + 1) lsta (update na (Unknown a) treea))"
    using f5 a4 a3 by simp
  qed

fun program_map_of_lst ::
  "nat (* initial position in the AVL *) \<Rightarrow> inst list (* instructions *)
   \<Rightarrow> (nat, inst) map (* result *)"
where
  "program_map_of_lst _ [] = empty"
  -- {* the empty program is translated into the empty tree. *}
| "program_map_of_lst pos (Stack (PUSH_N bytes) # rest) =
   store_byte_list_in_map (pos + 1) bytes 
   ((program_map_of_lst (pos + 1 + length bytes) rest)
       (pos := Some (Stack (PUSH_N bytes))))"
  -- {* The PUSH instruction is translated together with the immediate value. *}
| "program_map_of_lst pos (i # rest) =
   (program_map_of_lst (pos + 1) rest)(pos := Some i)"

theorem content_small_aux_bytes [simp] :
  "k < pos \<Longrightarrow>
   m k = None \<Longrightarrow>
   (store_byte_list_in_map (pos+1) lst m) k = None"
apply(induction lst arbitrary:pos k m)
apply(auto)
done

theorem content_small [simp] :
   "k < pos \<Longrightarrow> program_content_of_list pos lst k = None"
apply(induction lst arbitrary:pos k)
apply(auto)
done

theorem content_small_aux_stack [simp] :
 "(\<And>pos k.
           k < pos \<Longrightarrow>
           program_content_of_lst pos lst k = None) \<Longrightarrow>
       k < pos \<Longrightarrow>
       a = Stack x10 \<Longrightarrow>
       program_content_of_lst pos (Stack x10 # lst) k =
       None"
apply(cases x10)
apply(auto)
done

theorem content_small_aux [simp] :
"(\<And>pos k.
           k < pos \<Longrightarrow>
           program_content_of_lst pos lst k = None) \<Longrightarrow>
       k < pos \<Longrightarrow>
       program_content_of_lst pos (a # lst) k = None"
apply(cases a)
apply(auto)
done

theorem update_add :
   "m k = None \<Longrightarrow>
    insert x (ran m) = ran (map_update k x m)"
apply(auto)
done

theorem ran_blargh :
  "m1 = m2 \<Longrightarrow> ran m1 = ran m2"
apply(auto)
done

theorem update_add2 :
   "m k = None \<Longrightarrow>
    insert x (ran m) =
    ran (\<lambda>a. if a = k then Some x else m a)"
apply(subst update_add)
apply(blast)
apply(rule ran_blargh)
apply(auto)
done

fun make_unknown :: "nat \<Rightarrow> byte list \<Rightarrow> (nat,inst) map" where
 "make_unknown pos [] = empty"
|"make_unknown pos (a#t) =
    map_update pos (Unknown a) (make_unknown (pos+1) t)"

theorem make_small [simp] :
  "k < pos \<Longrightarrow> make_unknown pos bytes k = None"
apply(induction bytes arbitrary:pos k)
apply(auto)
done

theorem unfold_update :
   "(m(pos \<mapsto> a)) x = (if x = pos then Some a else m x)"
apply(auto)
done

theorem make_unknown_lemma :
  "m2 pos = None \<Longrightarrow>
   m1(pos \<mapsto> a) ++ m2 = (m1 ++ m2)(pos \<mapsto> a)"
apply(subst map_add_def)
apply(subst map_add_def)
apply(subst unfold_update)
apply(auto)
done

theorem combine_some : "m2 n = Some x \<Longrightarrow> Some x = (m1 ++ m2) n"
apply(auto)
done

theorem combine_none :
   "m2 x = None \<Longrightarrow> m3 x = m1 x \<Longrightarrow> m3 x = (m1 ++ m2) x"
apply(auto)
by (simp add: map_add_def)

theorem program_list_bytes [simp] :
  "store_byte_list_in_program pos bytes m =
   m ++ make_unknown pos bytes"
apply(induction bytes arbitrary: pos m)
apply(auto simp:make_unknown_lemma)
done

theorem unknown_union :
  "(\<forall>k. k < pos + length bytes \<longrightarrow>  m k = None) \<Longrightarrow>
    ran (m ++ make_unknown pos bytes) =
    ran m \<union> Unknown ` set bytes"
apply(induction bytes arbitrary: pos m)
apply(auto)
done

theorem more_lemmas :
"insert x
        (Unknown ` set bytes \<union>
         ran
          (program_content_of_lst
            (Suc (pos + length bytes)) rest)) =
       ran
        (program_content_of_lst
          (Suc (pos + length bytes)) rest
         (pos \<mapsto> x) ++
         make_unknown (Suc pos) bytes)"
apply(subst make_unknown_lemma)
apply(auto simp:unknown_union)
done

theorem index_one [simp] :
  "0 < n \<Longrightarrow> index (x # lst) n = index lst (n-1)"
apply(cases n)
apply(auto)
done

theorem lemma_2 [simp] :
  "0 < n \<Longrightarrow>
   (\<And>t n. index (program_list_of_lst lst) n =
   program_content_of_lst t lst (n + t)) \<Longrightarrow>
   index (program_list_of_lst lst) (n-1) =
   program_content_of_lst (Suc t) lst (n + t)"
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
done

theorem index_append_small [simp] :
  "n < length a \<Longrightarrow> index (a @ b) n = index a n"
apply(auto)
by (simp add: nth_append)

theorem index_append_large1 [simp] :
  "index (a @ b) (n+length a) = index b n"
apply(induction a arbitrary:n b)
apply(auto)
done

theorem index_append_large [simp] :
  "n \<ge> length a \<Longrightarrow> index (a @ b) n = index b (n-length a)"
by (metis index_append_large1 ordered_cancel_comm_monoid_diff_class.diff_add)

fun get_stack :: "inst \<Rightarrow> stack_inst" where
"get_stack (Stack s) = s"

fun get_push_bytes :: "inst \<Rightarrow> byte list" where
"get_push_bytes (Stack (PUSH_N s)) = s"

theorem get_unknown [simp] :
  "n < length lst \<Longrightarrow>
   make_unknown t lst (n+t) = Some (Unknown (lst!n))"
apply(induction lst arbitrary:n t)
apply(simp)
apply(auto)
proof -
  fix lsta :: "8 word list" and na :: nat and ta :: nat
  assume a1: "na < Suc (length lsta)"
  assume a2: "0 < na"
  assume a3: "\<And>n t. n < length lsta \<Longrightarrow> make_unknown t lsta (n + t) = Some (Unknown (lsta ! n))"
  obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "\<forall>x0 x1. (\<exists>v2. x1 = Suc v2 \<and> v2 < x0) = (x1 = Suc (nn x0 x1) \<and> nn x0 x1 < x0)"
    by moura
  then have f4: "na = Suc (nn (length lsta) na) \<and> nn (length lsta) na < length lsta"
    using a2 a1 less_Suc_eq_0_disj by auto
  then have f5: "na + ta = nn (length lsta) na + Suc ta"
    by (metis add_Suc_shift)
  have "nn (length lsta) na = na - Suc 0"
    using f4 diff_Suc_1 by presburger
  then show "make_unknown (Suc ta) lsta (na + ta) = Some (Unknown (lsta ! (na - Suc 0)))"
    using f5 f4 a3 by presburger
qed

theorem get_unknown2 [simp] :
  "n \<ge> length lst \<Longrightarrow>
   make_unknown t lst (n+t) = None"
apply(induction lst arbitrary:n t)
apply(simp)
apply(auto)
by (metis (mono_tags, lifting) Suc_leD Suc_le_D add_Suc_shift le_SucE)

theorem lemma_3 :
    "(\<And>t n.
           index (program_list_of_lst lst) n =
           program_content_of_lst t lst (n + t)) \<Longrightarrow>
       n \<ge> x2 + 1 \<Longrightarrow>
       index (program_list_of_lst lst) (n - Suc x2) =
       program_content_of_lst (t + Suc x2) lst (n+t)"
apply(auto)
by (smt ab_semigroup_add_class.add_ac(1) add.commute add_Suc_right le_add_diff_inverse2)

theorem lemma_1 :
   "(\<And>t n.
           index (program_list_of_lst lst) n =
           program_content_of_lst t lst (n + t)) \<Longrightarrow>
       index (program_list_of_lst (a # lst)) n =
       program_content_of_lst t (a # lst) (n + t)"
apply(cases a)
apply(auto)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
defer
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply(cases "get_stack a")
apply(auto)
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
defer
apply (metis One_nat_def add_Suc_shift diff_Suc_1 less_imp_Suc_add)
apply(cases "n = 0")
apply(simp add:nth_append make_unknown_lemma)
apply(simp add:nth_append make_unknown_lemma)
apply(cases "n-1 < length (get_push_bytes a)")
apply(simp add:nth_append make_unknown_lemma)
apply(rule combine_some)
apply (metis Suc_pred add_Suc_shift get_unknown)
apply(simp add:nth_append make_unknown_lemma) (* n-1 \<ge> length x2 *)
apply(rule combine_none)
apply (metis Suc_pred add_Suc_shift get_unknown2 linorder_not_less)
using lemma_3
apply (fastforce)
done

theorem program_list_content_eq :
  "index (program_list_of_lst lst) n =
    program_content_of_lst t lst (n+t)"
apply(induction lst arbitrary:t n)
apply(auto simp:lemma_1)
done

theorem program_list_content :
  "set (program_list_of_lst lst) = ran (program_content_of_lst 0 lst)"
apply(induction lst rule:program_content_of_lst.induct)
apply(simp)
defer
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(simp)
apply(simp)
apply(rule update_add2)
apply(auto simp:more_lemmas)
done