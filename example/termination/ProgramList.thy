theory ProgramList

imports Main "../../ContractSem" "../../RelationalSem" "../../ProgramInAvl"

begin

declare cut_memory.simps [simp del]

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

lemma store_bytes_inv :
  "sorted1(inorder tree) \<Longrightarrow>
   sorted1(inorder (store_byte_list_in_program n lst tree))"
apply(induction lst arbitrary:tree n)
apply(auto)
  by (simp add: invar_update)

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
  have f5: "na + 1 = 1 + na"
    by auto
  have f6: "- 1 \<le> na"
    using a4 by linarith
  have "(0 \<le> 1 + na) = (- 1 \<le> na)"
    by fastforce
  then show "map_tree_eq (store_byte_list_in_map (nat (na + 1)) lsta (ma(nat na \<mapsto> Unknown a))) (store_byte_list_in_program (na + 1) lsta (update na (Unknown a) treea))"
    using f6 f5 a4 a3 a2 a1 by (metis invar_update le_add2 le_add_same_cancel2 nat_0_le update_eq)
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

lemma program_avl_inv :
  "sorted1(inorder (program_avl_of_lst n lst))"
proof (induction lst arbitrary:n)
case Nil thus ?case by simp
next
case (Cons a tl) thus ?case
proof (cases a)
  case (Unknown x1)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Bits x2)
  then show ?thesis
    by (simp add: Cons.IH invar_update)

next
  case (Sarith x3)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Arith x4)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Info x5)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Dup x6)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Memory x7)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Storage x8)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Pc x9)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Stack x10)
  then show ?thesis proof (cases x10)
    case POP
    then show ?thesis
      by (simp add: Cons.IH Stack invar_update) 
  next
    case (PUSH_N x2)
    then show ?thesis
      by (simp add: Cons.IH Stack invar_update store_bytes_inv) 
  next
    case CALLDATALOAD
    then show ?thesis by (simp add: Cons.IH Stack invar_update) 

  qed
    
next
  case (Swap x11)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Log x12)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
next
  case (Misc x13)
  then show ?thesis
    by (simp add: Cons.IH invar_update)
qed
qed

lemma nat_suc2 : "n \<ge> 0 \<Longrightarrow> Suc (nat n + length x2) = nat (n + 1 + length x2)"
apply(auto)
done

lemma content_eq : 
  "n \<ge> 0 \<Longrightarrow>
   map_tree_eq (program_map_of_lst (nat n) lst)
               (program_avl_of_lst n lst)"
proof (induction lst arbitrary:n)
case Nil thus ?case by (simp add:empty_eq)
next
case (Cons a tl) thus ?case
proof (cases a)
  case (Unknown x1)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Bits x2)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Sarith x3)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Arith x4)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Info x5)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Dup x6)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Memory x7)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Storage x8)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Pc x9)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Stack x10)
  then have "map_tree_eq
     (program_map_of_lst (nat n)
       (Stack x10 # tl))
     (program_avl_of_lst n (Stack x10 # tl))"
  proof (cases x10)
    case POP
    then show ?thesis
    apply(auto simp:map_tree_eq_def)
      apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
      by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_other map_tree_eq_def nat_suc program_avl_inv transfer_nat_int_relations(1))
  next
    case (PUSH_N x2)
    then show ?thesis
    (* apply(auto simp:map_tree_eq_def)
    apply(auto)
    apply(subst nat_suc)
    apply (simp add: Cons.prems)
    apply(subst nat_suc2)
    apply (simp add: Cons.prems) *)
    proof -
     have "map_tree_eq (program_map_of_lst
            (nat
              (n + 1 + int (length x2)))
            tl) (program_avl_of_lst
           (n + 1 + int (length x2))
           tl)" (is "map_tree_eq ?a1 ?b1")
       by (simp add: Cons.IH Cons.prems)
     then have "map_tree_eq (?a1(nat n \<mapsto> Stack (PUSH_N x2)))
                       (update n (Stack (PUSH_N x2)) ?b1)"
          (is "map_tree_eq ?a2 ?b2")
       by (metis Cons.prems le_add2 le_add_same_cancel2 nat_0_le program_avl_inv update_eq)
     then have "map_tree_eq
       (store_byte_list_in_map (nat (n + 1)) x2 ?a2)
       (store_byte_list_in_program (n + 1) x2 ?b2)"
       by (simp add: Cons.prems invar_update program_avl_inv store_bytes_eq)
     then show ?thesis
       by (smt Cons.prems PUSH_N Suc_eq_plus1 nat_0_le nat_int_add nat_suc program_avl_of_lst.simps(2) program_map_of_lst.simps(2))
     qed
  next
    case CALLDATALOAD
    then show ?thesis
    apply(auto simp:map_tree_eq_def)
      apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_other map_tree_eq_def nat_suc program_avl_inv transfer_nat_int_relations(1))
  qed
  then show ?thesis
    using Stack by auto
next
  case (Swap x11)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Log x12)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
next
  case (Misc x13)
  then show ?thesis 
apply(auto simp:map_tree_eq_def)
  apply (simp add: AVL_Map.map_update Cons.prems program_avl_inv transfer_nat_int_relations(1))
  by (smt AVL_Map.map_update Cons.IH Cons.prems fun_upd_apply int_eq_iff int_nat_eq map_tree_eq_def nat_eq_iff nat_suc program_avl_inv semiring_1_class.of_nat_simps(2))
qed
qed

theorem content_small_aux_bytes [simp] :
  "k < pos \<Longrightarrow>
   m k = None \<Longrightarrow>
   (store_byte_list_in_map (pos+1) lst m) k = None"
apply(induction lst arbitrary:pos k m)
apply(auto)
done

theorem content_small_aux_stack [simp] :
 "(\<And>pos k.
           k < pos \<Longrightarrow>
           program_map_of_lst pos lst k = None) \<Longrightarrow>
       k < pos \<Longrightarrow>
       a = Stack x10 \<Longrightarrow>
       program_map_of_lst pos (Stack x10 # lst) k =
       None"
apply(cases x10)
apply(auto)
  using Suc_eq_plus1 content_small_aux_bytes by auto

theorem content_small_aux [simp] :
"(\<And>pos k.
           k < pos \<Longrightarrow>
           program_map_of_lst pos lst k = None) \<Longrightarrow>
       k < pos \<Longrightarrow>
       program_map_of_lst pos (a # lst) k = None"
apply(cases a)
apply(auto)
done

theorem content_small [simp] :
   "k < pos \<Longrightarrow> program_map_of_lst pos lst k = None"
apply(induction lst arbitrary:pos k)
apply(auto)
done


theorem update_add :
   "m k = None \<Longrightarrow>
    Set.insert x (ran m) = ran (map_update k x m)"
apply(auto)
done

theorem ran_blargh :
  "m1 = m2 \<Longrightarrow> ran m1 = ran m2"
apply(auto)
done

theorem update_add2 :
   "m k = None \<Longrightarrow>
    Set.insert x (ran m) =
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
  "store_byte_list_in_map pos bytes m =
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
"Set.insert x
        (Unknown ` set bytes \<union>
         ran
          (program_map_of_lst
            (Suc (pos + length bytes)) rest)) =
       ran
        (program_map_of_lst
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
   program_map_of_lst t lst (n + t)) \<Longrightarrow>
   index (program_list_of_lst lst) (n-1) =
   program_map_of_lst (Suc t) lst (n + t)"
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
           program_map_of_lst t lst (n + t)) \<Longrightarrow>
       n \<ge> x2 + 1 \<Longrightarrow>
       index (program_list_of_lst lst) (n - Suc x2) =
       program_map_of_lst (t + Suc x2) lst (n+t)"
apply(auto)
by (smt ab_semigroup_add_class.add_ac(1) add.commute add_Suc_right le_add_diff_inverse2)

theorem lemma_1 :
   "(\<And>t n.
           index (program_list_of_lst lst) n =
           program_map_of_lst t lst (n + t)) \<Longrightarrow>
       index (program_list_of_lst (a # lst)) n =
       program_map_of_lst t (a # lst) (n + t)"
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

theorem program_list_map_eq :
  "index (program_list_of_lst lst) n =
    program_map_of_lst t lst (n+t)"
apply(induction lst arbitrary:t n)
apply(auto simp:lemma_1)
done

theorem program_list_content :
  "set (program_list_of_lst lst) = ran (program_map_of_lst 0 lst)"
apply(induction lst rule:program_map_of_lst.induct)
apply(simp)
defer
apply(simp)
(* apply(simp) *)
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

theorem program_list_content_eq :
  "index (program_list_of_lst lst) n =
   program_content_of_lst lst n"
proof -
  have a: "index (program_list_of_lst lst) n =
         program_map_of_lst 0 lst n"
    by (metis add.right_neutral program_list_map_eq)
  have b: "program_map_of_lst 0 lst n =
           program_content_of_lst lst n"
    by (smt content_eq map_tree_eq_def nat_0 nat_int of_nat_0_le_iff)
  from a and b show ?thesis by auto
qed

end


