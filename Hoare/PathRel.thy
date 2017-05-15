theory PathRel
imports Main
begin

definition path :: "'a rel \<Rightarrow> 'a list \<Rightarrow> bool" where
"path r lst = (\<forall>i < length lst-1. (lst!i, lst!(i+1)) \<in> r)"

fun pathR :: "'a rel \<Rightarrow> 'a list \<Rightarrow> bool" where
"pathR r (a#b#rest) = ((a,b) \<in> r \<and> pathR r (b#rest))"
| "pathR r _ = True"

lemma path_defs : "pathR r lst = path r lst"
apply (simp add:path_def)
apply (induction lst; simp)
apply (case_tac lst; auto simp add:less_Suc_eq_0_disj)
done

definition tlR :: "'a list rel" where
"tlR = {(a#lst,lst) | a lst. True }"

definition push_pop :: "'a list rel" where
"push_pop = (Id \<union> tlR \<union> converse tlR)"

definition sucR :: "nat rel" where
"sucR = {(Suc n,n) | n. True }"

definition inc_dec :: "nat rel" where
"inc_dec = (Id \<union> sucR \<union> converse sucR)"

lemma inc_dec_expand : "inc_dec = {(a,b) | a b. a+1 = b \<or> a=b \<or> a = b+1}"
by (auto simp:inc_dec_def sucR_def)

type_synonym 'a lang = "'a list \<Rightarrow> bool"

fun invL :: "'a set \<Rightarrow> 'a lang" where
"invL s [] = True"
| "invL s lst = (hd lst \<in> s \<and> last lst \<in> s)"

definition seq :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
"seq a b lst = (\<exists>u v. a u \<and> b v \<and> lst = u@v)"

definition star :: "'a lang \<Rightarrow> 'a lang" where
"star x lst = (\<exists>l. \<forall>el. el \<in> set l \<and> concat l = lst)"

(* *)
definition inc_decL :: "nat lang" where
"inc_decL lst = pathR inc_dec lst"

lemma test :
   "inc_decL lst \<Longrightarrow>
    i < length lst - 1 \<Longrightarrow>
    lst!i = lst!(i+1) \<or> lst!i = lst!(i+1)+1 \<or> lst!i+1 = lst!(i+1)"
by (auto simp add:inc_decL_def inc_dec_def sucR_def path_defs path_def)

definition push_popL :: "'a list lang" where
"push_popL lst = pathR push_pop lst"

lemma push_pop_inc_dec :
   "(a,b) \<in> push_pop \<Longrightarrow>
    (length a, length b) \<in> inc_dec"
by (auto simp: push_pop_def inc_dec_def sucR_def tlR_def)

definition mapR :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b rel" where
"mapR r f = {(f x,f y) | x y. (x,y) \<in> r}"

definition mapR2 :: "'a rel \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b rel" where
"mapR2 r f = {(x, y) | x y. (f x,f y) \<in> r}"

lemma push_pop_inc_dec_map : "mapR push_pop length \<subseteq> inc_dec"
unfolding mapR_def
using push_pop_inc_dec by fastforce

definition hd_last :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"hd_last lst a b = (hd lst = a \<and> last lst = b \<and> length lst > 0)"

lemma converse_rev : "pathR r lst \<Longrightarrow> pathR (converse r) (rev lst)"
unfolding path_defs path_def
  by (smt Suc_diff_Suc Suc_eq_plus1_left add.commute add.right_neutral converse.intros diff_Suc_less le_less_trans length_rev less_diff_conv not_add_less1 not_less rev_nth)

lemma sym_rev : "sym r \<Longrightarrow> pathR r lst \<Longrightarrow> pathR r (rev lst)"
  by (metis converse_rev sym_conv_converse_eq)

lemma list_all_values :
   "inc_decL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    last lst \<le> hd lst \<Longrightarrow>
    {last lst .. hd lst} \<subseteq> set lst"
apply (induction lst)
apply (auto simp add:inc_decL_def inc_dec_def sucR_def)
apply (case_tac lst; auto; fastforce)
done

lemma sym_inc_dec : "sym inc_dec"
  by (simp add: inc_dec_def sup_assoc sym_Id sym_Un sym_Un_converse)


lemma list_all_values2 :
   "inc_decL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    {min (hd lst) (last lst) .. max (hd lst) (last lst)} \<subseteq> set lst"
apply (cases "last lst \<le> hd lst")
  using list_all_values apply fastforce
  using list_all_values [of "rev lst"]
  by (simp add: sym_rev hd_rev inc_decL_def sym_inc_dec last_rev max_def min_def)

definition takeLast :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"takeLast n lst = rev (take n (rev lst))"

lemma takeLast_drop :
  "takeLast n lst = drop (length lst - n) lst"
apply (induction lst arbitrary:n)
apply (auto simp add:takeLast_def)
  by (metis length_Cons length_rev rev.simps(2) rev_append rev_rev_ident take_append take_rev)

(* unchanged *)
lemma next_unchanged :
  "(st1, st2) \<in> push_pop \<Longrightarrow>
   l \<le> length st2 \<Longrightarrow>
   l \<le> length st1 \<Longrightarrow>
   takeLast l st2 = takeLast l st1"
by (auto simp:push_pop_def tlR_def takeLast_def)

lemma pathR2 : "pathR r [a, b] = ((a,b) \<in> r)"
by auto

lemma pathR3 :
 "pathR r (a # b # list) = ((a,b) \<in> r \<and> pathR r (b#list))"
by auto

declare pathR.simps [simp del]

lemma stack_unchanged :
  "push_popL lst \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   (* hd_last lst a b \<Longrightarrow> *)
   \<forall>sti \<in> set lst. l \<le> length sti \<Longrightarrow>
   takeLast l (hd lst) = takeLast l (last lst)"
apply (induction lst)
apply (auto simp:push_popL_def hd_last_def)
by (metis (no_types, lifting) hd_conv_nth list.set_cases list.set_sel(1) next_unchanged nth_Cons_0 pathR.simps(1))

lemma take_all [simp] : "takeLast (length a) a = a"
by (simp add:takeLast_def)

lemma find_return :
   "push_popL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    length (last lst) \<le> length (hd lst) \<Longrightarrow>
    takeLast (length (last lst)) (hd lst) \<in> set lst"
apply (induction lst; auto simp:push_pop_def push_popL_def)
apply (case_tac lst; auto)
  apply (metis PathRel.take_all le_refl next_unchanged pathR.simps(1) push_pop_def)
apply (auto simp:pathR.simps)
  apply (smt Nitpick.size_list_simp(2) PathRel.take_all basic_trans_rules(31) inf_sup_aci(5) le_SucE list.sel(3) mem_Collect_eq next_unchanged prod.sel(1) prod.sel(2) push_pop_def sup.cobounded2 tlR_def zero_order(2))
  by (smt Suc_leD Suc_leI inf_sup_aci(5) inf_sup_ord(3) le_imp_less_Suc length_Cons mem_Collect_eq next_unchanged prod.inject push_pop_def subset_eq tlR_def)

definition monoI :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) \<Rightarrow> bool" where
"monoI iv v = (\<forall>i < length (snd v). iv (snd v!i) \<longrightarrow> iv ((fst v#snd v)!i))"

definition mono_same :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) rel" where
"mono_same iv = {((g1,lst), (g2,lst)) | lst g1 g2. iv g1 \<longrightarrow> iv g2}"

definition mono_pop :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) rel" where
"mono_pop iv =
   {((g1,a#lst), (g2,lst)) | lst g1 g2 a. iv g1 \<longrightarrow> iv a \<longrightarrow> iv g2}"

definition mono_push :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) rel" where
"mono_push iv =
   {((g1,lst), (g2,a#lst)) | lst g1 g2 a. iv g1 \<longrightarrow> iv a} \<inter>
   {((g1,lst), (g2,a#lst)) | lst g1 g2 a. iv a \<longrightarrow> iv g2}"

definition mono_rules :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) rel" where
"mono_rules iv = mono_same iv \<union> mono_pop iv \<union> mono_push iv"

lemma mono_same :
   "monoI iv a \<Longrightarrow>
    (a,b) \<in> mono_same iv \<Longrightarrow>
    monoI iv b"
unfolding monoI_def mono_same_def
  using less_SucI less_Suc_eq_0_disj by fastforce

lemma mono_push :
   "monoI iv (v1,lst) \<Longrightarrow>
    ((v1, lst), (v2,a#lst)) \<in> mono_push iv \<Longrightarrow>
    monoI iv (v2,a#lst)"
unfolding monoI_def mono_push_def
apply auto
  apply (metis diff_Suc_1 less_Suc_eq_0_disj nth_Cons')
  apply (metis diff_Suc_1 less_Suc_eq_0_disj nth_Cons')
  apply (metis diff_Suc_1 less_Suc_eq_0_disj nth_Cons')
done

lemma mono_pop :
   "monoI iv (v1,a#lst) \<Longrightarrow>
    ((v1,a#lst), (v2,lst)) \<in> mono_pop iv \<Longrightarrow>
    monoI iv (v2,lst)"
unfolding monoI_def mono_pop_def
apply auto
  apply (metis Suc_mono length_Cons less_SucI list.sel(3) nth_Cons' nth_tl)
  apply (metis Suc_mono length_Cons less_SucI list.sel(3) nth_Cons' nth_tl)
  apply (metis Suc_mono length_Cons less_SucI list.sel(3) nth_Cons' nth_tl)
done

lemma mono_works :
   "monoI iv (v1,lst1) \<Longrightarrow>
    ((v1,lst1), (v2,lst2)) \<in> mono_rules iv \<Longrightarrow>
    (lst1, lst2) \<in> push_pop \<Longrightarrow>
    monoI iv (v2,lst2)"
apply (auto simp add: push_pop_def)
using mono_same [of iv "(v1,lst2)" "(v2,lst2)"]
  apply (smt Int_iff Pair_inject UnE mem_Collect_eq mono_pop mono_pop_def mono_push_def mono_rules_def)
  apply (smt Int_iff UnE fst_conv mem_Collect_eq mono_pop mono_push mono_push_def mono_rules_def mono_same snd_conv tlR_def)
  by (smt UnE fst_conv mem_Collect_eq mono_pop mono_pop_def mono_push mono_rules_def mono_same snd_conv tlR_def)

definition first :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
"first P k lst ==
   k < length lst \<and> P (lst!k) \<and> (\<forall>k2 < k. \<not>P (lst!k2))"

definition first_return :: "nat \<Rightarrow> 'a list list \<Rightarrow> bool" where
"first_return k lst =
    first (\<lambda>b. b = tl (hd lst)) k lst"

definition first_smaller :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"first_smaller k lst = first (\<lambda>b. b < hd lst) k lst"

definition first_one_smaller :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"first_one_smaller k lst = first (\<lambda>b. Suc b = hd lst) k lst"

lemma pathR_take : "pathR r lst \<Longrightarrow> pathR r (take k lst)"
by (simp add:path_defs path_def)

lemma pathR_drop : "pathR r lst \<Longrightarrow> pathR r (drop k lst)"
by (simp add:path_defs path_def)

definition clip :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"clip k k3 lst = take (k - k3 + 1) (drop k3 lst)"

lemma pathR_clip : "pathR r lst \<Longrightarrow> pathR r (clip k1 k2 lst)"
by (simp add:pathR_drop pathR_take clip_def)

lemma hd_clip :
   "k3 < k \<Longrightarrow> k < length lst \<Longrightarrow>
    hd (clip k k3 lst) = lst!k3"
unfolding clip_def
  by (metis Cons_nth_drop_Suc Nat.add_0_right One_nat_def add_Suc_right list.sel(1) order.strict_trans take_Suc_Cons)

lemma last_index :
   "length lst > 0 \<Longrightarrow> last lst = lst!(length lst-1)"
  using last_conv_nth by auto

lemma last_clip :
   "k3 < k \<Longrightarrow> k < length lst \<Longrightarrow>
    last (clip k k3 lst) = lst!k"
unfolding clip_def
by (auto simp add: last_conv_nth min.absorb2)

lemma hd_take : "hd (take (Suc k3) lst) = hd lst"
  by (metis list.sel(1) take_Nil take_Suc)

lemma last_take :
  "length lst > k3 \<Longrightarrow>
   last (take (Suc k3) lst) = lst!k3"
  by (simp add: take_Suc_conv_app_nth)


lemma first_smaller1 :
   "inc_decL lst \<Longrightarrow>
    first_one_smaller k lst \<Longrightarrow>
    first_smaller k lst"
apply (cases "length lst > 0")
apply (auto simp:first_one_smaller_def first_def first_smaller_def)
subgoal for k3
using list_all_values [of "take (Suc k3) lst"]
apply (auto simp:inc_decL_def pathR_take hd_clip last_clip
  hd_take last_take)
apply (cases "lst!k \<in> set (take (Suc k3) lst)")
  apply (smt Suc_leI in_set_conv_nth le_neq_implies_less length_take min.absorb2 nth_take order.strict_trans)
  by (simp add: less_Suc_eq_le set_mp)
done

lemma inc_dec_too_large :
"z \<ge> y \<Longrightarrow>
 (z, x) \<in> inc_dec \<Longrightarrow>  
 Suc x < y \<Longrightarrow> False"
by (auto simp add:inc_dec_def sucR_def)

lemma first_smaller2 :
   "inc_decL lst \<Longrightarrow>
    first_smaller k lst \<Longrightarrow>
    first_one_smaller k lst"
apply (cases "length lst > 0")
apply (auto simp:first_one_smaller_def first_def first_smaller_def)
using list_all_values [of "take (Suc k) lst"]
apply (auto simp:inc_decL_def pathR_take hd_clip last_clip
  hd_take last_take)
apply (cases "Suc (lst ! k) < hd lst"; auto)
apply (cases "length lst > 1"; auto)
defer
apply (cases "length lst = 1"; auto)
  apply (simp add: hd_conv_nth)
apply (rule inc_dec_too_large [of "hd lst" "lst!(k-1)" "lst!k"])
apply auto
  apply (metis diff_is_0_eq diff_less dual_order.strict_implies_order hd_conv_nth less_Suc_eq_le not_le)
apply (auto simp add:path_defs path_def)
  by (smt One_nat_def Suc_eq_plus1 Suc_lessI Suc_n_not_le_n diff_less hd_conv_nth less_diff_conv less_or_eq_imp_le neq0_conv)

end
