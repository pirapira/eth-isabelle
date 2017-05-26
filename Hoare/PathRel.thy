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

definition minList :: "nat list \<Rightarrow> nat" where
"minList lst = foldr min lst (hd lst)"

definition maxList :: "nat list \<Rightarrow> nat" where
"maxList lst = foldr max lst (hd lst)"

lemma min_exists_aux :
   "n < length lst \<Longrightarrow>
    0 < length lst \<Longrightarrow>
    foldr min lst (x::nat) \<le> lst!n"
apply (induction lst arbitrary:n x; auto)
  using less_Suc_eq_0_disj min.coboundedI2 by fastforce

lemma max_exists_aux :
   "n < length lst \<Longrightarrow>
    0 < length lst \<Longrightarrow>
    foldr max lst (x::nat) \<ge> lst!n"
apply (induction lst arbitrary:n x; auto)
  using less_Suc_eq_0_disj max.coboundedI2 by fastforce

lemma min_exists :
   "length lst > 0 \<Longrightarrow> n < length lst \<Longrightarrow>
    minList lst \<le> lst!n"
unfolding minList_def
using min_exists_aux by simp

lemma max_exists :
   "length lst > 0 \<Longrightarrow> n < length lst \<Longrightarrow>
    maxList lst \<ge> lst!n"
unfolding maxList_def
using max_exists_aux by simp


lemma min_max :
  "length lst > 0 \<Longrightarrow>
   set lst \<subseteq> {minList lst .. maxList lst}"
by (metis atLeastAtMost_iff in_set_conv_nth max_exists min_exists subsetI)

lemma minList_one : "minList [a] = a"
by (simp add:minList_def)

lemma min_aux : "foldr min lst (x::nat) \<le> x"
by (induction lst arbitrary:x; auto simp add: min.coboundedI2)

lemma max_aux : "foldr max lst (x::nat) \<ge> x"
by (induction lst arbitrary:x; auto simp add: max.coboundedI2)

lemma minlist1 : "a \<le> b \<Longrightarrow> minList (a # b # list) = minList (a#list)"
by (simp add: minList_def)

lemma maxlist1 : "a \<ge> b \<Longrightarrow> maxList (a # b # list) = maxList (a#list)"
by (simp add: maxList_def)

lemma min_smaller :
   "x \<le> y \<Longrightarrow> foldr min lst (x::nat) \<le> foldr min lst y"
by (induction lst arbitrary:x; auto simp add: min.coboundedI2)

lemma min_min : "a \<ge> (b::nat) \<Longrightarrow> min a (min b c) = min b c"
by simp

lemma min_min2 : "a \<le> (b::nat) \<Longrightarrow> min a (min b c) = min a c"
by simp

lemma min_simp : "a < (b::nat) \<Longrightarrow> min b a = a"
by simp

lemma min_of_min :
   "b \<le> (a::nat) \<Longrightarrow> min b (foldr min lst a) = min b (foldr min lst b)"
by (induction lst; auto)

lemma max_of_max :
   "b \<ge> (a::nat) \<Longrightarrow> max b (foldr max lst a) = max b (foldr max lst b)"
by (induction lst; auto)

lemma minlist_swap :
   "minList (a # b # list) = minList (b # a # list)"
apply (simp add: minList_def)
apply (cases "a \<ge> b")
apply (auto simp add:min_min min_min2)
apply (rule min_of_min; auto)
using min_of_min [of a b list]
  by auto

lemma maxlist_swap :
   "maxList (a # b # list) = maxList (b # a # list)"
by (simp add: maxList_def;cases "a \<le> b"; metis linear max.left_commute max_of_max)

lemma minlist2 : "a \<ge> b \<Longrightarrow> minList (a # b # list) = minList (b#list)"
  using minlist1 minlist_swap by fastforce

lemma maxlist2 : "a \<le> b \<Longrightarrow> maxList (a # b # list) = maxList (b#list)"
  using maxlist1 maxlist_swap by fastforce

lemma find_min :
  "length lst > 0 \<Longrightarrow> \<exists>k. minList lst = lst!k"
apply (induction lst; auto)
apply (case_tac lst; auto simp add:minList_one)
  apply (metis nth_Cons_0)
apply (case_tac "aa \<le> a")
apply (simp add:minlist2)
  apply (metis nth_Cons_Suc)
apply (case_tac "a \<le> aa")
apply (case_tac k)
apply auto
apply (simp add:minList_def min_min2)
apply (rule exI[where x = 0])
apply auto
  apply (metis min_absorb2 min_aux min_def min_of_min)
apply (case_tac "a \<le> minList (aa#list)")
apply auto
apply (rule exI[where x = 0])
apply auto
apply (simp add:minList_def min_min2)
  apply (metis min.absorb2 min_aux min_def min_of_min)
subgoal for a b list nat
apply (rule exI[where x = "nat+2"])
apply auto
apply (simp add:minList_def min_min2)
  by (metis min_def min_of_min)
done

lemma find_max :
  "length lst > 0 \<Longrightarrow> \<exists>k. maxList lst = lst!k"
apply (induction lst; auto)
apply (case_tac lst; auto)
apply (simp add:maxList_def)
  apply (metis nth_Cons_0)
apply (case_tac "aa \<ge> a")
apply (simp add:maxlist2)
  apply (metis nth_Cons_Suc)
apply (case_tac "a \<ge> aa")
apply (case_tac k)
apply auto
apply (rule exI[where x = 0])
  apply (metis foldr.simps(2) list.sel(1) max.orderE maxList_def max_of_max nth_Cons_0 o_apply)
apply (case_tac "a \<ge> maxList (aa#list)")
apply auto
apply (rule exI[where x = 0])
apply auto
  apply (metis foldr.simps(2) list.sel(1) max.orderE maxList_def max_of_max o_apply)
subgoal for a b list nat
apply (rule exI[where x = "nat+2"])
apply auto
apply (simp add:maxList_def)
  by (smt inf_sup_aci(5) max_def max_of_max sup_nat_def)
done

lemma find_max2 :
  "length lst > 0 \<Longrightarrow> \<exists>k < length lst. maxList lst = lst!k"
apply (induction lst; auto)
apply (case_tac lst; auto)
apply (simp add:maxList_def)
apply (case_tac "aa \<ge> a")
apply (simp add:maxlist2)
  apply auto[1]
apply (case_tac "a \<ge> aa")
apply (case_tac k)
apply auto
apply (rule exI[where x = 0])
subgoal for a b list
apply auto
  apply (metis foldr.simps(2) list.sel(1) max.orderE maxList_def max_of_max o_apply)
done
apply (case_tac "a \<ge> maxList (aa#list)")
apply auto
apply (rule exI[where x = 0])
apply auto
  apply (metis foldr.simps(2) list.sel(1) max.orderE maxList_def max_of_max o_apply)
subgoal for a b list nat
apply (rule exI[where x = "nat+2"])
apply auto
apply (simp add:maxList_def)
  by (smt inf_sup_aci(5) max_def max_of_max sup_nat_def)
done

lemma find_min2 :
  "length lst > 0 \<Longrightarrow> \<exists>k < length lst. minList lst = lst!k"
apply (induction lst; auto)
apply (case_tac lst; auto)
apply (simp add:minList_def)
apply (case_tac "aa \<le> a")
apply (simp add:minlist2)
  apply auto[1]
apply (case_tac "a \<le> aa")
apply (case_tac k)
apply auto
apply (rule exI[where x = 0])
subgoal for a b list
apply auto
  apply (metis foldr.simps(2) list.sel(1) min.orderE minList_def min_of_min o_apply)
done
apply (case_tac "a \<le> minList (aa#list)")
apply auto
apply (rule exI[where x = 0])
apply auto
  apply (metis foldr.simps(2) list.sel(1) min.orderE minList_def min_of_min o_apply)
subgoal for a b list nat
apply (rule exI[where x = "nat+2"])
apply auto
apply (simp add:minList_def)
  by (smt inf_sup_aci(5) min_def min_of_min sup_nat_def)
done

lemma clip_set : "set (clip imin imax lst) \<subseteq> set lst"
  by (metis clip_def dual_order.trans set_drop_subset set_take_subset)

lemma min_max_all_values :
   "inc_decL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    {minList lst .. maxList lst} \<subseteq> set lst"
using find_min2 [of lst] find_max2 [of lst]
apply clarsimp
subgoal for x imin imax
apply (case_tac "imax = imin")
apply simp

apply (case_tac "imax < imin")
using list_all_values [of "clip imin imax lst"]
apply (simp add:hd_clip last_clip inc_decL_def
  pathR_clip)
apply (cases "clip imin imax lst = []"; auto)
apply (simp add:clip_def)
using clip_set [of imin imax lst]
  using atLeastAtMost_iff apply blast

apply (case_tac "imin < imax"; auto)
using list_all_values2 [of "clip imax imin lst"]
apply (simp add:hd_clip last_clip inc_decL_def
  pathR_clip)
apply (cases "clip imax imin lst = []"; auto)
apply (simp add:clip_def)
using clip_set [of imax imin lst]
  by fastforce
done

lemma min_max_all_values2 :
   "inc_decL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    {minList lst .. maxList lst} = set lst"
  by (simp add: antisym min_max min_max_all_values)

lemma push_popL_inc_decL :
   "push_popL lst \<Longrightarrow> inc_decL (map length lst)"
by (auto simp add:push_popL_def inc_decL_def path_defs path_def
                     push_pop_inc_dec)

definition first_return :: "nat \<Rightarrow> 'a list list \<Rightarrow> bool" where
"first_return k lst =
    first (\<lambda>b. (hd lst,b) \<in> tlR) k lst"

lemma takeLast_cons :
  "takeLast (length lst) (a # lst) = lst"
by (simp add:takeLast_def)

(* *)
lemma first_return_smaller :
   "push_popL lst \<Longrightarrow>
    first_return k lst \<Longrightarrow>
    first_one_smaller k (map length lst)"
apply (cases "length lst > 0")
apply (auto simp:first_one_smaller_def first_def
   first_return_def tlR_def hd_map)
subgoal for a k1
using find_return [of "take (Suc k1) lst"]
apply (simp add:hd_take last_take)
apply (cases "push_popL (take (Suc k1) lst)")
apply (auto simp add:takeLast_cons push_popL_def pathR_take)
apply (smt in_set_conv_nth length_take less_SucE less_imp_le_nat less_trans_Suc min.absorb2 nth_take order.strict_trans)
done
done

lemma first_smaller_return :
   "push_popL lst \<Longrightarrow>
    first_smaller k (map length lst) \<Longrightarrow>
    first_one_smaller k (map length lst) \<Longrightarrow>
    first_return k lst"
apply (cases "length lst > 0")
apply (auto simp:first_one_smaller_def
   first_smaller_def first_def
   first_return_def tlR_def hd_map)
apply (cases "hd lst"; auto)
subgoal for a list
using stack_unchanged [of "take (Suc k) lst" "length list"]
apply (simp add:push_popL_def pathR_take hd_take last_take
  takeLast_def)
  by (smt Suc_leD in_set_conv_nth length_take less_SucE less_or_eq_imp_le min.absorb2 not_le nth_take)
done

(* call includes enter and exit *)
definition call :: "'a list list \<Rightarrow> bool" where
"call lst = (
   length lst > 2 \<and>
   (lst!1, lst!0) \<in> tlR \<and>
   push_popL lst \<and>
   first_return (length lst-2) (tl lst))"

definition ncall :: "nat list \<Rightarrow> bool" where
"ncall lst = (
   length lst > 2 \<and>
   (lst!1, lst!0) \<in> sucR \<and>
   inc_decL lst \<and>
   first_one_smaller (length lst-2) (tl lst))"

(* a call is a kind of a cycle...
   perhaps cycles have useful features *)
lemma call_stack_length :
  "call lst \<Longrightarrow> hd lst = last lst"
apply (auto simp add:call_def first_return_def first_def tlR_def)
  by (metis One_nat_def Suc_diff_Suc Suc_lessD hd_conv_nth last_conv_nth length_tl less_numeral_extra(2) list.inject list.size(3) nth_tl numeral_2_eq_2 zero_less_diff)

lemma ncall_stack_length :
  "ncall lst \<Longrightarrow> hd lst = last lst"
apply (auto simp add:ncall_def first_one_smaller_def first_def sucR_def)
  by (metis (no_types, hide_lams) One_nat_def Suc_1 Suc_diff_Suc diff_Suc_1 gr_implies_not_zero hd_conv_nth in_set_conv_nth last_index length_pos_if_in_set length_tl less_trans_Suc list.size(3) nth_tl zero_less_numeral)

lemma pathR_tl : "pathR r lst \<Longrightarrow> pathR r (tl lst)"
apply (auto simp add:path_defs path_def)
  by (simp add: nth_tl)


lemma call_ncall : "call lst \<Longrightarrow> ncall (map length lst)"
apply (auto simp add:call_def ncall_def tlR_def sucR_def)
  apply (metis Suc_lessD nth_map numeral_2_eq_2)
  using push_popL_inc_decL apply auto[1]
using first_return_smaller [of "tl lst" "length lst - 2"]
by (simp add:push_popL_def pathR_tl map_tl)

lemma ncall_call :
   "ncall (map length lst) \<Longrightarrow>
    push_popL lst \<Longrightarrow>
    call lst"
apply (auto simp add:call_def ncall_def tlR_def sucR_def)
apply (cases "lst!1"; auto)
apply (subst (asm) nth_map)
apply auto
apply (simp add:push_popL_def path_defs path_def push_pop_def
  tlR_def)
subgoal for a list proof -
  fix a :: 'a and list :: "'a list"
  assume a1: "\<forall>i<length lst - Suc 0. lst ! i = lst ! Suc i \<or> (\<exists>a. lst ! i = a # lst ! Suc i) \<or> (\<exists>a. lst ! Suc i = a # lst ! i)"
  assume a2: "2 < length lst"
  assume a3: "length list = length (lst ! 0)"
  assume a4: "lst ! Suc 0 = a # list"
  have "[] \<noteq> tl lst"
    using a2 by (metis (no_types) One_nat_def Suc_pred length_tl less_Suc_eq less_trans_Suc list.size(3) nat_neq_iff zero_less_numeral)
  then show "list = lst ! 0"
  using a4 a3 a1 by (metis (no_types) One_nat_def length_Cons length_greater_0_conv length_tl less_Suc_eq list.sel(3) nat_neq_iff)
qed
apply (rule first_smaller_return)
apply (simp add:push_popL_def pathR_tl)
apply (rule first_smaller1)
apply (auto simp add:inc_decL_def pathR_tl map_tl)
done

(* extended call might have some stuff around it *)
definition ecall :: "'a list list \<Rightarrow> 'a list \<Rightarrow> bool" where
"ecall lst s = (\<exists>k1 k2.
   k1 < k2 \<and> k2 < length lst \<and> call (clip k2 k1 lst) \<and>
   set (take (Suc k1) lst) = {s} \<and>
   set (drop k2 lst) = {s})"

definition scall :: "'a list list \<Rightarrow> 'a list \<Rightarrow> bool" where
"scall lst s = (call lst \<and> hd lst = s)"

definition sncall :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
"sncall lst s = (ncall lst \<and> hd lst = s)"

definition const_seq :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
"const_seq lst s = (set lst \<subseteq> {s})"

lemma const_single : "const_seq [x] x"
by (simp add:const_seq_def)

(* perhaps naturals can be divided into sequences easier? *)

definition call_end :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
"call_end lst s = (
   length lst > 1 \<and>
   Suc s = hd lst \<and>
   inc_decL lst \<and>
   first_one_smaller (length lst-1) lst)"

(*

find index

fun split_at :: "nat \<Rightarrow> nat list \<Rightarrow> nat list * nat list" where
"split_at a [] = [[]]"
""
*)

fun decompose :: "nat list \<Rightarrow> nat \<Rightarrow> nat list list" where
"decompose lst n = (
   let l1 = takeWhile (%k. k > n) lst in
   let rest = dropWhile (%k. k > n) lst in
   if length rest = 0 then [l1] else
   if length rest = 1 \<or> length (tl rest) \<ge> length lst
      then [l1@[hd rest]] else
   (l1@[hd rest]) # decompose (tl rest) n
)"

lemma concat_decompose_base :
   "dropWhile pred lst = [] \<Longrightarrow> takeWhile pred lst = lst"
by (induction lst; auto; metis list.distinct(1))

lemma concat_decompose_base2 :
   "dropWhile pred lst = [a] \<Longrightarrow> takeWhile pred lst @ [a] = lst"
by (induction lst; auto; metis list.distinct(1))

lemma concat_decompose_step :
   "dropWhile pred lst = a#rest \<Longrightarrow>
    takeWhile pred lst @ [a] @ rest = lst"
  by (metis append_Cons append_Nil takeWhile_dropWhile_id)

fun findIndices :: "'a list \<Rightarrow> 'a \<Rightarrow> nat list" where
"findIndices (b#rest) a =
   (if a = b then [0] else []) @ map Suc (findIndices rest a)"
| "findIndices [] a = []"

lemma get_index :
   "i \<in> set (findIndices lst a) \<Longrightarrow> lst!i = a"
by (induction lst arbitrary:i; auto)

lemma do_find :
   "length (findIndices lst a) > 0 \<Longrightarrow>
    take (hd (findIndices lst a)) lst @ [a] @
    drop (hd (findIndices lst a)+1) lst = lst"
by (induction lst; auto simp add: hd_map)

lemma tl_map_suc :
   "tl lst = map f lst2 \<Longrightarrow>
    tl (map g lst) = map (%x. g (f x)) lst2"
by (induction lst arbitrary:lst2; auto)

lemma split_findIndices :
   "length (findIndices lst a) > 0 \<Longrightarrow>
    tl (findIndices lst a) =
    map (%i. i + (hd (findIndices lst a)) + 1)
    (findIndices (drop (hd (findIndices lst a)+1) lst) a)"
by (induction lst; auto simp add: hd_map tl_map_suc)

lemma sorted_indices_aux :
  "findIndices lst a = i1 # i2 # ilst \<Longrightarrow>
   i1 < i2"
using split_findIndices [of lst a]
by auto

lemma tl_suc_rule :
   "length lst > 1 \<Longrightarrow>
    tl lst! i < tl lst ! Suc i \<Longrightarrow>
    lst! Suc i < lst ! Suc (Suc i)"
by (cases lst; auto)

lemma map_suc_rule :
"n < length lst \<Longrightarrow> m < length lst \<Longrightarrow>
 lst!n < lst!m \<Longrightarrow>
 map (\<lambda>i. Suc (i + x)) lst ! n < map (\<lambda>i. Suc (i + x)) lst ! m"
  by simp

lemma sorted_again :
   "i + 1 < length (findIndices lst a) \<Longrightarrow>
    findIndices lst a ! i < findIndices lst a ! (i+1)"
apply (induction i arbitrary:lst)
apply auto
apply (case_tac "findIndices lst a"; auto)
apply (case_tac "list"; auto)
using sorted_indices_aux apply force
apply (rule tl_suc_rule)
apply auto
subgoal for i lst
using split_findIndices [of lst a]
apply simp
apply (cases "findIndices lst a = []"; auto)
apply (rule map_suc_rule)
  apply (metis Suc_lessD Suc_lessE diff_Suc_1 length_map length_tl)
  apply (metis Suc_lessE diff_Suc_1 length_map length_tl)
  by (metis Nitpick.size_list_simp(2) Suc_less_eq length_map)
done

(*
lemma nth_split_findIndices :
   "length (findIndices lst a) > n \<Longrightarrow>
    drop (Suc n) (findIndices lst a) =
    map (%i. i + (findIndices lst a!n) + 1)
    (findIndices (drop ((findIndices lst a!n)+1) lst) a)"
apply (induction n arbitrary:lst)
apply auto
subgoal for lst
using split_findIndices [of lst a]
apply auto
by (simp add: drop_Suc hd_conv_nth)
apply (case_tac lst)
apply auto

*)

lemma weird_mono_aux :
   "(\<forall>n. Suc n < limit \<longrightarrow> f n < f (Suc n)) \<Longrightarrow> k+m < limit \<Longrightarrow> (f k::nat) \<le> f (k+m)"
by (induction m; auto)

lemma weird_mono :
   "(\<forall>n. Suc n < limit \<longrightarrow> f n < f (Suc n)) \<Longrightarrow>
   k < limit \<Longrightarrow> m < limit \<Longrightarrow> m \<le> k \<Longrightarrow> (f m::nat) \<le> f k"
using weird_mono_aux [of limit f]
  by (metis le_add_diff_inverse)


lemma sorted_indices : "sorted (findIndices lst a)"
apply (rule sorted_nth_monoI)
apply (rule weird_mono [of "length (findIndices lst a)"
  "%i. findIndices lst a ! i"])
apply auto
using sorted_again by force

(* do splitting based on indexes *)
fun indexSplit :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"indexSplit (i1#ilst) lst =
   take (Suc i1) lst # indexSplit (map (%x. x-i1-1) ilst) (drop (Suc i1) lst)"
| "indexSplit [] lst = [lst]"

value "findIndices [a,a] a"

value "((\<lambda>x. x - Suc 0) \<circ> Suc) 0"

lemma funext : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
by auto

lemma inc_dec : "((\<lambda>x. x - Suc 0) \<circ> Suc) = id"
by (rule funext; auto)

lemma duh : "map ((\<lambda>x. x - Suc 0) \<circ> Suc) lst = lst"
by (simp add:inc_dec)

lemma empty_split :
   "set (indexSplit ilst []) = {[]}"
by (induction ilst "[]" rule:indexSplit.induct; auto)

lemma empty_length : "set lst = {[]} \<Longrightarrow> concat lst = []"
  by (simp add: empty_split)

lemma empty_split2 : "concat (indexSplit ilst []) = []"
  by (simp add: empty_split)

lemma split_combine_step :
   "concat (indexSplit (map Suc ilst) (aa # lst)) =
    aa # concat (indexSplit ilst lst)"
apply (induction ilst lst rule:indexSplit.induct)
apply auto
  by (metis comp_apply diff_Suc_Suc)

lemma split_and_combine :
   "concat (indexSplit (findIndices lst a) lst) = lst"
by (induction lst; auto simp add:duh split_combine_step)

lemma call_end_ends :
   "call_end lst s \<Longrightarrow> s = last lst"
apply (auto simp add:call_end_def first_one_smaller_def first_def)
  by (metis One_nat_def Suc_inject last_conv_nth less_numeral_extra(2) list.size(3))

definition split :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list list" where
"split lst a = indexSplit (findIndices lst a) lst"

(* split into a constant sequence *)
lemma split_one : "hd (split (a#lst) a) = [a]"
by (auto simp add:split_def)

definition first_elem :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
"first_elem el k lst = first (%x. x = el) k lst"

lemma feq_aux : "x > 0 \<Longrightarrow> (\<lambda>b. Suc b = x) = (\<lambda>b. b = x - Suc 0)"
by (rule funext; auto)

lemma one_smaller_elem :
  "length lst > 0 \<Longrightarrow>
   hd lst > 0 \<Longrightarrow>
   first_one_smaller k lst = first_elem (hd lst - 1) k lst"
by (simp add:first_one_smaller_def first_elem_def feq_aux)

lemma find_index :
   "i < length lst \<Longrightarrow> i \<in> set (findIndices lst (lst!i))"
apply (induction lst "lst!i" arbitrary:i rule:findIndices.induct)
by (auto simp add: less_Suc_eq_0_disj)

lemma more_mono_aux :
   "(\<forall>n. Suc n < limit \<longrightarrow> f n < f (Suc n)) \<Longrightarrow>
     k+m+1 < limit \<Longrightarrow> (f k::nat) < f (k+m+1)"
by (induction m; auto)

lemma more_mono :
   "(\<forall>n. Suc n < limit \<longrightarrow> f n < f (Suc n)) \<Longrightarrow>
   k < limit \<Longrightarrow> m < limit \<Longrightarrow> m < k \<Longrightarrow> (f m::nat) < f k"
using more_mono_aux [of limit f]
  by (metis Suc_eq_plus1 less_imp_Suc_add)

lemma use_sorting_aux :
   "length (findIndices lst el) > m \<Longrightarrow>
    m > n \<Longrightarrow>
    findIndices lst el!n < findIndices lst el!m"
apply (rule more_mono [of "length (findIndices lst el)"
   "%i. findIndices lst el!i"]; auto)
using sorted_again apply force
done

lemma use_sorting :
   "findIndices lst el = a # list \<Longrightarrow>
    x \<in> set list \<Longrightarrow>
    a < x"
using use_sorting_aux [of _ lst el]
  by (smt in_set_conv_nth length_Cons lessI less_trans_Suc list.sel(3) nth_Cons_0 nth_tl zero_less_Suc)

lemma find_elem :
 "first_elem el k lst \<Longrightarrow>
  hd (findIndices lst el) = k"
apply (auto simp:first_elem_def first_def)
apply (cases "findIndices lst (lst ! k)")
  using find_index apply fastforce
apply auto
apply (case_tac "\<forall>x \<in> set list. x > a")
defer
using use_sorting apply force
  by (metis find_index get_index list.set_intros(1) set_ConsD)

lemma split_first :
   "hd (indexSplit (i#ilst) lst) = take (Suc i) lst"
by auto

lemma get_to_end :
  "hd lst = Suc (last lst) \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   first_one_smaller k lst \<Longrightarrow>
   hd (indexSplit (findIndices lst (last lst)) lst) =
   take (Suc k) lst"
apply (cases "\<not>first_elem (last lst) k lst")
using one_smaller_elem apply fastforce
apply auto
using find_elem [of "last lst" k lst]
  by (metis (full_types) find_index first_def first_elem_def hd_Cons_tl length_pos_if_in_set less_numeral_extra(3) list.size(3) split_first)

lemma make_call_end :
  "hd lst = Suc (last lst) \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   first_one_smaller k lst \<Longrightarrow>
   inc_decL lst \<Longrightarrow>
   call_end (take (Suc k) lst) (last lst)"
apply (auto simp add:call_end_def hd_take inc_decL_def
 pathR_take first_one_smaller_def first_def min.absorb2)
by (metis gr_zeroI hd_conv_nth n_not_Suc_n)

lemma find_first :
   "P (lst!i) \<Longrightarrow> i < length lst \<Longrightarrow> \<exists>k \<le> i. first P k lst"
apply (induction lst arbitrary:i)
apply (auto simp add:first_def)
apply (case_tac i;auto)
apply (case_tac "P a")
subgoal for a lst nat
apply (rule exI[where x = 0])
by auto
apply (case_tac "\<forall>j < Suc nat. \<not> P ((a # lst) ! j)")
subgoal for a lst nat by (rule exI[where x = "Suc nat"]; auto)
apply auto
apply (case_tac j; auto)
apply (case_tac "\<exists>k\<le>nata.
                k < length lst \<and>
                P (lst ! k) \<and> (\<forall>k2<k. \<not> P (lst ! k2))")
apply (thin_tac "(\<And>i. P (lst ! i) \<Longrightarrow>
             i < length lst \<Longrightarrow>
             \<exists>k\<le>i.
                k < length lst \<and>
                P (lst ! k) \<and> (\<forall>k2<k. \<not> P (lst ! k2)))")
apply auto
subgoal for a lst nat nata k
apply (rule exI [where x = "Suc k"])
apply auto
  using less_Suc_eq_0_disj by auto
done

lemma find_first_one_smaller :
  "1 < length lst \<Longrightarrow>
   hd lst = Suc (last lst) \<Longrightarrow>
   \<exists>k. first_one_smaller k lst"
apply (simp add:first_one_smaller_def)
using find_first [of "\<lambda>b. b = last lst" lst "length lst - 1"]
by (metis One_nat_def Suc_lessD diff_Suc_less last_conv_nth less_numeral_extra(2) list.size(3))

lemma hd_good :
  "inc_decL lst \<Longrightarrow>
   hd lst = last lst \<or> hd lst = Suc (last lst) \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   x = hd (split lst (last lst)) \<Longrightarrow>
   call_end x (last lst) \<or> const_seq x (last lst)"
apply (auto simp:split_def)
  apply (metis PathRel.split_def const_single list.collapse split_one)
using find_first_one_smaller [of lst]
apply auto
apply (cases "length lst = 1")
  apply (simp add: hd_conv_nth last_conv_nth)
apply (cases "Suc 0 < length lst")
apply auto
defer
  apply (simp add: hd_conv_nth last_conv_nth)
subgoal for k
using get_to_end [of lst k]
  make_call_end [of lst k]
  by simp
done

(* splitting split *)
lemma split_index_split :
   "tl (indexSplit (i#ilst) lst) =
    indexSplit (map (%j. j - Suc i) ilst)
                   (drop (Suc i) lst)"
by auto

lemma split_index_split2 :
   "indexSplit (i#ilst) lst = a#rest \<Longrightarrow>
    length a < length lst \<Longrightarrow>
    length a = Suc i"
by auto

lemma split_index_split3 :
   "indexSplit (i#ilst) lst = a#rest \<Longrightarrow>
    length a < length lst \<Longrightarrow>
    rest = indexSplit (map (%j. j - length a) ilst)
                   (drop (length a) lst)"
using split_index_split split_index_split2 by fastforce

lemma duh2 :
 "((\<lambda>x. x - Suc aa) \<circ> (\<lambda>i. Suc (i + aa))) = id"
by (rule funext; auto)

lemma aux1 :
  "findIndices lst el = aa # list \<Longrightarrow>
   map (\<lambda>x. x - Suc aa) list =
   findIndices (drop (Suc aa) lst) el"
using split_findIndices [of lst el]
by (simp add:duh2)

lemma split_split :
   "split lst (last lst) = a # rest \<Longrightarrow>
    length a < length lst \<Longrightarrow>
    rest = split (drop (length a) lst) (last lst)"
apply (simp add:split_def)
apply (case_tac "findIndices lst (last lst)")
apply auto
subgoal for aa list
apply (cases "aa < length lst")
defer
  apply linarith
apply (cases "min (length lst) (Suc aa) = Suc aa")
apply auto
using aux1 apply fastforce
done done

lemma split_combine : "concat (split lst el) = lst"
unfolding split_def
using split_and_combine [of lst el]
by simp

lemma split_final_aux : 
  "split lst el = a # rest \<Longrightarrow>
   length a = length lst \<Longrightarrow>
   concat rest = []"
using split_combine [of lst el]
  by auto

lemma split_final : 
  "split lst el = a # rest \<Longrightarrow>
   length a = length lst \<Longrightarrow>
   set rest \<subseteq> {[]}"
using split_final_aux [of lst el a rest]
  by auto


lemma split_length : 
  "split lst el = a # rest \<Longrightarrow>
   length a \<le> length lst"
using split_combine [of lst el]
  by auto

lemma split_last_aux1 :
"split lst (last lst) = a # rest \<Longrightarrow>
 length a > 0 \<Longrightarrow>
 length lst > 0"
  using split_length by fastforce

lemma find_first_elem :
  "0 < length lst \<Longrightarrow>
   \<exists>k. first_elem (last lst) k lst"
apply (simp add:first_elem_def)
using find_first [of "\<lambda>b. b = last lst" lst "length lst - 1"]
  by (metis One_nat_def diff_Suc_less last_conv_nth length_greater_0_conv)


lemma split_last :
"split lst (last lst) = a # rest \<Longrightarrow>
 length a > 0 \<Longrightarrow>
 last a = last lst"
using split_last_aux1 [of lst a rest]
apply simp
using find_first_elem [of lst]
apply (auto simp:split_def)
apply (cases "findIndices lst (last lst)")
apply simp
subgoal for k aa list
using find_elem  [of "last lst" k lst]
apply auto
  by (metis List.take_all Suc_lessD get_index last_take list.set_intros(1) not_le)
done

lemma split_last_nth :
"split lst (last lst) = a # rest \<Longrightarrow>
 length a > 0 \<Longrightarrow>
 lst!(length a - 1) = last lst"
using split_last [of lst a rest]
  split_combine [of lst "last lst"]
  by (metis One_nat_def concat.simps(2) diff_Suc_less last_index nth_append)


lemma correct_pieces_aux :
  "inc_decL lst \<Longrightarrow>
   hd lst = last lst \<or> hd lst = Suc (last lst) \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   n < length (split lst (last lst)) \<Longrightarrow>
   x = split lst (last lst) ! n \<Longrightarrow>
   \<forall>t \<in> set lst. t \<ge> last lst \<Longrightarrow>
   call_end x (last lst) \<or> const_seq x (last lst)"
apply (induction n arbitrary: x lst)
  apply (simp add: hd_conv_nth hd_good)
apply (case_tac "split lst (last lst)")
apply simp
subgoal for n x lst a rest
using split_split [of lst a rest]
apply simp
apply (cases "length a = length lst")
using split_final [of lst "last lst" a rest]
apply (cases "rest!n = []")
  apply (simp add: const_seq_def)
  apply (meson in_set_conv_nth singleton_iff subsetCE)
apply (cases "length a < length lst")
defer
using split_length apply fastforce
apply simp
proof -
assume a : "(\<And>x lst.
        inc_decL lst \<Longrightarrow>
        hd lst = last lst \<or> hd lst = Suc (last lst) \<Longrightarrow>
        lst \<noteq> [] \<Longrightarrow>
        n < length (split lst (last lst)) \<Longrightarrow>
        x = split lst (last lst) ! n \<Longrightarrow>
        \<forall>x\<in>set lst. last lst \<le> x \<Longrightarrow>
        call_end (split lst (last lst) ! n) (last lst) \<or>
        const_seq (split lst (last lst) ! n)
         (last lst))"
assume b : "inc_decL lst"
show "(\<And>x lst.
        inc_decL lst \<Longrightarrow>
        hd lst = last lst \<or> hd lst = Suc (last lst) \<Longrightarrow>
        lst \<noteq> [] \<Longrightarrow>
        n < length (split lst (last lst)) \<Longrightarrow>
        x = split lst (last lst) ! n \<Longrightarrow>
        \<forall>x\<in>set lst. last lst \<le> x \<Longrightarrow>
        call_end (split lst (last lst) ! n) (last lst) \<or>
        const_seq (split lst (last lst) ! n)
         (last lst)) \<Longrightarrow>
    inc_decL lst \<Longrightarrow>
    hd lst = last lst \<or> hd lst = Suc (last lst) \<Longrightarrow>
    lst \<noteq> [] \<Longrightarrow>
    n < length (split (drop (length a) lst) (last lst)) \<Longrightarrow>
    x = split (drop (length a) lst) (last lst) ! n \<Longrightarrow>
    \<forall>x\<in>set lst. last lst \<le> x \<Longrightarrow>
    split lst (last lst) =
    a # split (drop (length a) lst) (last lst) \<Longrightarrow>
    rest = split (drop (length a) lst) (last lst) \<Longrightarrow>
    length a < length lst \<Longrightarrow>
    call_end (split (drop (length a) lst) (last lst) ! n)
     (last lst) \<or>
    const_seq (split (drop (length a) lst) (last lst) ! n)
     (last lst)"
using a [of "drop (length a) lst" x]
apply simp
apply (cases "inc_decL (drop (length a) lst)")
defer
apply (simp add:inc_decL_def pathR_drop)
apply simp
apply (cases "\<forall>x\<in>set (drop (length a) lst). last lst \<le> x")
defer
  apply (meson in_set_dropD)
apply simp
apply (cases "length a")
  apply (metis drop_0)
using split_last_nth [of lst a rest]
proof -
  fix nat :: nat
  assume a1: "inc_decL lst"
  assume a2: "lst \<noteq> []"
  assume a3: "x = split (drop (length a) lst) (last lst) ! n"
  assume a4: "split lst (last lst) = a # split (drop (length a) lst) (last lst)"
  assume a5: "rest = split (drop (length a) lst) (last lst)"
  assume a6: "length a < length lst"
  assume a7: "hd (drop (length a) lst) = last lst \<or> hd (drop (length a) lst) = Suc (last lst) \<Longrightarrow> call_end (split (drop (length a) lst) (last lst) ! n) (last lst) \<or> const_seq (split (drop (length a) lst) (last lst) ! n) (last lst)"
  assume a8: "\<forall>x\<in>set (drop (length a) lst). last lst \<le> x"
  assume a9: "length a = Suc nat"
  have "\<forall>n. \<not> Suc n \<le> n"
  by (metis le_imp_less_Suc nat_less_le)
  moreover
  { assume "last lst = lst ! Suc nat"
    then have "const_seq x (last lst) \<or> call_end x (last lst)"
      using a9 a7 a6 a3 by (metis (full_types) hd_drop_conv_nth) }
    ultimately show ?thesis
      using a9 a8 a7 a6 a5 a4 a2 a1 by (metis (no_types) Suc_eq_plus1 Suc_less_SucD Suc_pred' \<open>\<lbrakk>split lst (last lst) = a # rest; 0 < length a\<rbrakk> \<Longrightarrow> lst ! (length a - 1) = last lst\<close> drop_eq_Nil hd_drop_conv_nth length_pos_if_in_set list.set_sel(1) nat_less_le not_le test zero_less_Suc)
qed
qed
done

lemma correct_pieces :
  "inc_decL lst \<Longrightarrow>
   hd lst = last lst \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   \<forall>t \<in> set lst. t \<ge> last lst \<Longrightarrow>
   x \<in> set (split lst (last lst)) \<Longrightarrow>
   call_end x (last lst) \<or> const_seq x (last lst)"
using correct_pieces_aux [of lst]
  by (metis in_set_conv_nth)

lemma first_one_smaller_prev :
"inc_decL lst \<Longrightarrow>
 length lst > 0 \<Longrightarrow>
 k > 0 \<Longrightarrow>
 first_one_smaller k lst \<Longrightarrow>
 lst!(k-1) = lst!0"
using first_smaller1 [of lst k]
apply simp
apply (auto simp add: first_one_smaller_def
  first_smaller_def first_def inc_decL_def
  path_defs inc_dec_def path_def sucR_def)
apply (simp add:hd_conv_nth)
  by (smt Suc_less_SucD Suc_pred lessI order.strict_trans)


lemma ncall_last :
  "ncall lst \<Longrightarrow>
   (last (clip (length lst - 2) 1 lst)) = lst!1"
using ncall_stack_length [of lst]
apply (auto simp add:ncall_def clip_def last_conv_nth
  sucR_def)
apply (cases
"min (length lst - Suc 0) (Suc (length lst - 3)) = length lst -2")
apply auto
using first_one_smaller_prev [of "tl lst" "length lst-2"]
apply auto
apply (cases "inc_decL (tl lst)")
defer
apply (simp add:inc_decL_def path_defs path_def)
  apply (metis (no_types, lifting) One_nat_def Suc_diff_Suc Suc_lessD Suc_mono length_tl nth_tl numeral_2_eq_2)
apply auto
  by (metis (no_types, lifting) One_nat_def Suc_diff_Suc diff_Suc_eq_diff_pred diff_less_Suc length_tl less_diff_conv less_numeral_extra(2) neq0_conv nth_tl numeral_2_eq_2 numeral_3_eq_3 one_add_one)


(*
using first_smaller1 [of  "tl lst" "length lst - 2"]
apply (auto simp add:first_smaller_def first_def)
apply (cases "inc_decL (tl lst)")
defer
apply (simp add:inc_decL_def path_defs path_def)
  apply (metis (no_types, lifting) One_nat_def Suc_diff_Suc Suc_lessD Suc_mono length_tl nth_tl numeral_2_eq_2)
apply auto
*)

lemma ncall_inc_dec :
   "ncall lst \<Longrightarrow> inc_decL (clip a b lst)"
by (simp add: ncall_def inc_decL_def pathR_clip)

lemma ncall_sub_length :
"ncall lst \<Longrightarrow> length (clip (length lst - 2) 1 lst) > 0"
by (simp add: ncall_def clip_def)

lemma ncall_second :
"ncall lst \<Longrightarrow> hd (clip (length lst - 2) 1 lst) = lst ! 1"
by (auto simp add: ncall_def clip_def sucR_def
 hd_drop_conv_nth hd_take)

lemma inc_dec_tl : "inc_decL lst \<Longrightarrow> inc_decL (tl lst)"
by (auto simp add: inc_decL_def pathR_tl)

lemma first_smaller_before :
 "first_smaller k lst \<Longrightarrow>
  x \<in> set (take k lst) \<Longrightarrow>
  x \<ge> lst!0"
apply (auto simp add:first_smaller_def first_def)
  by (metis gr_implies_not_zero hd_conv_nth in_set_conv_nth length_take less_imp_le_nat list.size(3) min.absorb2 not_le nth_take)

lemma ncall_inside_big :
"ncall lst \<Longrightarrow>
 x\<in>set (clip (length lst - 2) 1 lst) \<Longrightarrow>
 lst ! 1 \<le> x"
apply (auto simp add:ncall_def sucR_def)
using first_smaller1 [of "tl lst" "length lst - 2"]
apply (auto simp add:inc_dec_tl)
using first_smaller_before [of "length lst -2" "tl lst"
  x]
apply auto
apply (simp add:clip_def)
apply (cases "take (Suc (length lst - 3))
               (drop (Suc 0) lst) = take (length lst - 2) (tl lst)")
defer
  apply (simp add: Suc_diff_Suc drop_Suc numeral_2_eq_2 numeral_3_eq_3)
apply simp
  by (simp add: nth_tl)

definition seqSplit :: "(nat*nat) list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"seqSplit ilst lst =
   map (%ival. take (snd ival) (drop (fst ival) lst)) ilst"


lemma decompose_ncall :
  "ncall lst \<Longrightarrow>
   \<exists>pieces. concat pieces = clip (length lst-2) 1 lst \<and>
   (\<forall>x \<in> set pieces. call_end x (lst!1) \<or> const_seq x (lst!1))"
apply (rule exI[where x =
   "split (clip (length lst-2) 1 lst) (lst!1)"])
apply auto
using split_combine apply fastforce
subgoal for x
using ncall_last [of lst]
apply simp
using correct_pieces [of "clip (length lst-2) 1 lst" x]
apply (simp add:ncall_inc_dec)
apply (cases "clip (length lst - 2) (Suc 0) lst = []")
using ncall_sub_length apply fastforce
apply simp
using ncall_second [of lst]
apply simp
using ncall_inside_big apply force
done
done

definition call_e :: "'a list list \<Rightarrow> 'a list \<Rightarrow> bool" where
"call_e lst s = (
   length lst > 1 \<and>
   (hd lst,s) \<in> tlR  \<and>
   push_popL lst \<and>
   first_return (length lst-1) lst)"

lemma call_end1 :
   "call_e lst s \<Longrightarrow> call_end (map length lst) (length s)"
apply (auto simp add:call_e_def call_end_def tlR_def sucR_def
   hd_map)
  apply (metis Suc_lessE length_Suc_conv list.sel(1) list.simps(9))

  using push_popL_inc_decL apply auto[1]
using first_return_smaller [of "lst" "length lst - 1"]
by (simp add:push_popL_def pathR_tl map_tl)

lemma first_smaller_return2 :
  "push_popL lst \<Longrightarrow>
   first_one_smaller k (map length lst) \<Longrightarrow>
   first_return k lst"
  by (simp add: first_smaller1 first_smaller_return push_popL_inc_decL)

lemma first_return_nil :
  "length lst > 0 \<Longrightarrow>
   first_return k lst \<Longrightarrow>
   length (hd lst) > 0"
by (auto simp add: first_return_def first_def tlR_def)

lemma first_return_get :
  "hd lst = a # list \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   first_return (length lst - 1) lst \<Longrightarrow>
   list = last lst"
apply (auto simp add: first_return_def first_def tlR_def)
  by (simp add: last_conv_nth)


lemma call_end2 :
   "call_end (map length lst) (length s) \<Longrightarrow>
    push_popL lst \<Longrightarrow>
    last lst = s \<Longrightarrow>
    call_e lst s"
apply (auto simp add:call_end_def call_e_def tlR_def sucR_def)
apply (cases "hd lst"; auto)
  apply (metis Suc_lessD length_greater_0_conv list.map_sel(1) list.size(3) nat.distinct(1))
using first_smaller_return2 [of lst "length lst - 1"]
apply simp
using first_return_get apply force
using first_smaller_return2 [of lst "length lst - 1"]
apply force
done

lemma split_and_combine2 :
   "concat (indexSplit ilst lst) = lst"
by (induction ilst lst rule:indexSplit.induct; auto)

lemma decompose_ncall_index :
  "ncall lst \<Longrightarrow>
   \<exists>ilst. (\<forall>x \<in> set (indexSplit ilst (clip (length lst-2) 1 lst)).
    call_end x (lst!1) \<or> const_seq x (lst!1))"
apply (rule exI[where x =
   "findIndices (clip (length lst-2) 1 lst) (lst!1)"])
apply auto
subgoal for x
using ncall_last [of lst]
apply simp
using correct_pieces [of "clip (length lst-2) 1 lst" x]
apply (simp add:ncall_inc_dec)
apply (cases "clip (length lst - 2) (Suc 0) lst = []")
using ncall_sub_length apply fastforce
apply simp
using ncall_second [of lst]
apply (simp add:split_def)
using ncall_inside_big apply force
done
done

lemma index_split_map :
"x \<in> set (indexSplit ilst lst) \<Longrightarrow>
 map f x \<in> set (indexSplit ilst (map f lst))"
by (induction ilst lst arbitrary:x rule:indexSplit.induct;
    auto simp add: take_map drop_map)

lemma const_seq_convert :
  "push_popL lst \<Longrightarrow>
   const_seq (map length lst) n \<Longrightarrow>
   \<exists>t. const_seq lst t"
apply (cases lst)
apply (auto simp add:const_seq_def)
subgoal for a list x
apply (induction list arbitrary: x a lst n)
apply (auto simp add:push_popL_def pathR.simps
  push_pop_def)
  apply (metis PathRel.take_all Un_upper2 converseD converse_converse le_refl next_unchanged push_pop_def subset_iff)
  apply (metis PathRel.take_all Un_upper2 converseD converse_converse le_refl next_unchanged push_pop_def subset_iff)
  apply (metis (mono_tags, lifting) PathRel.take_all converse.intros le_refl next_unchanged push_pop_def set_mp sup.cobounded2)
  apply (metis (mono_tags, lifting) PathRel.take_all converse.intros le_refl next_unchanged push_pop_def set_mp sup.cobounded2)
done done

lemma index_split_get :
"x \<in> set (indexSplit ilst lst) \<Longrightarrow>
 \<exists>a b. x = take a (drop b lst)"
apply (induction ilst lst arbitrary:x rule:indexSplit.induct)
apply auto
  apply (metis drop_0)
  apply metis
  by (metis List.take_all drop_0 le_add2)

lemma pathR_split :
   "pathR r lst \<Longrightarrow>
    x \<in> set (indexSplit ilst lst) \<Longrightarrow>
    pathR r x"
using index_split_get pathR_take pathR_drop
  by blast

lemma call_pathR : "call lst \<Longrightarrow> pathR push_pop lst"
by (auto simp: call_def push_popL_def)

lemma call_inside_pushpopL : 
  "call lst \<Longrightarrow> push_popL (clip (length lst - 2) 1 lst)"
by (simp add:call_def push_popL_def pathR_clip)

lemma foo_aux2 :
"j < length lst - 1 \<Longrightarrow>
 sti \<in> set (take j (drop (Suc 0) lst)) \<Longrightarrow>
 sti \<in> set (take (length lst - 2) (drop (Suc 0) lst))"
using List.set_take_subset_set_take [of j "length lst-2"
  "drop (Suc 0) lst"]
apply auto
apply (cases "length lst")
apply auto
  by fastforce

lemma foo_aux :
"j < length lst - 1 \<Longrightarrow>
 sti \<in> set (take j (drop (Suc 0) lst)) \<Longrightarrow>
 length sti
    \<in> length `
       set
        (take (length lst - 2) (drop (Suc 0) lst))"
using foo_aux2 [of j lst sti]
  by blast

lemma call_inside_big_idx :
"call lst \<Longrightarrow>
 j \<ge> 1 \<Longrightarrow> j < length lst - 1 \<Longrightarrow>
 takeLast (length (lst!1)) (lst!j) = lst ! 1"
using stack_unchanged [of "clip j 1 lst"
   "length (lst!1)"]
apply simp
apply (cases "push_popL (clip j (Suc 0) lst)")
defer
apply (simp add:call_def push_popL_def pathR_clip)
apply (cases "clip j (Suc 0) lst = []")
apply (simp add:clip_def call_def)
apply (simp add:last_clip hd_clip)
apply (subgoal_tac "\<forall>sti\<in>set (clip j (Suc 0) lst).
        length (lst ! Suc 0) \<le> length sti")
apply simp
apply auto
  apply (metis (mono_tags, lifting) Nitpick.size_list_simp(2) One_nat_def PathRel.take_all hd_clip last_clip le_less length_tl less_SucI nat_diff_split zero_less_one)

subgoal for sti
using ncall_inside_big [of "map length lst" "length sti"]
apply (simp add:call_ncall)
apply (cases "length sti
     \<in> set (clip (length (map length lst) - 2) (Suc 0)
              (map length lst))")
apply auto
  apply (simp add: clip_def drop_map take_map)
apply (cases "Suc (length lst - 3) = length lst - 2")
defer
apply (simp)
apply simp
using foo_aux apply fastforce
done
done

lemma ex_idx : "x \<in> set lst \<Longrightarrow> \<exists>i<length lst. x = lst!i"
  by (metis in_set_conv_nth)

lemma call_inside_big :
"call lst \<Longrightarrow>
 x\<in>set (clip (length lst - 2) 1 lst) \<Longrightarrow>
 takeLast (length (lst!1)) x = lst ! 1"
using ex_idx [of x "clip (length lst - 2) 1 lst"]
apply auto
subgoal for j
using call_inside_big_idx [of lst "Suc j"]
apply (simp add:clip_def)
apply (subgoal_tac "Suc j < length lst - Suc 0")
apply simp
  by (metis One_nat_def Suc_diff_Suc Suc_lessI call_def diff_Suc_1 diff_diff_left nat_neq_iff numeral_2_eq_2 numeral_3_eq_3 one_add_one)
done

lemma const_seq_empty : "const_seq [] x"
by (simp add:const_seq_def)

lemma const_seq_eq : "const_seq (a # list) b \<Longrightarrow> b = a"
by (simp add:const_seq_def)

lemma in_index_split :
"x \<in> set (indexSplit ilst lst) \<Longrightarrow>
 y \<in> set x \<Longrightarrow>
 y \<in> set lst"
  by (metis in_set_dropD in_set_takeD index_split_get)

lemma call_end_last : "call_end lst x \<Longrightarrow> last lst = x"
apply (auto simp add:call_end_def)
  by (metis (mono_tags, lifting) One_nat_def Suc_lessD diff_Suc_1 first_def first_one_smaller_def last_index)

(* decompose call to sub calls ...
   cycle could also be split into subcycles *)
lemma decompose_call :
  "call lst \<Longrightarrow>
   \<exists>ilst. (\<forall>x \<in> set (indexSplit ilst (clip (length lst-2) 1 lst)).
    call_e x (lst!1) \<or> const_seq x (lst!1))"
using decompose_ncall_index [of "map length lst"]
      call_ncall [of lst]
apply auto
subgoal for ilst
apply (rule exI[where x=ilst])
apply clarsimp
(* because internally the stack is high,
   it should not change *)
apply (case_tac "const_seq (map length x) (map length lst ! Suc 0) \<or>
    call_end (map length x) (map length lst ! Suc 0)")
defer
subgoal for x
using index_split_map [of x ilst "clip (length lst - 2) (Suc 0)
                 lst" length]
apply (simp add:clip_def take_map drop_map)
apply force
done
subgoal for x
using pathR_split [of "push_pop"
   "clip (length lst - 2) (Suc 0) lst" x ilst]
  pathR_clip [of "push_pop" lst "length lst-2" "Suc 0"]
  call_pathR [of lst]
apply simp

apply auto
subgoal (* constant *)
using const_seq_convert [of x "map length lst ! Suc 0"]
apply (auto simp add:push_popL_def)
apply (cases x)
using const_seq_empty apply force
subgoal for xa a list
apply (simp add:map_nth)
using const_seq_eq [of a list xa]
apply simp
apply (subgoal_tac "a \<in> set (clip (length lst - 2) (Suc 0) lst)")
defer
using in_index_split apply fastforce
apply (subgoal_tac "lst ! Suc 0 = a")
apply auto
using call_inside_big [of lst a]
  by (metis One_nat_def PathRel.take_all Suc_lessD call_def const_seq_eq nth_map numeral_2_eq_2)
done
apply (rule call_end2)
  apply (simp add: call_def)
  using push_popL_def apply blast
using call_end_last [of "map length x" "length (lst ! Suc 0)"]
using call_inside_big [of lst "last x"]
apply simp
  by (smt One_nat_def PathRel.take_all Suc_lessD call_def call_end_def diff_less in_index_split last_index length_map nth_map nth_mem numeral_2_eq_2 zero_less_one)
done done

definition ncall_pieces :: "nat list \<Rightarrow> nat list list" where
"ncall_pieces lst =
  (let ilst =  findIndices (clip (length lst-2) 1 lst) (lst!1) in
   indexSplit ilst (clip (length lst-2) 1 lst))"

lemma decompose_ncall_pieces :
  "ncall lst \<Longrightarrow>
   x \<in> set (ncall_pieces lst) \<Longrightarrow>
   call_end x (lst!1) \<or> const_seq x (lst!1)"
apply (simp add:ncall_pieces_def)
apply auto
using ncall_last [of lst]
apply simp
using correct_pieces [of "clip (length lst-2) 1 lst" x]
apply (simp add:ncall_inc_dec)
apply (cases "clip (length lst - 2) (Suc 0) lst = []")
using ncall_sub_length apply fastforce
apply simp
using ncall_second [of lst]
apply (simp add:split_def)
using ncall_inside_big apply force
done

definition call_pieces :: "'a list list \<Rightarrow> 'a list list list" where
"call_pieces lst =
  (let ilst = findIndices (clip (length lst-2) 1 (map length lst)) (length (lst!1)) in
   indexSplit ilst (clip (length lst-2) 1 lst))"


lemma lengths_aux :
"length lst > 1 \<Longrightarrow>
 x \<in> set (call_pieces lst) \<Longrightarrow>
 map length x \<in> set (ncall_pieces (map length lst))"
apply (subgoal_tac "map length lst ! 1 = length (lst!1)")
apply (auto simp add: clip_def drop_map index_split_map take_map
  call_pieces_def ncall_pieces_def)
done

(*
lemma lengths_aux :
"length lst > 1 \<Longrightarrow>
 x \<in> set (indexSplit
               (findIndices
                 (clip (length lst - 2)
                   (Suc 0) (map length lst))
                 (length (lst ! Suc 0)))
               (clip (length lst - 2) (Suc 0)
                 lst)) \<Longrightarrow>
    map length x
     \<in> set (indexSplit
              (findIndices
                (clip (length lst - 2)
                  (Suc 0) (map length lst))
                (map length lst ! Suc 0))
              (clip (length lst - 2) (Suc 0)
                (map length lst)))"
apply (subgoal_tac "map length lst ! 1 = length (lst!1)")
apply (auto simp add: clip_def drop_map index_split_map take_map)
done
*)

lemma decompose_call_pieces :
  "call lst \<Longrightarrow>
   x \<in> set (call_pieces lst) \<Longrightarrow>
   call_e x (lst!1) \<or> const_seq x (lst!1)"
using decompose_ncall_pieces [of "map length lst" "map length x"]
      call_ncall [of lst]
apply (case_tac "const_seq (map length x) (map length lst ! Suc 0) \<or>
    call_end (map length x) (map length lst ! Suc 0)")
apply (simp add:call_pieces_def)
using pathR_split [of "push_pop"
   "clip (length lst - 2) (Suc 0) lst" x "findIndices
                 (clip (length lst - 2)
                   (Suc 0) (map length lst))
                 (length (lst ! Suc 0))"]
  pathR_clip [of "push_pop" lst "length lst-2" "Suc 0"]
  call_pathR [of lst]
apply simp

apply auto
subgoal (* constant *)
using const_seq_convert [of x "map length lst ! Suc 0"]
apply (auto simp add:push_popL_def)
apply (cases x)
using const_seq_empty apply force
subgoal for xa a list
apply (simp add:map_nth)
using const_seq_eq [of a list xa]
apply simp
apply (subgoal_tac "a \<in> set (clip (length lst - 2) (Suc 0) lst)")
defer
using in_index_split apply fastforce
apply (subgoal_tac "lst ! Suc 0 = a")
apply auto
using call_inside_big [of lst a]
  by (metis One_nat_def PathRel.take_all Suc_lessD call_def const_seq_eq nth_map numeral_2_eq_2)
done
apply (rule call_end2)
  apply (simp add: call_def)
  using push_popL_def apply blast
using call_end_last [of "map length x" "length (lst ! Suc 0)"]
using call_inside_big [of lst "last x"]
apply simp
  apply (metis PathRel.take_all Suc_lessD call_def call_end_def in_index_split last_in_set last_map length_map less_numeral_extra(2) list.size(3) nth_map numeral_2_eq_2)
using lengths_aux [of lst x]
apply simp
  by (simp add: call_def less_imp_le_nat)


lemma sucR_add : "(a,b) \<in> sucR \<Longrightarrow> (a+m,b+m) \<in> sucR"
by (simp add:sucR_def)

lemma inc_dec_add : "(a,b) \<in> inc_dec \<Longrightarrow> (a+m,b+m) \<in> inc_dec"
by (simp add:inc_dec_def sucR_def)

lemma pathR_map :
  "(\<forall>a b. (a,b) \<in> r \<longrightarrow> (f a, f b) \<in> r) \<Longrightarrow>
    pathR r lst \<Longrightarrow> pathR r (map f lst)"
by (simp add:path_defs path_def)

lemma tl_map : "tl (map f lst) = map f (tl lst)"
  by (simp add: map_tl)

lemma ncall_plus : "ncall lst \<Longrightarrow> ncall (map (%a. a +m) lst)"
apply (auto simp: ncall_def)
apply (simp add:sucR_def)
  using less_iff_Suc_add apply auto[1]
apply (simp add:inc_decL_def)
apply (rule pathR_map)
apply (auto simp add:inc_dec_add)
apply (auto simp add:first_one_smaller_def first_def)
apply (simp add:tl_map hd_map)
  apply (metis add_Suc length_tl less_diff_conv less_numeral_extra(2) list.map_sel(1) list.size(3) one_add_one)
apply (simp add:tl_map hd_map)
apply (subgoal_tac "hd (map (\<lambda>a. a + m) (tl lst)) = hd (tl lst) + m")
apply simp
  by (metis length_tl less_diff_conv less_numeral_extra(2) list.map_sel(1) list.size(3) one_add_one)

end
