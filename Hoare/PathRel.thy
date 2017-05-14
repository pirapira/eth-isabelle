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

lemma list_all_value :
   "inc_decL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    min (hd lst) (last lst) \<le> x \<Longrightarrow>
    x \<le> max (hd lst) (last lst) \<Longrightarrow>
    \<exists>i. lst!i = x"
apply (induction lst)
apply (auto simp add:inc_decL_def)
apply (case_tac lst)
apply auto
  apply (meson nth_Cons_0)
apply (auto simp: inc_dec_def sucR_def)
  apply (meson nth_Cons_Suc)
subgoal proof -
  fix aa :: nat and list :: "nat list"
  assume a1: "\<lbrakk>min aa (if list = [] then aa else last list) \<le> x; x \<le> max aa (if list = [] then aa else last list)\<rbrakk> \<Longrightarrow> \<exists>i. (aa # list) ! i = x"
  assume a2: "min (Suc aa) (if list = [] then aa else last list) \<le> x"
  assume a3: "x \<le> max (Suc aa) (if list = [] then aa else last list)"
  obtain nn :: nat where
    f4: "\<not> min aa (if list = [] then aa else last list) \<le> x \<or> \<not> x \<le> max aa (if list = [] then aa else last list) \<or> (aa # list) ! nn = x"
    using a1 by metis
  have f5: "Suc aa \<le> (if list = [] then aa else last list) \<or> x \<le> Suc aa"
    using a3 by (metis max_def)
  have f6: "\<forall>n. min n (min (Suc aa) (if list = [] then aa else last list)) \<le> x"
    using a2 by (metis min.coboundedI2)
  have f7: "\<not> Suc aa \<le> (if list = [] then aa else last list) \<or> Suc aa \<le> x"
    using a2 by linarith
  have f8: "Suc aa \<le> aa \<or> list \<noteq> [] \<or> x \<le> Suc aa"
    using a3 by force
  have f9: "\<forall>n. \<not> n \<le> min (Suc aa) (if list = [] then aa else last list) \<or> n \<le> x"
    using f6 by (metis min_def)
  have f10: "(if list = [] then aa else last list) \<le> aa \<or> x \<le> (if list = [] then aa else last list)"
    using a3 by linarith
  have f11: "(if list = [] then aa else last list) \<le> x \<or> aa \<le> (if list = [] then aa else last list)"
    using a2 by linarith
  { assume "Suc (last list) \<le> aa"
    then have "\<not> aa \<le> last list"
      by (metis not_less_eq_eq)
    moreover
    { assume "\<exists>n. \<not> aa \<le> last list \<and> \<not> min n (last list) \<le> x"
      then have "\<not> aa \<le> (if False then aa else last list) \<and> \<not> last list \<le> x"
        by (meson min.coboundedI2)
      then have "list = []"
        using f11 by presburger }
    ultimately have "x \<le> aa \<longrightarrow> x \<le> aa \<and> min aa (if list = [] then aa else last list) \<le> x \<and> \<not> aa \<le> (if list = [] then aa else last list) \<or> list = []"
      by presburger }
  moreover
  { assume "\<not> Suc (if False then aa else last list) \<le> aa"
    moreover
    { assume "\<not> Suc (if list = [] then aa else last list) \<le> aa"
      moreover
      { assume "\<exists>n. \<not> min aa n \<le> x"
        moreover
        { assume "Suc aa \<le> last list"
          then have "x \<le> aa \<longrightarrow> list = []"
            using f7 not_less_eq_eq by presburger }
        ultimately have "x \<le> aa \<longrightarrow> x \<le> aa \<and> min aa (if list = [] then aa else last list) \<le> x \<and> \<not> aa \<le> (if list = [] then aa else last list) \<or> list = []"
          using f9 by force }
      moreover
      { assume "min aa (if list = [] then aa else last list) \<le> x \<and> \<not> Suc (if list = [] then aa else last list) \<le> aa"
        moreover
        { assume "\<exists>n. \<not> n \<le> aa \<and> n \<le> x"
          then have "\<not> x \<le> aa"
            by (metis min.coboundedI2 min_def) }
        ultimately have "x \<le> aa \<longrightarrow> aa \<le> (if list = [] then aa else last list) \<and> min aa (if list = [] then aa else last list) \<le> x \<and> x \<le> (if list = [] then aa else last list)"
          by (meson not_less_eq_eq) }
      ultimately have "x \<le> aa \<longrightarrow> aa \<le> (if list = [] then aa else last list) \<and> min aa (if list = [] then aa else last list) \<le> x \<and> x \<le> (if list = [] then aa else last list) \<or> x \<le> aa \<and> min aa (if list = [] then aa else last list) \<le> x \<and> \<not> aa \<le> (if list = [] then aa else last list) \<or> list = []"
        by blast }
    ultimately have "x \<le> aa \<longrightarrow> aa \<le> (if list = [] then aa else last list) \<and> min aa (if list = [] then aa else last list) \<le> x \<and> x \<le> (if list = [] then aa else last list) \<or> x \<le> aa \<and> min aa (if list = [] then aa else last list) \<le> x \<and> \<not> aa \<le> (if list = [] then aa else last list) \<or> list = []"
      by force }
  moreover
  { assume "\<not> x \<le> aa"
    then have "list = [] \<or> aa \<le> (if list = [] then aa else last list) \<and> min aa (if list = [] then aa else last list) \<le> x \<and> x \<le> (if list = [] then aa else last list) \<or> (\<exists>n. x = n \<and> \<not> n \<le> aa \<and> n \<le> Suc aa)"
      using f10 f5 by (metis (no_types) min.coboundedI1 nat_le_linear not_less_eq_eq) }
  moreover
  { assume "list = []"
    moreover
    { assume "x \<le> aa \<and> min aa (if list = [] then aa else last list) \<le> x \<and> list = []"
      moreover
      { assume "aa \<le> aa \<and> list = [] \<and> min aa (if list = [] then aa else last list) \<le> x"
        then have "x \<le> max aa (if True then aa else last list) \<and> min aa (if list = [] then aa else last list) \<le> x \<and> list = [] \<or> (\<exists>n. x = n \<and> \<not> n \<le> aa \<and> n \<le> Suc aa)"
          using f8 by force }
      ultimately have "(\<exists>n. x = n \<and> \<not> n \<le> aa \<and> n \<le> Suc aa) \<or> (\<exists>n. (aa # list) ! n = x)"
        using f4 by force }
    ultimately have "(\<exists>n. x = n \<and> \<not> n \<le> aa \<and> n \<le> Suc aa) \<or> (\<exists>n. (aa # list) ! n = x)"
      using a3 a2 by force }
  moreover
  { assume "\<exists>n. x = n \<and> \<not> n \<le> aa \<and> n \<le> Suc aa"
    then have "\<exists>n. (Suc aa # aa # list) ! n = x"
      by (metis le_SucE nth_Cons_0) }
  ultimately show "\<exists>n. (Suc aa # aa # list) ! n = x"
    using f4 by (metis max_def nth_Cons_Suc)
qed
proof -
  fix a :: nat and list :: "nat list"
  assume a1: "min a (if list = [] then Suc a else last list) \<le> x"
  assume a2: "x \<le> max a (if list = [] then Suc a else last list)"
  assume a3: "\<lbrakk>min (Suc a) (if list = [] then Suc a else last list) \<le> x; x \<le> max (Suc a) (if list = [] then Suc a else last list)\<rbrakk> \<Longrightarrow> \<exists>i. (Suc a # list) ! i = x"
  have f4: "\<And>n. min x n \<le> max a (if list = [] then Suc a else last list)"
    using a2 by (metis min.coboundedI1)
  then have f5: "\<And>n. x \<le> n \<or> n \<le> max a (if list = [] then Suc a else last list)"
    by (metis min_def)
  then have f6: "x \<le> Suc (max a (if list = [] then Suc a else last list))"
    by (metis not_less_eq_eq order_refl)
  obtain nn :: nat where
    f7: "\<not> x \<le> max (Suc a) (if list = [] then Suc a else last list) \<or> \<not> min (Suc a) (if list = [] then Suc a else last list) \<le> x \<or> (Suc a # list) ! nn = x"
    using a3 by blast
  then have f8: "\<not> x \<le> max (Suc a) (if list = [] then Suc a else last list) \<or> \<not> (if list = [] then Suc a else last list) \<le> x \<or> Suc a \<le> (if list = [] then Suc a else last list) \<or> (Suc a # list) ! nn = x"
    by (metis min_def)
  then have f9: "\<not> x \<le> Suc a \<or> \<not> (if list = [] then Suc a else last list) \<le> x \<or> Suc a \<le> (if list = [] then Suc a else last list) \<or> Suc a \<le> (if list = [] then Suc a else last list) \<or> (Suc a # list) ! nn = x"
    by (metis max_def)
  have f10: "\<not> Suc a \<le> x \<or> \<not> x \<le> Suc a \<or> Suc a \<le> (if list = [] then Suc a else last list) \<or> (Suc a # list) ! nn = x"
    using f7 by (metis (no_types) max_def min.coboundedI1)
  have f11: "\<not> Suc a \<le> (if list = [] then Suc a else last list) \<or> \<not> Suc a \<le> x \<or> \<not> x \<le> (if list = [] then Suc a else last list) \<or> (Suc a # list) ! nn = x"
    using f7 by (metis (no_types) max_def min.coboundedI1)
  { assume "x \<noteq> a"
    then have "Suc x \<noteq> Suc a"
      by blast
    moreover
    { assume "Suc a \<le> x"
      moreover
      { assume "x \<le> Suc a \<and> Suc a \<le> x"
        then have "(if list = [] then Suc a else last list) \<le> a \<and> \<not> a \<le> (if list = [] then Suc a else last list) \<or> Suc a \<le> (if list = [] then Suc a else last list) \<and> Suc a \<le> x \<and> x \<le> (if list = [] then Suc a else last list) \<or> Suc a \<le> x \<and> x \<le> Suc a \<and> \<not> Suc a \<le> (if list = [] then Suc a else last list)"
          using a2 by (metis (no_types) max_def not_less_eq_eq)
        then have "(if list = [] then Suc a else last list) \<le> a \<and> \<not> a \<le> (if list = [] then Suc a else last list) \<or> (\<exists>n. (Suc a # list) ! n = x)"
          using f11 f10 by blast }
      moreover
      { assume "\<not> x \<le> Suc a"
        moreover
        { assume "\<not> (if list = [] then Suc a else last list) \<le> a \<and> \<not> x \<le> Suc a"
          then have "Suc a \<le> (if list = [] then Suc a else last list) \<and> \<not> x \<le> Suc a"
            by (metis not_less_eq_eq)
          moreover
          { assume "Suc a \<le> (if list = [] then Suc a else last list) \<and> Suc a \<le> (if list = [] then Suc a else last list) \<and> x \<le> (if list = [] then Suc a else last list) \<and> \<not> x \<le> Suc a"
            then have "x \<le> max (Suc a) (if list = [] then Suc a else last list) \<and> min (Suc a) (if list = [] then Suc a else last list) \<le> x"
              by linarith
            then have "\<exists>n. (Suc a # list) ! n = x"
              using f7 by metis }
          ultimately have "(if list = [] then Suc a else last list) \<le> a \<and> \<not> a \<le> (if list = [] then Suc a else last list) \<or> (\<exists>n. (Suc a # list) ! n = x)"
            using f4 by (metis (no_types) max_def min_def) }
        ultimately have "(if list = [] then Suc a else last list) \<le> a \<and> \<not> a \<le> (if list = [] then Suc a else last list) \<or> (\<exists>n. (Suc a # list) ! n = x)"
          using f5 by (metis (no_types) max_def not_less_eq_eq) }
      ultimately have "\<exists>n. (Suc a # list) ! n = x"
        using f9 f6 a1 by (metis (no_types) max_def min_def not_less_eq_eq) }
    moreover
    { assume "\<not> Suc a \<le> x \<and> Suc x \<noteq> Suc a"
      then have "Suc x \<le> a"
        by (meson le_SucE not_less_eq_eq)
      then have "Suc x \<le> a \<and> list \<noteq> []"
        using a1 min_def by auto
      then have "last list \<le> a \<and> \<not> a \<le> last list \<and> list \<noteq> []"
        using a1 by force
      then have "x \<le> max (Suc a) (last list) \<and> last list \<le> x \<and> list \<noteq> [] \<and> \<not> Suc a \<le> last list"
        using f6 a1 by (simp add: max_def min_def)
      then have "\<exists>n. (Suc a # list) ! n = x"
        using f8 by auto }
    ultimately have "\<exists>n. (a # Suc a # list) ! n = x"
      by (metis (full_types) nth_Cons_Suc) }
  then show "\<exists>n. (a # Suc a # list) ! n = x"
    by (metis (no_types) nth_Cons_0)
qed

definition hd_last :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"hd_last lst a b = (hd lst = a \<and> last lst = b \<and> length lst > 0)"

lemma list_all_values :
   "inc_decL lst \<Longrightarrow>
    length lst > 0 \<Longrightarrow>
    min (hd lst) (last lst) \<le> x \<Longrightarrow>
    x \<le> max (hd lst) (last lst) \<Longrightarrow>
    x \<in> set lst"
apply (induction lst)
apply (auto simp add:inc_decL_def inc_dec_def sucR_def)
apply (case_tac lst; auto)
  using le_less min_le_iff_disj sup.cobounded2 sup_nat_def apply fastforce
  by fastforce

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

end
