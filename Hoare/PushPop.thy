theory PushPop
imports Main
begin

(* can only push or pop one element at a time *)

type_synonym 'a rel = "'a \<Rightarrow> 'a \<Rightarrow> bool"

type_synonym 'a lrel = "'a list rel"

definition urel :: "'a rel \<Rightarrow> bool" where
"urel r == (\<forall>a b c. r a b \<longrightarrow> r a c \<longrightarrow> b = c)"

fun iterR :: "nat \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"iterR 0 r = (\<lambda>x y. x = y)"
| "iterR (Suc n) r = (\<lambda>x y. \<exists>z. r x z \<and> iterR n r z y)"

fun starR :: "'a rel \<Rightarrow> 'a rel" where
"starR r = (\<lambda>x y. \<exists>n. iterR n r x y)"

lemma iter_urel : "urel r \<Longrightarrow> urel (iterR n r)"
apply (induction n)
apply (auto simp add:urel_def)
apply metis
done

lemma apply_urel :
  "urel r \<Longrightarrow>
   r a b \<Longrightarrow>
   r a c \<Longrightarrow> b = c"
by (simp add:urel_def)

lemma iter_last :
  "iterR (Suc n) r x y =
  (\<exists>z. iterR n r x z \<and> r z y)"
by (induction n arbitrary: x; auto)

lemma iter_add1 :
   "urel r \<Longrightarrow>
    iterR (n+k) r x y \<Longrightarrow>
    iterR n r x z \<Longrightarrow>
    iterR k r z y"
apply (induction k arbitrary: x z n y)
apply (simp)
using iter_urel apply_urel apply force
  by (metis add_Suc_right iter_last)

lemma iter_add :
   "iterR (n+k) r x y =
    (\<exists>z. iterR n r x z \<and> iterR k r z y)"
apply (induction k arbitrary: x n y, simp)
by (smt add_Suc iter_last semiring_normalization_rules(24))

definition takeLast :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"takeLast n lst = rev (take n (rev lst))"

lemma takeLast_drop :
  "takeLast n lst = drop (length lst - n) lst"
apply (induction lst arbitrary:n)
apply (auto simp add:takeLast_def)
  by (metis length_Cons length_rev rev.simps(2) rev_append rev_rev_ident take_append take_rev)

(* intermediate length: relation for naturals *)

definition push_pop :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> bool" where
"push_pop r f ==
  (\<forall>a b. r a b \<longrightarrow> f a = f b \<or> tl (f a) = f b \<or> f a = tl (f b))"

definition inc_dec :: "'a rel \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
"inc_dec r f ==
  (\<forall>a b. r a b \<longrightarrow> f a = f b \<or> f a = Suc (f b) \<or> Suc (f a) = f b)"

lemma push_pop_inc_dec :
   "push_pop r f \<Longrightarrow>
    inc_dec r (\<lambda>a. length (f a))"
apply (auto simp: push_pop_def inc_dec_def)
  by (metis Nitpick.size_list_simp(2) tl_Nil)

lemma all_values_aux :
  "(min (f z) (f b) \<le> x \<Longrightarrow>
          x \<le> max (f z) (f b) \<Longrightarrow>
          iterR k r z b \<Longrightarrow>
          \<exists>c k1.
             iterR k1 r z c \<and> k1 \<le> k \<and> f c = x) \<Longrightarrow>
    inc_dec r f \<Longrightarrow>
    min (f aa) (f b) \<le> x \<Longrightarrow>
    x \<le> max (f aa) (f b) \<Longrightarrow>
    r aa z \<Longrightarrow>
    iterR k r z b \<Longrightarrow>
    \<exists>c k1. iterR k1 r aa c \<and> k1 \<le> Suc k \<and> f c = x"
apply (cases "f aa = f z")
apply force
apply (cases "f aa = Suc (f z)")
apply force
apply (cases "Suc (f aa) = f z")
apply force
apply (metis inc_dec_def)
done

lemma all_values :
  "inc_dec r f \<Longrightarrow>
   min (f a) (f b) \<le> x \<Longrightarrow>
   x \<le> max (f a) (f b) \<Longrightarrow>
   iterR k r a b \<Longrightarrow>
   \<exists>c k1. iterR k1 r a c \<and> k1 \<le> k \<and> f c = x"
apply (induction k arbitrary: a, simp)
apply auto
subgoal for k aa z
using all_values_aux [of f z b x k r aa]
by force
done

(* stack length smaller, bottom stays equal *)

lemma next_unchanged :
  "push_pop r f \<Longrightarrow>
   r st1 st2 \<Longrightarrow>
   l \<le> length (f st2) \<Longrightarrow>
   l \<le> length (f st1) \<Longrightarrow>
   takeLast l (f st2) = takeLast l (f st1)"
apply (simp add:takeLast_def)
apply (cases "f st1 = f st2")
apply force
apply (cases "f st1 = tl (f st2)")
apply simp
  apply (smt diff_Suc_eq_diff_pred drop_Suc length_tl min.absorb1 rev_drop take_take)
apply (cases "f st2 = tl (f st1)")
apply simp
  apply (smt diff_Suc_eq_diff_pred drop_Suc length_tl min.absorb1 rev_drop take_take)
apply (metis push_pop_def)
done

lemma stack_unchanged_split :
  "iterR (Suc k) r st1 st2 \<Longrightarrow>
   \<exists>st3. r st1 st3 \<and>
     (takeLast l (f st2) = takeLast l (f st3) \<and>
     takeLast l (f st3) = takeLast l (f st1)) \<Longrightarrow>
   takeLast l (f st2) = takeLast l (f st1)"
by auto

lemma ex_and :
"\<exists>st3. P st3 \<Longrightarrow>
 \<forall>st. (P st \<longrightarrow> Q st) \<Longrightarrow> 
 \<exists>st3. P st3 \<and> Q st3"
by auto

lemma funny :
   "\<forall>sti k1.
             k1 \<le> Suc k \<longrightarrow>
             iterR k1 r st3 sti \<longrightarrow>
             l \<le> length (f sti) \<Longrightarrow>
    r st3 st \<Longrightarrow> l \<le> length (f st)"
apply (drule spec2[where x="st" and y = "Suc 0"])
apply auto
done

lemma Spec : 
  "(\<And>st. R st \<Longrightarrow> P st \<Longrightarrow> Q st) \<Longrightarrow>
   R x \<Longrightarrow> P x \<Longrightarrow> Q x"
by auto

lemma stack_unchanged :
  "iterR k r st1 st2 \<Longrightarrow>
   push_pop r f \<Longrightarrow>
   (\<forall>sti. \<forall>k1 \<le> k. iterR k1 r st1 sti \<longrightarrow>
                   l \<le> length (f sti) ) \<Longrightarrow>
   takeLast l (f st2) = takeLast l (f st1)"
apply (induction k arbitrary:st1, simp)
apply auto
subgoal for k st3 z
apply (rule stack_unchanged_split [of k r st3 st2 l f])
apply auto
apply (rule exI [where x=z])
apply auto
apply (drule Spec[where R="\<lambda>st1. iterR k r st1 st2"
   and P="\<lambda>st1. \<forall>sti k1. k1 \<le> k \<longrightarrow> iterR k1 r st1 sti \<longrightarrow> l \<le> length (f sti)"
   and x="z"], auto)
apply fastforce
apply (rule next_unchanged [of r f], auto)
apply (drule spec2[where x="z" and y = "Suc 0"], auto)
apply (drule spec2[where x="st3" and y = "0"], auto)
done done

(* find returns *)

lemma what :
   "length (f st2) \<le> length (f z) - Suc 0 \<Longrightarrow>
    length (f st2) \<le> length (f z)"
by auto

lemma find_return_aux :
"( iterR k r z st2 \<Longrightarrow>
        length (f st2) \<le> length (f z) \<Longrightarrow>
        \<exists>st3 k3.
           k3 \<le> k \<and>
           iterR k3 r z st3 \<and>
           f st3 =
           takeLast (length (f st2)) (f z)) \<Longrightarrow>
    push_pop r f \<Longrightarrow>
    length (f st2) \<le> length (f st) \<Longrightarrow>
    r st z \<Longrightarrow>
    iterR k r z st2 \<Longrightarrow>
    \<exists>st3 k3.
       k3 \<le> Suc k \<and>
       iterR k3 r st st3 \<and>
       f st3 = takeLast (length (f st2)) (f st)"
apply (cases "f st = f z")
apply auto
apply force
apply (cases "f st = tl (f z)")
apply auto
subgoal
using what [of f st2 z]
apply auto
  using iterR.simps(2) next_unchanged apply fastforce
done
apply (cases "f z = tl (f st)")
apply auto
apply (cases "length (f st2) = length (f st)")
apply auto
  apply (metis (mono_tags) diff_zero drop_0 iterR.simps(1) le0 rev_drop rev_swap takeLast_def)
subgoal proof -
  assume a1: "length (f st2) \<le> length (f st) - Suc 0 \<Longrightarrow> \<exists>st3 k3. k3 \<le> k \<and> iterR k3 r z st3 \<and> f st3 = takeLast (length (f st2)) (tl (f st))"
  assume a2: "push_pop r f"
  assume a3: "length (f st2) \<le> length (f st)"
  assume a4: "r st z"
  assume a5: "f st \<noteq> tl (f st)"
  assume a6: "f z = tl (f st)"
  assume a7: "length (f st2) \<noteq> length (f st)"
  obtain nn :: nat and aa :: 'a where
    f8: "\<not> length (f st2) \<le> length (f st) - Suc 0 \<or> nn \<le> k \<and> iterR nn r z aa \<and> takeLast (length (f st2)) (tl (f st)) = f aa"
    using a1 by (metis (no_types))
  then have f9: "\<not> length (f st2) \<le> length (f st) - 1 \<or> takeLast (length (f st2)) (f z) = f aa"
    using a6 One_nat_def by presburger
  have f10: "length (f st) - 1 = length (f z) \<or> [] = f st"
    using a6 by auto
  have f11: "length (f st2) \<le> length (f z) \<or> [] = f st"
    using a7 a6 a3 by (metis (no_types) Nitpick.size_list_simp(2) le_antisym not_less_eq_eq)
  then have f12: "iterR nn r z aa \<or> [] = f st"
    using f10 f8 One_nat_def by presburger
  have f13: "takeLast (length (f st2)) (f z) = f aa \<or> [] = f st"
    using f11 f10 f9 by presburger
  have f14: "nn \<le> k \<or> [] = f st"
    using f11 f10 f8 One_nat_def by presburger
  have f15: "takeLast (length (f st2)) (f st) = takeLast (length (f st2)) (f z) \<or> [] = f st"
    using f11 a4 a3 a2 by (metis next_unchanged)
  have "[] \<noteq> f st"
    using a5 by (metis list.sel(2))
  then have "\<exists>n a. iterR (Suc n) r st a \<and> takeLast (length (f st2)) (f st) = f a \<and> \<not> Suc k \<le> n"
    using f15 f14 f13 f12 a4 not_less_eq_eq by auto
  then show ?thesis
    by (metis not_less_eq_eq)
qed
apply (metis push_pop_def)
done

lemma find_return :
  "iterR k r st1 st2 \<Longrightarrow>
   push_pop r f \<Longrightarrow>
   length (f st2) \<le> length (f st1) \<Longrightarrow>
   \<exists>st3 k3. k3 \<le> k \<and> iterR k3 r st1 st3 \<and>
   f st3 = takeLast (length (f st2)) (f st1)"
apply (induction k arbitrary: st1)
  apply (simp add: takeLast_def)
apply auto
subgoal for k st z
using find_return_aux [of k r z st2 f st]
by fastforce
done

(* monotonic invariants *)

definition monoI :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"monoI lst cur iv g = (\<forall>i < length (lst g).
   iv (lst g!i) \<longrightarrow> iv ((cur g # lst g)!i))"

definition mono_same :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> bool" where
"mono_same lst cur iv r ==
   (\<forall>g1 g2. r g1 g2 \<longrightarrow> lst g1 = lst g2 \<longrightarrow> iv (cur g1) \<longrightarrow> iv (cur g2))"

definition mono_pop :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> bool" where
"mono_pop lst cur iv r ==
   (\<forall>g1 g2 a. r g1 g2 \<longrightarrow> a # lst g2 = lst g1 \<longrightarrow> iv (cur g1) \<longrightarrow>
            iv a \<longrightarrow> iv (cur g2))"

definition mono_push :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> bool" where
"mono_push lst cur iv r ==
   (\<forall>g1 g2 a. r g1 g2 \<longrightarrow> a # lst g1 = lst g2 \<longrightarrow> iv (cur g1) \<longrightarrow> iv a) \<and>
   (\<forall>g1 g2 a. r g1 g2 \<longrightarrow> a # lst g1 = lst g2 \<longrightarrow> iv a \<longrightarrow> iv (cur g2))"

definition mono_rules :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> bool" where
"mono_rules lst cur iv r ==
   mono_same lst cur iv r \<and>
   mono_pop lst cur iv r \<and>
   mono_push lst cur iv r"

lemma mono_same :
   "monoI lst cur iv g1 \<Longrightarrow>
    r g1 g2 \<Longrightarrow>
    mono_same lst cur iv r \<Longrightarrow>
    lst g1 = lst g2 \<Longrightarrow>
    monoI lst cur iv g2"
unfolding monoI_def mono_same_def
by (metis nth_non_equal_first_eq)

lemma mono_push :
   "monoI lst cur iv g1 \<Longrightarrow>
    r g1 g2 \<Longrightarrow>
    mono_push lst cur iv r \<Longrightarrow>
    lst g2 = a # lst g1 \<Longrightarrow>
    monoI lst cur iv g2"
unfolding monoI_def mono_push_def
by (auto, metis (no_types, lifting) diff_Suc_1 less_Suc_eq_0_disj nth_Cons')

lemma mono_pop :
   "monoI lst cur iv g1 \<Longrightarrow>
    r g1 g2 \<Longrightarrow>
    mono_pop lst cur iv r \<Longrightarrow>
    lst g1 = a # lst g2 \<Longrightarrow>
    monoI lst cur iv g2"
unfolding monoI_def mono_pop_def
by (auto, metis gr0_conv_Suc length_Cons linorder_neqE_nat not_less_eq nth_Cons_0 nth_Cons_Suc)

lemma mono_works :
   "monoI lst cur iv g1 \<Longrightarrow>
    r g1 g2 \<Longrightarrow>
    push_pop r lst \<Longrightarrow>
    mono_rules lst cur iv r \<Longrightarrow>
    monoI lst cur iv g2"
unfolding mono_rules_def
apply clarsimp
apply (cases "lst g1 = lst g2")
using mono_same apply metis
apply (cases "lst g2 = tl (lst g1)")
using mono_pop [of lst cur iv g1 r g2]
  apply (metis hd_Cons_tl tl_Nil)
apply (cases "lst g1 = tl (lst g2)")
using mono_push [of lst cur iv g1 r g2]
  apply (metis hd_Cons_tl tl_Nil)
using push_pop_def apply metis
done

(* first return stack length *)

definition firstR :: "'a rel \<Rightarrow> nat \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"firstR r k P st1 st2 ==
   iterR k r st1 st2 \<and> P st1 st2 \<and>
   (\<forall>l1 l2 st3. l2 > 0 \<longrightarrow> l1+l2 = k \<longrightarrow>
      iterR l1 r st1 st3 \<longrightarrow>
      iterR l2 r st3 st2 \<longrightarrow>
      \<not>P st1 st3)"

definition first_return :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> 'a rel" where
"first_return lst r k st1 st2 =
    firstR r k (\<lambda>a b. lst b = tl (lst a)) st1 st2"

definition first_smaller :: "('a \<Rightarrow> nat) \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> 'a rel" where
"first_smaller lst r k st1 st2 =
    firstR r k (\<lambda>a b. lst b < lst a) st1 st2"


definition u_firstR :: "'a rel \<Rightarrow> nat \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"u_firstR r k P st1 st2 ==
   iterR k r st1 st2 \<and> P st1 st2 \<and>
   (\<forall>k3 st3. k3 < k \<longrightarrow>
      iterR k3 r st1 st3 \<longrightarrow>
      \<not>P st1 st3)"

definition u_first_return :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> 'a rel" where
"u_first_return lst r k st1 st2 =
    u_firstR r k (\<lambda>a b. lst b = tl (lst a)) st1 st2"

definition u_first_smaller :: "('a \<Rightarrow> nat) \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> 'a rel" where
"u_first_smaller lst r k st1 st2 =
    u_firstR r k (\<lambda>a b. lst b < lst a) st1 st2"

definition u_first_one_smaller :: "('a \<Rightarrow> nat) \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> 'a rel" where
"u_first_one_smaller lst r k st1 st2 =
    u_firstR r k (\<lambda>a b. Suc (lst b) = lst a) st1 st2"

lemma first_simple :
   "firstR r k P st1 st2 \<Longrightarrow> urel r \<Longrightarrow> u_firstR r k P st1 st2"
unfolding firstR_def u_firstR_def
by (metis iter_add1 less_imp_add_positive)

lemma u_first_simple :
   "u_firstR r k P st1 st2 \<Longrightarrow> firstR r k P st1 st2"
unfolding firstR_def u_firstR_def
using less_add_same_cancel1 by blast

(* it is the same as first with that length *)

lemma first_smaller_foo :
   "inc_dec r f \<Longrightarrow>
    u_first_one_smaller f r k st1 st2 \<Longrightarrow>
    u_first_one_smaller f r k st1 st2 \<Longrightarrow>
    u_first_smaller f r k st1 st2"
apply (subst (asm) u_first_one_smaller_def)
apply (auto simp add: u_first_smaller_def u_firstR_def)
subgoal for k4 st4
apply (drule spec[where x = k4], auto)
apply (drule spec[where x = st4], auto)
using all_values [of r f st1 st4 "f st1 - 1" k4]
apply (auto simp: u_first_one_smaller_def u_firstR_def)
  by (smt One_nat_def diff_Suc_1 diff_le_self le_less_trans max_def min.absorb2 not_less not_less_eq_eq)
done

lemma first_smaller :
   "inc_dec r f \<Longrightarrow>
    u_first_one_smaller f r k st1 st2 \<Longrightarrow>
    u_first_smaller f r k st1 st2"
using first_smaller_foo by fastforce

lemma first_smaller2 :
   "inc_dec r f \<Longrightarrow>
    urel r \<Longrightarrow>
    u_first_smaller f r k st1 st2 \<Longrightarrow>
    u_first_one_smaller f r k st1 st2"
apply (auto simp add: u_first_smaller_def u_first_one_smaller_def u_firstR_def)
defer apply fastforce

using all_values [of r f st1 st2 "f st1 - 1" k]
apply auto
proof -
  assume a1: "urel r"
  assume a2: "iterR k r st1 st2"
  assume a3: "f st2 < f st1"
  assume a4: "\<forall>k3<k. \<forall>st3. iterR k3 r st1 st3 \<longrightarrow> \<not> f st3 < f st1"
  assume "\<lbrakk>min (f st1) (f st2) \<le> f st1 - Suc 0; f st1 - Suc 0 \<le> max (f st1) (f st2)\<rbrakk> \<Longrightarrow> \<exists>c k1. iterR k1 r st1 c \<and> k1 \<le> k \<and> f c = f st1 - Suc 0"
  then obtain nn :: nat and aa :: 'a where
    f5: "\<not> min (f st1) (f st2) \<le> f st1 - Suc 0 \<or> \<not> f st1 - Suc 0 \<le> max (f st1) (f st2) \<or> iterR nn r st1 aa \<and> nn \<le> k \<and> f st1 - Suc 0 = f aa"
    by (metis (full_types))
  obtain nna :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    f6: "\<forall>n na. \<not> n < na \<or> Suc n = na \<or> n < nna n na \<and> Suc (nna n na) = na"
    by (metis (no_types) lessE)
  have f7: "1 = Suc 0"
    by (metis Suc_diff_Suc diff_Suc_1 diff_self_eq_0 lessI)
  then have f8: "iterR nn r st1 aa \<or> \<not> min (f st1) (f st2) \<le> f st1 - 1 \<or> \<not> f st1 - 1 \<le> max (f st1) (f st2)"
    using f5 by (metis (no_types))
  have f9: "\<forall>a p n aa ab. \<not> urel p \<or> \<not> iterR n p (ab::'a) aa \<or> a = aa \<or> \<not> iterR n p ab a"
    by (metis (no_types) iter_urel urel_def)
  have f10: "min (f st1) (f st2) = f st2"
    using a3 by (meson min_def not_less)
  have f11: "max (f st1) (f st2) = f st1"
    using a3 by (meson max_def not_less)
  have f12: "\<not> f st2 \<le> f st1 - 1 \<or> f st1 - 1 = f aa \<or> \<not> f st1 - 1 \<le> max (f st1) (f st2)"
    using f10 f7 f5 by (metis (no_types))
  have f13: "iterR nn r st1 aa \<or> \<not> f st2 \<le> f st1 - 1 \<or> \<not> f st1 - 1 \<le> f st1"
    using f11 f10 f8 by metis
  have f14: "k = nn \<or> \<not> k \<le> nn \<or> \<not> f st2 \<le> f st1 - 1 \<or> \<not> f st1 - 1 \<le> f st1"
    using f11 f10 f7 f5 by (metis (no_types) le_less not_less)
  have f15: "k = nn \<or> f st1 = f aa \<or> \<not> f aa \<le> f st1 \<or> \<not> f st2 \<le> f st1 - 1 \<or> \<not> f st1 - 1 \<le> f st1"
    using f11 f10 f7 f5 a4 by (metis (no_types) le_less)
  { assume "Suc (f st2) \<noteq> f st1"
    { assume "st2 \<noteq> aa"
      moreover
      { assume "f st1 \<noteq> f aa \<and> st2 \<noteq> aa"
        moreover
        { assume "k \<le> nn \<and> st2 \<noteq> aa"
          then have "\<not> iterR k r st1 aa \<and> k \<le> nn"
            using f9 a2 a1 by metis
          then have "f st1 - 1 = f aa \<longrightarrow> f st1 < f aa \<or> f aa < f st2"
  using f14 f13 by (metis (no_types) not_less) }
  ultimately have "f st1 - 1 = f aa \<longrightarrow> f st1 - 1 < f st2 \<or> f st1 < f aa"
    using f15 by (metis (no_types) le_less not_less) }
  ultimately have "Suc (f aa) = f st1 \<longrightarrow> f st1 < f st1 - 1 \<or> f st1 - 1 < f st2"
    by (metis diff_Suc_1 lessI) }
  moreover
  { assume "Suc (f aa) \<noteq> f st1"
    moreover
    { assume "Suc (f aa) \<noteq> f st1 \<and> \<not> f st1 < f st1 - 1"
      moreover
        { assume "Suc (f aa) \<noteq> f st1 \<and> f st1 - 1 \<le> f st1 \<and> \<not> f st1 - 1 < f st2"
          then have "f st1 - 1 \<noteq> nna (f st2) (f st1) \<or> Suc (nna (f st2) (f st1)) \<noteq> f st1"
            using f12 f11 by (metis (no_types) not_less) }
      ultimately have "Suc (nna (f st2) (f st1)) = f st1 \<and> f st1 - 1 = nna (f st2) (f st1) \<longrightarrow> f st1 - 1 < f st2"
        by (meson not_less) }
    ultimately have "Suc (nna (f st2) (f st1)) = f st1 \<and> f st1 - 1 = nna (f st2) (f st1) \<longrightarrow> f st1 < f st1 - 1 \<or> f st1 - 1 < f st2"
      by meson }
  ultimately have "Suc (f st2) = f st1"
    using f6 a3 by (metis (no_types) diff_Suc_1 le_less lessI not_less) }
  then show "Suc (f st2) = f st1"
    by metis
qed

definition path :: "'a rel \<Rightarrow> 'a list \<Rightarrow> bool" where
"path r lst = (\<forall>i < length lst-1. r (lst!i) (lst!(i+1)))"

fun pathR :: "'a rel \<Rightarrow> 'a list \<Rightarrow> bool" where
"pathR r (a#b#rest) = (r a b \<and> pathR r (b#rest))"
| "pathR r _ = True"

lemma path_defs : "pathR r lst = path r lst"
apply (simp add:path_def)
apply (induction lst; simp)
apply (case_tac lst; auto simp add:less_Suc_eq_0_disj)
done

fun tlR :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"tlR (a#lst) b = (b=lst)"
| "tlR _ _ = False"

definition push_pop_s :: "'a list rel \<Rightarrow> bool" where
"push_pop_s r == (\<forall>a b. r a b \<longrightarrow> a = b \<or> tlR a b \<or> tlR b a)"

(* should the relations be handled as sets? *)

definition inc_dec_s :: "nat rel \<Rightarrow> bool" where
"inc_dec_s r == (\<forall>a b. r a b \<longrightarrow> a = b \<or> a = Suc b \<or> Suc a = b)"

(* is it better to apply these relations to sequences? *)

(*
lemma all_values2_aux :
  "(min (f z) (f b) \<le> x \<Longrightarrow>
          x \<le> max (f z) (f b) \<Longrightarrow>
          iterR k r z b \<Longrightarrow>
          \<exists>c k1 k2.
             iterR k1 r z c \<and> iterR k2 r c b \<and> f c = x) \<Longrightarrow>
    inc_dec r f \<Longrightarrow>
    min (f aa) (f b) \<le> x \<Longrightarrow>
    x \<le> max (f aa) (f b) \<Longrightarrow>
    r aa z \<Longrightarrow>
    iterR k r z b \<Longrightarrow>
    \<exists>c k1 k2. iterR k1 r aa c \<and> iterR k2 r c b \<and> f c = x"
apply (cases "f aa = f z")
apply auto
  apply (metis iterR.simps(2))

apply (cases "f aa = Suc (f z)")
apply auto
defer
apply (cases "Suc (f aa) = f z")
apply auto

done

lemma all_values :
  "inc_dec r f \<Longrightarrow>
   min (f a) (f b) \<le> x \<Longrightarrow>
   x \<le> max (f a) (f b) \<Longrightarrow>
   iterR k r a b \<Longrightarrow>
   \<exists>c k1. iterR k1 r a c \<and> k1 \<le> k \<and> f c = x"
apply (induction k arbitrary: a, simp)
apply auto
subgoal for k aa z
using all_values_aux [of f z b x k r aa]
by force
done
*)

lemma first_return_smaller :
   assumes a1:"first_return lst r k st1 st2"
   and a2:"length (lst st1) > 0"
   and a3:"push_pop r lst"
   shows "first_smaller (\<lambda>a. length (lst a)) r k st1 st2"


lemma first_return_smaller :
   "first_return lst r k st1 st2 \<Longrightarrow>
    length (lst st1) > 0 \<Longrightarrow>
    push_pop r lst \<Longrightarrow>
    first_smaller (\<lambda>a. length (lst a)) r k st1 st2"
apply (auto simp add: first_return_def first_smaller_def firstR_def)
subgoal for l1 l2 st3
apply (drule spec2[where x = l1 and y = l2], auto)
apply (drule spec[where x = st3], auto)
using all_values[of r
 "\<lambda>a. length (lst a)" st1 st3 "length (lst st1)-1" l1] apply auto
apply (cases "inc_dec r (\<lambda>a. length (lst a))", auto)
defer
using push_pop_inc_dec apply force
apply (cases "min (length (lst st1)) (length (lst st3))
     \<le> length (lst st1) - Suc 0")
defer
  apply linarith
apply auto
apply (cases "length (lst st1) - Suc 0
     \<le> max (length (lst st1)) (length (lst st3))")
defer
  apply linarith
apply auto
subgoal for st4 k4
(* now we should use uniqueness *)
(* but the assumption we needed was deleted --
   use structured proof *)

lemma first_return_stack :
   "first_return lst r k st1 st2 \<Longrightarrow>
    k3 < k \<Longrightarrow>
    iterR k3 r st1 st3 \<Longrightarrow>
    takeLast (lst st3) "
apply (auto simp add: first_return_def firstR_def)

(*
lemma first_return_stack :
   "first_return lst r k st1 st2 \<Longrightarrow>
    l < k \<Longrightarrow>
    "
*)

(* monotonic invariant holds until first return *)

(* monotonic invariant with nat or int? *)

end

