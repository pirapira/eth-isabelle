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
   urel r \<Longrightarrow>
   (\<forall>sti. \<forall>k1 \<le> k. iterR k1 r st1 sti \<longrightarrow>
                   l \<le> length (f sti) ) \<Longrightarrow>
   takeLast l (f st2) = takeLast l (f st1)"
apply (induction k arbitrary:st1, simp)
apply auto
subgoal for k st3 z
apply (rule stack_unchanged_split [of k r st3 st2 l f])
apply auto
apply (rule ex_and)
  apply blast
apply auto
defer
apply (rule next_unchanged [of r f], auto)
subgoal for st
by (rule funny[of k r st3 l f st]; auto)
apply (drule spec2[where x="st3" and y = "0"], auto)
subgoal for st
apply (rule Spec[where R="\<lambda>st1. iterR k r st1 st2"
   and P="\<lambda>st1. \<forall>sti k1. k1 \<le> k \<longrightarrow> iterR k1 r st1 sti \<longrightarrow> l \<le> length (f sti)"
   and x="st"])
apply auto
defer
apply fastforce
  using apply_urel by fastforce
done done

(* find returns *)

(* monotonic invariants *)

end

