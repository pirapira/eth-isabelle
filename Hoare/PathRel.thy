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

end
