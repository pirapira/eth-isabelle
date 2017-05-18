theory CallTree
imports PathRel
begin

datatype tree = Leaf | Tree tree "tree list"



fun expand :: "tree \<Rightarrow> nat list" where
"expand Leaf = [0]"
| "expand (Tree t lst) =
   [0] @ map Suc (concat (map expand (t#lst))) @ [0]"

value "expand (Tree Leaf [Leaf, Tree Leaf []])"
value "expand (Tree Leaf [Leaf])"

lemma expand_size : "length (expand t) > 0"
by (cases t; auto)

lemma expand_hd_last : "hd (expand t) = last (expand t)"
by (cases t; auto)

lemma app_nth :
   "i < length a \<Longrightarrow> (a@b)!i = a!i"
  by (simp add: nth_append)

lemma expand_inside_large :
   "0 < i \<Longrightarrow> i < length (expand t) - 1 \<Longrightarrow>
    expand t ! i > 0"
by (cases t; auto simp add:nth_append)

lemma tree_inc_dec : "inc_decL (expand t)"
apply (induction t)
apply (simp add:inc_decL_def pathR.simps inc_dec_def)

oops


lemma tree_call :
   "ncall lst \<Longrightarrow> \<exists>t x. map (%y. y+x) (expand t) = lst"
oops

end

