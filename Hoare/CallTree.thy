theory CallTree
imports PathRel
begin

datatype tree = Leaf | Tree tree "tree list"

fun expand :: "tree \<Rightarrow> nat list" where
"expand Leaf = [0]"
| "expand (Tree t lst) =
   [0] @ map Suc (expand t @ concat (map (tl \<circ> expand) lst)) @ [0]"

value "expand (Tree Leaf [Leaf, Tree Leaf [],
  Tree Leaf [], Leaf])"
value "expand (Tree (Tree Leaf []) [Leaf])"

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

lemma path_app :
   "pathR r a \<Longrightarrow> pathR r b \<Longrightarrow>
    length a > 0 \<Longrightarrow> length b > 0 \<Longrightarrow>
    (last a, hd b) \<in> r \<Longrightarrow>
    pathR r (a@b)"
apply (auto simp add:path_defs path_def nth_append)
  apply (metis Suc_lessI diff_Suc_1 hd_conv_nth last_conv_nth)
apply (subgoal_tac "(Suc i - length a) = Suc (i - length a)"; auto)
done

lemma tree_inc_dec : "inc_decL (expand t)"
apply (induction t)
apply (simp add:inc_decL_def pathR.simps inc_dec_def)
apply auto

oops


lemma tree_call :
   "ncall lst \<Longrightarrow> \<exists>t x. map (%y. y+x) (expand t) = lst"
using ncall_def decompose_call

oops

end

