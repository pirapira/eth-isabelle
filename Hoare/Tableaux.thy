theory Tableaux
 imports Main
begin

type_synonym 'a table = "int \<Rightarrow> int \<Rightarrow> 'a option"
type_synonym 'a row = "int \<Rightarrow> 'a option"

definition cells :: "'a table \<Rightarrow> (int*int) set" where
"cells tab = {(x,y) | x y. tab x y \<in> range Some}"

definition init_list :: "'a list \<Rightarrow> 'a table" where
"init_list lst = (%x y.
   if int (length lst) \<ge> x \<or> x < 0 \<or> y \<noteq> 0 then None
   else Some (lst!nat x))"

definition int_list :: "int list \<Rightarrow> unit table" where
"int_list lst = (%x y.
   if int (length lst) \<ge> x \<or> x < 0 then None
   else if lst!nat x = y then Some () else None)"

definition transpose :: "'a table \<Rightarrow> 'a table" where
"transpose a = (%x y. a y x)"

definition skew :: "(int \<Rightarrow> int) \<Rightarrow> 'a table \<Rightarrow> 'a table" where
"skew f a = (%x y. a x (f x + y))"

(* y changes *)
definition column :: "int \<Rightarrow> 'a table \<Rightarrow> 'a row" where
"column x a = (%y. a x y)"

definition row :: "int \<Rightarrow> 'a table \<Rightarrow> 'a row" where
"row y a = (%x. a x y)"

lemma rc_transpose : "row x a = column x (transpose a)"
by (simp add:row_def column_def transpose_def)

definition elems :: "'a row \<Rightarrow> 'a set" where
"elems r = {a | a x. r x = Some a}"

lemma skew_elems :
  "elems (column y a) = elems (column y (skew f a))"
unfolding elems_def column_def skew_def
  by (metis add_minus_cancel)


end

