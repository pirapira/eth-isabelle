theory PathInvariant
imports PathRel
begin

lemma mono_list :
  "push_popL (map snd lst) \<Longrightarrow>
   pathR (mono_rules iv) lst \<Longrightarrow>
   length lst > 0 \<Longrightarrow>
   monoI iv (hd lst) \<Longrightarrow>
   monoI iv (last lst)"
apply (induction "mono_rules iv" lst rule:pathR.induct)
apply (auto simp add:pathR.simps mono_works pathR2 pathR3 push_popL_def)
done

(* top rules *)
(* actually, the mono rules will hold *)
(* but sometime mono push and pop will only hold because
   they are part of call sequences
 *)

(*
mono_pop : because it is a call, and calls have the invariant

this rule has to be proven for each possible call into a contract
for the invariant to hold ...
*)
definition call_rule :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) list \<Rightarrow> bool" where
"call_rule iv lst = (
  call (map snd lst) \<longrightarrow> iv (fst (hd lst)) \<longrightarrow>
  iv (fst (last lst))
)"

definition call_out :: "'a list list \<Rightarrow> bool" where
"call_out lst = (
  push_popL lst \<and>
  length lst > 1 \<and>
  (last lst, hd lst) \<in> tlR \<and>
  (\<forall>x \<in> set lst. length x \<ge> length (hd lst))
)"

(*
for pushing, we need to ... well in theory the external call
 could break the invariant and then fix it
*)
definition call_out_rule :: "('a \<Rightarrow> bool) \<Rightarrow> ('a * 'a list) list \<Rightarrow> bool" where
"call_out_rule iv lst = (
  call_out (map snd lst) \<longrightarrow> iv (fst (hd lst)) \<longrightarrow>
  iv (fst (last lst))
)"

lemma mono_same_length :
   "(a,b) \<in> mono_same iv \<Longrightarrow>
    length (snd a) = length (snd b)"
  by (smt fst_conv mem_Collect_eq mono_same_def snd_conv)


lemma mono_pop_length :
   "(a,b) \<in> mono_pop iv \<Longrightarrow>
    length (snd a) = length (snd b) + 1"
  by (smt Suc_eq_plus1 fst_conv length_Cons mem_Collect_eq mono_pop_def snd_conv)

lemma mono_push_length :
   "(a,b) \<in> mono_push iv \<Longrightarrow>
    length (snd a) + 1 = length (snd b)"
  by (smt Int_iff One_nat_def add.right_neutral add_Suc_right fst_conv length_Cons mem_Collect_eq mono_push_def prod.sel(2))

lemma mono_is_push :
  "(a,b) \<in> mono_rules iv \<Longrightarrow>
   length (snd a) + 1 = length (snd b) \<Longrightarrow>
   (a, b) \<in> mono_push iv"
by (metis UnE less_add_same_cancel1 mono_pop_length mono_rules_def mono_same_length not_add_less1 zero_less_one)

lemma mono_is_pop :
  "(a,b) \<in> mono_rules iv \<Longrightarrow>
   length (snd a) = length (snd b) + 1 \<Longrightarrow>
   (a, b) \<in> mono_pop iv"
  by (metis UnE less_add_same_cancel1 mono_push_length mono_rules_def mono_same_length not_add_less1 zero_less_one)

lemma mono_is_same :
  "(a,b) \<in> mono_rules iv \<Longrightarrow>
   length (snd a) = length (snd b) \<Longrightarrow>
   (a, b) \<in> mono_same iv"
  by (metis UnE less_add_same_cancel1 mono_pop_length mono_push_length mono_rules_def not_add_less1 zero_less_one)

(* first the invariant is pushed into stack (second element). *)
lemma call_invariant_push :
  "call (map snd lst) \<Longrightarrow>
   monoI iv (hd lst) \<Longrightarrow>
   pathR (mono_rules iv) lst \<Longrightarrow>
   iv (fst (hd lst)) \<Longrightarrow>
   iv (hd (snd (lst!1)))"
apply (auto simp add:path_defs path_def
  call_def tlR_def)
apply (subgoal_tac "hd lst = lst!0")
apply auto
defer
  apply (metis hd_conv_nth list.size(3) not_numeral_less_zero)
apply (subgoal_tac "(lst!0, lst!1) \<in> mono_push iv")
apply (auto simp add:mono_push_def)[1]
apply (subgoal_tac "(lst!0, lst!1) \<in> mono_rules iv")
defer
  apply simp
apply (subgoal_tac "length (snd (lst!0)) + 1 = length (snd (lst!1))")
using mono_is_push [of "lst!0" "lst!1" iv]
  apply blast
  by (metis One_nat_def less_imp_Suc_add list.size(4) nth_map zero_less_Suc)

(* pushed element cannot change *)
lemma call_invariant_before_after :
  "call lst \<Longrightarrow>
   lst!1 = lst!(length lst-2)"
apply (subgoal_tac "length (lst!1) = length (lst!(length lst-2))")
using call_inside_big_idx [of lst "length lst-2"]
  apply (metis One_nat_def PathRel.take_all Suc_1 Suc_leI Suc_lessD call_def diff_less_mono2 lessI zero_less_diff)
using call_ncall [of lst]
  by (smt One_nat_def Suc_leI Suc_lessD call_def diff_less last_clip le_less length_map ncall_last nth_map numeral_2_eq_2 zero_less_diff zero_less_numeral)

lemma get_mono_inv :
  "monoI iv a \<Longrightarrow>
   length (snd a) > 0 \<Longrightarrow>
   iv (hd (snd a)) \<Longrightarrow>
   iv (fst a)"
  using hd_conv_nth monoI_def by fastforce

lemma ncall_first_step : 
  "ncall lst \<Longrightarrow>
   lst!1 = lst!0 + 1"
by (simp add:ncall_def sucR_def)

lemma ncall_next : 
  "ncall lst \<Longrightarrow>
   lst ! (length lst - 2) = lst!1"
  by (smt One_nat_def Suc_diff_Suc Suc_lessI diff_le_self last_clip less_eq_Suc_le ncall_def ncall_last numeral_2_eq_2 zero_less_diff)

lemma ncall_last_length : 
  "ncall lst \<Longrightarrow>
   last lst + 1 = lst ! (length lst - 2)"
using ncall_stack_length ncall_next ncall_first_step
  by (metis gr_implies_not_zero hd_conv_nth list.size(3) ncall_def)

lemma call_last_length : 
  "call lst \<Longrightarrow>
   length (last lst) + 1 =
   length (lst ! (length lst - 2))"
using ncall_stack_length call_ncall
  by (smt One_nat_def call_def diff_less last_index length_map ncall_last_length nth_map numeral_2_eq_2 order.strict_trans zero_less_Suc)


(* because the pushed element didn't change, current must have the
   invariant, and we can use the mono push rule *)
lemma call_invariant :
  "call (map snd lst) \<Longrightarrow>
   monoI iv (hd lst) \<Longrightarrow>
   pathR (mono_rules iv) lst \<Longrightarrow>
   iv (fst (hd lst)) \<Longrightarrow>
   iv (fst (last lst))"
apply (subgoal_tac "monoI iv (lst ! (length lst-2))")
apply (subgoal_tac "iv (hd (snd (lst ! (length lst-2))))")
apply (subgoal_tac "(lst ! (length lst-2), last lst) \<in> mono_pop iv")
apply (subgoal_tac "iv (fst (lst ! (length lst-2)))")
  apply (smt fst_conv list.sel(1) mem_Collect_eq mono_pop_def snd_conv)
  apply (metis (no_types, hide_lams) Suc_eq_plus1 hd_conv_nth length_Cons list.sel(1) list.size(3) monoI_def mono_pop_length nat.simps(3) zero_less_Suc)
apply (subgoal_tac "(lst ! (length lst - 2), last lst) \<in> mono_rules iv")
apply (subgoal_tac "length (snd (last lst)) + 1 = length (snd (lst ! (length lst - 2)))")
  apply (smt UnE add_right_imp_eq mono_push_length mono_rules_def mono_same_length numeral_eq_iff numeral_plus_numeral numerals(1) semiring_norm(2) semiring_norm(6) semiring_norm(85) semiring_norm(87) semiring_normalization_rules(24) semiring_normalization_rules(25))
using call_last_length [of "map snd lst"]
apply simp
apply (subgoal_tac "lst \<noteq> []")
apply (simp add:last_map)
  using call_def apply force
apply (subgoal_tac "lst \<noteq> []")
apply (simp add:path_defs path_def last_conv_nth)
  apply (smt Nil_is_map_conv Nitpick.size_list_simp(2) One_nat_def Suc_diff_Suc call_def diff_less length_greater_0_conv length_tl less_trans_Suc map_tl not_less_less_Suc_eq numeral_2_eq_2 zero_less_numeral)
  using call_def apply force
apply (subgoal_tac "snd (lst ! 1) = snd (lst ! (length (map snd lst) - 2))")
using call_invariant_push [of lst iv]
apply simp
using call_invariant_before_after [of "map snd lst"]
apply simp
  apply (smt Nil_is_map_conv One_nat_def call_def diff_less length_greater_0_conv length_tl less_trans_Suc map_tl nth_map order.strict_trans zero_less_diff zero_less_numeral)
using mono_list [of "take (length lst - 1) lst" iv]
apply (auto simp add:call_def push_popL_def)
apply (subgoal_tac "lst \<noteq> []")
apply auto
apply (subgoal_tac
   "map snd (take (length lst - 1) lst) =
    take (length lst - 1) (map snd lst)")
defer
apply (simp add: take_map)
apply (auto simp add:pathR_take)
  by (metis One_nat_def Suc_1 Suc_diff_Suc Suc_lessD diff_Suc_less hd_take last_take)


end
