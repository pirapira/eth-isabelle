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

lemma call_invariant :
  "call (map snd lst) \<Longrightarrow>
   monoI iv (hd lst) \<Longrightarrow>
   pathR (mono_rules iv) lst \<Longrightarrow>
   iv (fst (hd lst)) \<Longrightarrow>
   iv (fst (last lst))"



