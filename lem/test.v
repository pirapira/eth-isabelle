
Require Import Bvector.
Require Import Zdigits.
Require Import ZArith.

Section test.

Search (_ mod _).

Open Scope Z.


Lemma mod_add : forall a b c n, a mod n = b mod n -> (a+c) mod n = (b+c) mod n.
intros.
rewrite <- Zplus_mod_idemp_l.
rewrite H.
rewrite Zplus_mod_idemp_l.
reflexivity.
Qed.

Lemma mod_mul_eq : forall a b n m,
  n > 0 -> m > 0 ->
  (a-b) mod (n*m) = 0 ->
  (a-b) mod n = 0.
intros.
Search (_ mod _ = 0).
apply Zmod_divides.
omega.
apply Zmod_divides in H1.
elim H1; intros.
exists (m*x).
rewrite H2.
ring.
assert (n*m > 0).
apply Zmult_gt_0_compat; auto.
omega.
Qed.

Search ((_ - _) mod _ = 0 ).

Lemma mod_zero_minus : forall a b n, n > 0 ->
  (a-b) mod n = 0 ->
  a mod n = b mod n.
intros.
apply Zmod_divides in H0; try omega.
elim H0; clear H0; intros.
replace a with (b+x*n); try omega.
apply Z_mod_plus_full.
replace (x*n) with (n*x); try omega.
ring.
Qed.

Lemma mod_minus_zero : forall a b n, n > 0 ->
  a mod n = b mod n ->
  (a-b) mod n = 0.
intros.
assert ((a+(-b)) mod n = (b+(-b)) mod n).
apply mod_add; auto.
replace (a-b) with (a+ -b); try omega.
replace (b + -b) with 0 in H1; try omega.
rewrite Zmod_0_l in H1.
assumption.
Qed.

Eval cbv in (-1 mod 2).

Lemma div2_cancel : forall a, Z.div2 (2*a) = a.
intros.
rewrite Z.div2_div.
replace (2*a) with (a*2).
apply Z_div_mult.
omega.
omega.
Qed.

(*
Z.add_b2z_double_div2: forall (a0 : bool) (a : Z), (Z.b2z a0 + 2 * a) / 2 = a
*)


(* need relation between testbit and mod two_power_nat *)


Lemma div2_mod2 : forall n a,
   (Z.div2 a mod two_power_nat n) mod 2 = Z.div2 (a mod (2*Z.of_nat n)) mod 2.
intros.
Search Z.shiftl.
assert ((exists b, 2*b=a \/ 2*b+1=a)).
admit.
elim H; clear H; intros.
elim H; clear H; intros;rewrite <- H; clear H.
simpl.
induction n; intros.
simpl.
admit.
simpl.

Lemma to_binary_mod : forall n a b,
  a mod (two_power_nat n) = b mod (two_power_nat n) ->
  Z_to_binary n a = Z_to_binary n b.
induction n; intros.
simpl; reflexivity.
rewrite (Zmod2_twice a).
rewrite (Zmod2_twice b).
simpl.
case (Zmod2 b).
case (Zmod2 a).
simpl.
Search (_ mod _ = _ mod _).

a mod two_power_nat (S n) = b mod two_power_nat (S n) ->
(Z.div2 a) mod two_power_nat n = (Z.div2 b) mod two_power_nat n

Variable k : nat.
Variable a b : Bvector k.








