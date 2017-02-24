
Require Import Bvector.
Require Import Zdigits.
Require Import ZArith.

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

Lemma mod_mul_actual_eq : forall a b n m,
  n > 0 -> m > 0 ->
  a mod (n*m) = b mod (n*m) ->
  a mod n = b mod n.
intros.
apply mod_zero_minus; trivial.
eapply mod_mul_eq; trivial.
eapply H0.
apply mod_minus_zero; trivial.
apply Zmult_gt_0_compat; auto.
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

Search Z.testbit.

(*
Z.testbit_spec':
  forall a n : Z, 0 <= n -> Z.b2z (Z.testbit a n) = (a / 2 ^ n) mod 2
*)

Lemma modmud : forall n a, n > 0 -> a mod n = a - n*(a/n).
intros.
rewrite (Z.div_mod a n) at 2; try omega.
Qed.


Check Zmult_gt_0_compat.

(*
Z.div_mod
     : forall a b : Z, b <> 0 -> a = b * (a / b) + a mod b
*)
Lemma collect : forall a n m, n > 0 -> m > 0 ->
 a mod n + n*((a/n) mod m) = a mod (n*m).
intros.
replace (a mod n) with (a-n*(a/n)); try rewrite modmud; auto.
replace (a mod (n*m)) with (a-n*m*(a/(n*m))); try rewrite modmud; auto.
rewrite Z.div_div; try omega.
ring.
apply Zmult_gt_0_compat; trivial.
Qed.

Check Z.testbit.

Search (Fin.t _ -> nat).

Lemma finite_empty : Fin.t 0 -> False.
intros.
inversion H.
Qed.

(*
Lemma split_fin : forall n (k:Fin.t (S n)),
 (k = Fin.F1 \/ exists k0, k = Fin.FS k0).
intros.
set (vv := Fin.to_nat k).
set (v := proj1_sig vv).
assert (v = O \/ exists v0, v = S v0).
case v;auto.
intros.
right.
exists n0; trivial.
elim H; clear H; intros.
left.
assert (proj1_sig vv = O); trivial.
assert (Fin.of_nat_lt (proj2_sig vv) = k).
apply Fin.of_nat_to_nat_inv.
rewrite <- H1.
case vv.
assert (vv = exist _ O (proj2_sig vv)).
case vv; trivial.
setoid_rewrite H0 in H2.
cbv.
Search proj1_sig.
Check EqdepFacts.eq_dep.

inversion H0.
*)

Search List.nth.

Lemma vector_list_cons : forall A n (tl:Vector.t A n) a,
   Vector.to_list (a :: tl) = (a :: Vector.to_list tl)%list.
trivial.
Qed.

Lemma to_binary_testbit : forall (n:nat) (k:nat) a,
  (k < n)%nat ->
  Z.testbit a (Z.of_nat k) =
  List.nth k (Vector.to_list (Z_to_binary n a)) false.
induction n; intros.
inversion H.
replace (Vector.to_list (Z_to_binary (S n) a))
  with (Z.odd a :: Vector.to_list (Z_to_binary n (Z.div2 a)))%list;trivial.
assert (forall k0, (k0 < k)%nat -> Z.testbit (Z.div2 a) (Z.of_nat k0) =
        List.nth k0 (Vector.to_list (Z_to_binary n (Z.div2 a))) false).
intros.
apply IHn; auto; try omega.
assert (k=O \/ exists k0, k = S k0).
case k; eauto.
elim H1; clear H1 IHn; intros.
rewrite H1.
trivial.
elim H1; clear H1; intros.
rewrite H1.
replace (List.nth (S x)
  (Z.odd a :: Vector.to_list (Z_to_binary n (Z.div2 a))) false) with
  (List.nth x (Vector.to_list (Z_to_binary n (Z.div2 a))) false); trivial.
rewrite <- H0; try omega.
rewrite Z.div2_spec.
rewrite Z.shiftr_spec.
replace (Z.of_nat (S x)) with (Z.of_nat x + 1); trivial.
rewrite Nat2Z.inj_succ.
omega.
apply Nat2Z.is_nonneg.
Qed.

Lemma bvector_destruct : forall n (w:Bvector (S n)), exists h tl, w = h ::tl.
intros.
Check Vector.tl.
exists (Vector.hd w).
exists (Vector.tl w).
apply Vector.eta.
Qed.

Lemma bvector_empty : forall (w:Bvector 0), w = [].
apply VectorDef.case0; trivial.
Qed.


Lemma bvector_to_list_eq :
  forall n (v w:Bvector n),
  Vector.to_list v = Vector.to_list w ->
  v = w.
induction n; intros.
rewrite bvector_empty.
rewrite (bvector_empty v).
trivial.
elim (bvector_destruct _ v); intros.
elim H0; clear H0; intros.
elim (bvector_destruct _ w); intros.
elim H1; clear H1; intros.
rewrite H0; rewrite H0 in H; clear H0.
rewrite H1; rewrite H1 in H; clear H1.
rewrite !vector_list_cons in H.
inversion H.
assert (x0 = x2).
apply IHn; trivial.
rewrite H0; trivial.
Qed.


Search Vector.to_list.
Search List.nth.

Lemma list_nth_eq :
  forall A n def (v w:list A),
  length v = n -> length w = n ->
  (forall k, (k < n)%nat -> List.nth k v def = List.nth k w def) ->
  v = w.
induction n; intros.
Search (length _ = O).
rewrite List.length_zero_iff_nil in H, H0.
rewrite H; rewrite H0; trivial.
Search (length _ = (S _)).
destruct v.
inversion H.
destruct w.
inversion H0.

assert (a=a0 /\ v = w).
split.
assert (List.nth O (a :: v) def = List.nth O (a0 :: w) def).
apply H1; omega.
simpl in H2; assumption.
apply (IHn def v w); intros; auto.
assert (List.nth (S k) (a :: v) def = List.nth (S k) (a0 :: w) def).
apply H1; omega.
trivial.
elim H2; clear H2; intros.
rewrite H2; rewrite H3; trivial.
Qed.

Lemma vector_empty : forall A (w:Vector.t A 0), w = [].
intro.
apply (VectorDef.case0); trivial.
Qed.

Lemma vector_destruct : forall A n (w:Vector.t A (S n)), exists h tl, w = h ::tl.
intros.
exists (Vector.hd w).
exists (Vector.tl w).
apply Vector.eta.
Qed.

Lemma vector_to_list_eq :
  forall A n (v w:Vector.t A n),
  Vector.to_list v = Vector.to_list w ->
  v = w.
induction n; intros.
rewrite vector_empty.
rewrite (vector_empty _ v).
trivial.
elim (vector_destruct _ _ v); intros.
elim H0; clear H0; intros.
elim (vector_destruct _ _ w); intros.
elim H1; clear H1; intros.
rewrite H0; rewrite H0 in H; clear H0.
rewrite H1; rewrite H1 in H; clear H1.
rewrite !vector_list_cons in H.
inversion H.
assert (x0 = x2).
apply IHn; trivial.
rewrite H0; trivial.
Qed.



Lemma to_list_length : forall A n (v : Vector.t A n),
  length (Vector.to_list v) = n.
intros.
induction n.
rewrite (vector_empty _ v).
trivial.
elim (vector_destruct _ _ v); intros.
elim H; clear H; intros.
rewrite H; clear H.
rewrite !vector_list_cons; simpl.
rewrite IHn; trivial.
Qed.

Lemma to_binary_testbit_eq : forall n a b,
  (forall k, 0 <= k < Z.of_nat n -> Z.testbit a k = Z.testbit b k) ->
  Z_to_binary n a = Z_to_binary n b.
intros.
apply bvector_to_list_eq.
apply (list_nth_eq bool n false); intros.
apply to_list_length.
apply to_list_length.
rewrite <- !to_binary_testbit; trivial.
rewrite H; trivial.
omega.
Qed.

Check collect.

(*
collect
     : forall a n m : Z,
       n > 0 -> m > 0 -> a mod n + n * ((a / n) mod m) = a mod (n * m)
*)

Lemma two_power_succ : forall n, two_power_nat (S n) = 2 * two_power_nat n.
intro.
rewrite !two_power_nat_equiv.
rewrite Nat2Z.inj_succ.
Search (_ ^(Z.succ _)).
rewrite Z.pow_succ_r; trivial.
omega.
Qed.

Lemma two_power_pos : forall n, two_power_nat n > 0.
intros.
rewrite two_power_nat_equiv.
apply Z.lt_gt.
apply Z.pow_pos_nonneg; try omega.
Qed.

Lemma mod_combine : forall a b n,
  a mod 2 = b mod 2 ->
  Z.div2 a mod (two_power_nat n) = Z.div2 b mod (two_power_nat n) ->
  a mod two_power_nat (S n) = b mod two_power_nat (S n).
intros.
rewrite !two_power_succ.
rewrite <- !collect; try omega; try apply two_power_pos.
rewrite !Zdiv2_div in H0.
rewrite H0; rewrite H; trivial.
Qed.

Lemma mod_sameness : forall n m a b,
  n > 0 ->
  a mod n + n * m = b mod n + n * m ->
  a mod n = b mod n.
intros.
rewrite !modmud; trivial.
rewrite !modmud in H0; trivial.
omega.
Qed.

Lemma mul_sameness : forall n m1 m2 a b,
  n > 0 ->
  0 <= a < n ->
  0 <= b < n ->
  a + n * m1 = b + n * m2 ->
  m1 = m2.
intros.
assert (a = n * m2 - n*m1 + b).
omega.
replace (n * m2 - n*m1) with (n*(m2-m1)) in H3; try ring.
assert (m2-m1 = a/n).
eapply Zdiv_unique.
apply H1.
assumption.
replace (a/n) with 0 in H4; try omega.
Search (_/_ = 0).
rewrite Z.div_small; omega.
Qed.

(*
Theorem Zdiv_unique:
 forall a b q r, 0 <= r < b ->
   a = b*q + r -> q = a/b.
*)

Lemma mod_sameness2 : forall n m1 m2 a b,
  n > 0 ->
  a mod n + n * m1 = b mod n + n * m2 ->
  m1 = m2.
intros.
assert (0 <= a mod n < n).
apply Z_mod_lt; omega.
assert (0 <= b mod n < n).
apply Z_mod_lt; omega.
eapply mul_sameness; try apply H0; trivial.
Qed.

Lemma mod_sameness3 : forall n m1 m2 a b,
  n > 0 ->
  a mod n + n * m1 = b mod n + n * m2 ->
  a mod n = b mod n.
intros.
assert (m1 = m2).
eapply mod_sameness2; eassumption.
rewrite H1 in H0.
eapply mod_sameness; eassumption.
Qed.

Lemma mod_down : forall a b n,
  a mod two_power_nat (S n) = b mod two_power_nat (S n) ->
  Z.div2 a mod two_power_nat n = Z.div2 b mod two_power_nat n.
intros.
rewrite !two_power_succ in H.
rewrite <- !collect in H; try omega; try apply two_power_pos.
Search Z.div2.
rewrite !Z.div2_div.
assert (a mod 2 = b mod 2).
eapply (mod_sameness3 2 ((a / 2) mod two_power_nat n)).


omega.
eassumption.
omega.
Qed.

Lemma mod_extra : forall a b n,
  a mod two_power_nat (S n) = b mod two_power_nat (S n) ->
  a mod 2 = b mod 2.
intros.
rewrite !two_power_succ in H.
eapply mod_mul_actual_eq; try omega; try eassumption.
apply two_power_pos.
Qed.

Lemma two_power_zdiv : forall a k,
 a / two_power_nat (S k) = Z.div2 (a / two_power_nat k).
intros.
rewrite Z.div2_div.
rewrite two_power_succ.
rewrite Z.div_div; try omega.
replace (two_power_nat k * 2) with (2 * two_power_nat k); ring.
assert (two_power_nat k > 0).
apply two_power_pos.
omega.
Qed.

Lemma mod_down_iter : forall k n a b,
  a mod two_power_nat (n + k) = b mod two_power_nat (n + k) ->
  (a/two_power_nat k) mod two_power_nat n = (b/two_power_nat k) mod two_power_nat n.
induction k; intros.
replace (n+O)%nat with n in H; try omega.
replace (two_power_nat 0) with 1; simpl.
rewrite !Z.div_1_r; trivial.
trivial.
rewrite !two_power_zdiv.
apply mod_down.
apply IHk.
replace (S n + k)%nat with (n + S k)%nat; trivial.
omega.
Qed.

Lemma testbits_from_mod : forall a b n k,
a mod two_power_nat n = b mod two_power_nat n ->
(0 <= k < n)%nat ->
(a / two_power_nat k) mod 2 = (b / two_power_nat k) mod 2.
intros.
eapply mod_extra.
eapply mod_down_iter.
replace n with (S (n-k-1) + k)%nat in H; try eassumption.
omega.
Qed.

(* testbit condition should be equivalent with mod 2**n *)
Lemma testbits_mod : forall n a b,
  (forall k, 0 <= k < Z.of_nat n -> Z.testbit a k = Z.testbit b k) <->
  a mod two_power_nat n = b mod two_power_nat n.
induction n; intros.
rewrite two_power_nat_equiv.
simpl.
split; intros.
rewrite !modmud; try omega.
rewrite !Z.mul_1_l.
rewrite !Z.div_1_r.
omega.
omega.
split; intros.
apply mod_combine.
assert (Z.testbit a 0 = Z.testbit b 0).
apply H.
split; try omega.
rewrite Nat2Z.inj_succ.
omega.

rewrite <- !Z.bit0_mod.
rewrite H0.
trivial.

apply IHn; intros.

rewrite !Z.div2_spec.
rewrite !Z.shiftr_spec; try omega.
apply H.
rewrite Nat2Z.inj_succ.
omega.

apply Z.b2z_inj.
rewrite !Z.testbit_spec'; try omega.

replace (2 ^ k) with (two_power_nat (Z.to_nat k)).
eapply testbits_from_mod.
eassumption.
split.
omega.

replace (S n) with (Z.to_nat (Z.of_nat (S n))).

apply Z2Nat.inj_lt; try omega.

rewrite Nat2Z.id; trivial.

rewrite two_power_nat_equiv.
rewrite Z2Nat.id; omega.
Qed.

Lemma to_binary_mod : forall n a b,
  a mod (two_power_nat n) = b mod (two_power_nat n) ->
  Z_to_binary n a = Z_to_binary n b.
intros.
apply to_binary_testbit_eq.
apply testbits_mod.
trivial.
Qed.

Lemma binary_value_small : forall n x,
  binary_value n x < two_power_nat n.
induction n; intros.
simpl.
apply Z.gt_lt.
apply two_power_pos.
elim (bvector_destruct _ x); intros.
elim H; clear H; intros.
rewrite H.
rewrite binary_value_Sn.
rewrite two_power_succ.
set (H2 := (IHn x1)).
assert (bit_value x0 < 2).
unfold bit_value.
case x0; omega.
Search (?a * _ + _ < ?a * _).
replace (bit_value x0 + 2 * binary_value n x1) with
   (2 * binary_value n x1 + bit_value x0).
case x0.
unfold bit_value.
apply Z.double_above.
omega.
unfold bit_value.
omega.
omega.
Qed.

Lemma binary_value_mod : forall n a,
  binary_value n (Z_to_binary n (a mod two_power_nat n)) = a mod two_power_nat n.
intros.
Search (binary_value).
apply Z_to_binary_to_Z.
Search (0 <= _ mod _).
apply Z.le_ge.
apply Z_mod_lt.
apply two_power_pos.
apply Z_mod_lt.
apply two_power_pos.
Qed.

(* now we get the correct formula for converting to bvector and back *)
Lemma bvector_and_back : forall n a,
  binary_value n (Z_to_binary n a) = a mod (two_power_nat n).
intros.
(* set (b := (a-two_power_nat n*(a/two_power_nat n)) mod (two_power_nat n)). *)
replace (binary_value n (Z_to_binary n a)) with
  (binary_value n (Z_to_binary n (a mod two_power_nat n))).
apply binary_value_mod.

replace (Z_to_binary n a) with (Z_to_binary n (a mod two_power_nat n));auto.
apply to_binary_mod.

apply Z.mod_mod.
assert (two_power_nat n > 0).
apply two_power_pos.
omega.
Qed.

(* *)

Section Cyclic.

Variable n : nat.

Definition to_Z a := binary_value n a.

Definition from_Z a := Z_to_binary n a.

Definition wB := two_power_nat n.

Definition add (a b: Bvector n) := from_Z (to_Z a + to_Z b).

Hint Rewrite bvector_and_back : stuff.
Hint Unfold to_Z from_Z wB add : stuff.

Lemma add_spec : forall a b, to_Z (add a b) = (to_Z a + to_Z b) mod wB.
intros.
repeat autounfold with stuff; autorewrite with stuff.
trivial.
Qed.

Lemma add_comm : forall a b, add a b = add b a.
intros.
repeat autounfold with stuff.
rewrite Z.add_comm.
trivial.
Qed.

Lemma add_assoc : forall a b c, add a (add b c) = add (add a b) c.
intros.
repeat autounfold with stuff.
autorewrite with stuff.
apply to_binary_mod.
Search ((_ + _) mod _).
rewrite Zplus_mod_idemp_l.
rewrite Zplus_mod_idemp_r.
replace (binary_value n a + (binary_value n b + binary_value n c)) with
  (binary_value n a + binary_value n b + binary_value n c); trivial; ring.
Qed.

End Cyclic.


