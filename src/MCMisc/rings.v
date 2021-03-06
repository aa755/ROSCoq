Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MCMisc.tactics.
Require Import Ring.
(*less annoying than ^2 which multiplies by 1 as well*)
Definition sqr `{Mult A} (a:A) := a*a.

Section RingMisc.

(**some miscelleneous convenience props about rings.
The ring tactic can prove these. However, to use that tactic,
one has to manually assert the statement, which can
sometimes contain bulky terms, which may need to be updated
when a proof or statement changes slightly.
These lemmas can often help avoid those manual assertions.
*)
Context `{Ring A}.
Add Ring tempRing : (stdlib_ring_theory A).

Lemma RingShiftMinus  : forall 
  a b c : A,
  a - b  = c <-> a = b + c.
Proof using All.
  intros ? ? ?; split; intros Hh.
  (**the ring tactic does not seem to look at hyps*)
  - rewrite <- Hh. ring.
  - rewrite Hh. ring.
Qed.

Lemma RingProp2  : forall 
  a b  : A,
  a + b - b  =a.
Proof using All.
  intros ? ?. ring.
Qed.

Lemma RingProp3  : forall 
  a   : A,
  a + a   = 2 * a.
Proof using All.
  intros ? . ring.
Qed.

Lemma RingProp4  : forall 
  a b c  : A,
  -a * (b-c)   = a * (c-b).
Proof using All.
  intros ? ? ? . ring.
Qed.

Lemma MultShuffle3l: 
∀ a b c : A, 
 a * (b * c) = b * a * c.
Proof using All.
  intros.
  ring.
Qed.

Lemma PlusShuffle3l: 
∀ a b c : A, 
 a + (b + c) = b + a + c.
Proof using All.
  intros.
  ring.
Qed.

Lemma MultShuffle3r: 
∀ a b c : A, 
 a * b * c = a * c * b.
Proof using All.
  intros.
  ring.
Qed.

Lemma PlusShuffle3r: 
∀ a b c : A, 
 a + b + c = a + c + b.
Proof using All.
  intros.
  ring.
Qed.


Lemma MultSqrMix: 
∀ a b c d : A, 
 (a * b * c * d = (a * c) * (b * d)).
Proof using All.
  intros.
  ring.
Qed.

(*
 Lemma X:
 forall 
(X Y X0 Y0 xy cc X1 Y1 s c : A),

((X * (c * c) + xy * s * c + Y * (s * s)) * (X1 * X1) +
(Y * (c * c) - xy * s * c + X * (s * s)) * (Y1 * Y1) +
((X0 * c + Y0 * s) * X1 + (Y0 * c + - X0 * s) * Y1 +
 (xy * (1 - 2 * (s * s)) + (Y - X) * (2 * s * c)) * X1 *
 Y1 + cc))  =
X * ((X1 * c - Y1 * s) * (X1 * c - Y1 * s)) +
Y * ((Y1 * c + X1 * s) * (Y1 * c + X1 * s)) +
(X0 * (X1 * c - Y1 * s) + Y0 * (Y1 * c + X1 * s) +
 xy * (X1 * c - Y1 * s) * (Y1 * c + X1 * s) + cc)
.
 Proof.
 intros.
 ring_simplify.
*)

Section Le.
Require Export MathClasses.orders.rings.
Context `{Le A}
    `{@orders.SemiRingOrder A equiv plus mult zero one le}.

Lemma RingLeProp1  : forall 
  a  b : A,
  0 ≤ b
  ->a ≤ b + a.
Proof using All.
  intros ? ? Hh.
  apply flip_le_minus_l. rewrite plus_negate_r.
  assumption.
Qed.

Lemma RingLeProp1l  : forall 
  a  b : A,
  0 ≤ b
  ->a ≤  a + b.
Proof using All.
  intros ? ? Hh.
  rewrite commutativity.
  apply RingLeProp1.
  assumption.
Qed.

(** Proof is the dual of MathClasses.orders.rings.ge_1_mult_le_compat_r*)
Lemma le_1_mult_le_compat_r x y z : z ≤ 1 → 0 ≤ x → x ≤ y → x * z ≤ y .
  Proof.
    intros.
    transitivity x;[| easy].
    rewrite <-(mult_1_r x) at 2.
    now apply (order_preserving_nonneg (.*.) x).
  Qed.

Lemma RingLeProp2  : forall 
  a : A,
  0 ≤ a
  ->a ≤ 2*a.
Proof using All.
  intros ? Hh.
  rewrite <- RingProp3.
  apply RingLeProp1.
  assumption.
Qed.

Lemma RingLeProp3  : forall 
  a : A,
  0 ≤ a
  ->0 ≤ 2*a.
Proof using All.
  intros ? Hh.
  rewrite <- RingProp3.
  apply nonneg_plus_compat; assumption.
Qed.

Require Import MathClasses.interfaces.orders.

Context `{Lt A} `{Apart A} {FPSRO:@FullPseudoSemiRingOrder A 
equiv apart plus mult zero one le lt}.

Set Suggest Proof Using.
Lemma RingLeIfSqrLe  : forall 
  (a b : A),
  0 < b + a
  → sqr a ≤ sqr b
  → a ≤  b.
Proof using All.
  intros ? ? Hp Hs.
  apply flip_nonneg_minus in Hs.
  assert (sqr b - sqr a = (b-a)*(b+a)) as Heq by (unfold sqr;ring).
  rewrite Heq in Hs. clear Heq.
  apply flip_nonneg_minus.
  eapply nonneg_mult_rev_l; eauto.
Qed.

Lemma RingPosNnegCompatPlus  : forall 
  (a b : A),
  0 < b
  →0 ≤ a
  → 0 < b + a.
Proof using All.
  intros ? ? Hlt hlt. eapply lt_le_trans; eauto.
  rewrite commutativity.
  apply RingLeProp1.
  assumption.
Qed.

Lemma RingLeSqr1  : forall 
  (a b : A),
  0 ≤ b
  → 0 ≤ a
  → sqr a + sqr b ≤ sqr (b + a).
Proof using All.
  intros ? ? Ha Hb.
  unfold sqr.
  apply flip_nonneg_minus.
  ring_simplify.
  rewrite <- (@simple_associativity _ _ mult _ _).
  apply RingLeProp3.
  apply nonneg_mult_compat; assumption.
Qed.

Lemma RingLeMultIff  : forall 
  (a b k : A),
  0 < k
  → (a ≤ b ↔ k*a ≤ k*b).
Proof.
  intros ? ? ? Hk.
  split; intro h.
- apply (order_preserving (mult k));
  eauto with typeclass_instances.

- apply (order_reflecting) in h;
  eauto with typeclass_instances.
  (* k needs to be positive in this case *)
 
Qed.

Lemma RingLtMultIff  : forall 
  (a b k : A),
  0 < k
  → (a < b ↔ k*a < k*b).
Proof.
  intros ? ? ? Hk.
  split; intro h.
- apply (strictly_order_preserving);
  eauto with typeclass_instances.

- apply (strictly_order_reflecting) in h;
  eauto with typeclass_instances. 
Qed.



(** why is this needed? without it, rewrite Hki in [RingLeRecipMultIff]
below fails *)

Local Instance ProperLt :
Proper (equiv ==> equiv ==> iff) lt.
Proof.
eauto with typeclass_instances.
Qed.

(** there is a version for for fields, where the hypothesis H10 is not needed. *)
Lemma RingLeRecipMultIff {H10 :PropHolds (1 ≶ 0)} : forall 
  (a b k kinv : A),
  0 < k
  → kinv*k =1
  → (k*a ≤ b ↔ a ≤ kinv*b).
Proof.
  intros ? ? ? ? Hk Hki.
  rewrite RingLeMultIff with (k:=kinv);[|].
- ring_simplify [Hki] (kinv * (k * a)) .
  reflexivity.
- eapply pos_mult_rev_l;[| apply Hk].
  rewrite Hki. apply lt_0_1.
Qed.

   
End Le.


End RingMisc.
