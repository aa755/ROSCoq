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

End Le.


End RingMisc.
