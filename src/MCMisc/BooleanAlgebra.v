Require Export MathClasses.theory.rings.
Require Export MathClasses.interfaces.abstract_algebra.
Require Import Ring.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.interfaces.orders.
Require Export MathClasses.orders.rings.
Class BooleanAlgebra (A:Type) `{Ring A} :=
  boolean_mult : ∀ x:A, x*x=x.

Section BooleanAlgebraNotations.

Context `{BooleanAlgebra R}.

Require Export SetNotations.

Global Instance BooleanAlgUnion : SetUnion R :=
    λ (a b : R), a + b + a*b .
Global Instance BooleanAlgIntersection : SetIntersection R :=
    mult.


Notation "b \ x " := (b + b * x) (at level 100).

Notation "x ᶜ  " := (1 \ x) (at level 100).

End BooleanAlgebraNotations.

Section BooleanAlgebraProps.
  Context `{BooleanAlgebra R}.

Add Ring  stdlib_ring_theoryldsjfsd : (rings.stdlib_ring_theory R).


Lemma BooleanAlgebraXplusX : ∀ (x : R), x + x = 0.
Proof.
  intros x.
  pose proof (boolean_mult (x + x)) as Hs.
  assert ((x + x) * (x + x) = 2 * (x * x + x * x)) as Hr by ring.
  rewrite Hr in Hs. clear Hr.
  rewrite boolean_mult in Hs.
  apply equal_by_zero_sum in Hs.
  ring_simplify in Hs.
  ring_simplify.
  assumption.
Qed.

Lemma BooleanAlgebraMinusX : ∀ (x : R), - x = x.
Proof.
  intros x.
  apply equal_by_zero_sum.
  rewrite <- negate_plus_distr.
  rewrite BooleanAlgebraXplusX.
  ring.
Qed.

Lemma BooleanAlgebra1Max : ∀ (x : R), x ⊆ 1.
Proof.
  intros x.
  unfold setSubset.
  unfold setIntersection, BooleanAlgIntersection.
  ring.
Qed.

Lemma paperEq1 : ∀ (x y u v : R),
  (x + y) + (u + v) ⊆ (x + u) ∪ (y + v).
Proof.
  intros ? ? ? ?.
  unfold setSubset.
  unfold setUnion, BooleanAlgUnion.
  unfold setIntersection, BooleanAlgIntersection.
  ring_simplify.
  ring_simplify.
  rewrite BooleanAlgebraXplusX.
  ring_simplify.
  repeat (rewrite boolean_mult).
  setoid_rewrite  <- (mult_assoc u v v).
  setoid_rewrite  <- (mult_assoc x v v).
  setoid_rewrite  <- (mult_assoc y u u).
  setoid_rewrite  <- (mult_assoc x y y).
  repeat (rewrite boolean_mult).
  ring_simplify.
  rewrite BooleanAlgebraXplusX.
  ring.
Qed.

Lemma subsetUnionMeasure : ∀ a b: R,
  a ⊆ b →  (a ∪ b) = b.
Proof.
  intros ? ? Hs.
  unfold setSubset in Hs.
  unfold setUnion, BooleanAlgUnion.
  rewrite <- Hs.
  assert (a + b + a= b + (a + a)) as Hr by ring.
  rewrite Hr. clear Hr.
  rewrite BooleanAlgebraXplusX.
  ring.
Qed.

(*
Global Instance subsetPO :  orders.PartialOrder setSubset.
  constructor.
- destruct H. destruct ring_group. destruct abgroup_group.
  destruct group_monoid.
  destruct monoid_semigroup.
  exact sg_setoid.
Abort.
*)

Lemma paperEq2 : ∀ (x y u v : R),
  x*y + u*v ⊆ (x + u) ∪ (y + v).
Proof.
  intros ? ? ? ?.
  unfold setSubset.
  unfold setUnion, BooleanAlgUnion.
  unfold setIntersection, BooleanAlgIntersection.
  ring_simplify.
  ring_simplify.
  rewrite BooleanAlgebraXplusX.
  ring_simplify.
  repeat (rewrite boolean_mult).
  setoid_rewrite  <- (mult_assoc u v v).
  setoid_rewrite  <- (mult_assoc x y y).
  repeat (rewrite boolean_mult).
  ring_simplify.
  rewrite BooleanAlgebraXplusX.
  ring_simplify.
  setoid_rewrite  <- (mult_assoc (x*u)).
  repeat (rewrite boolean_mult).
  ring_simplify.
  rewrite BooleanAlgebraXplusX.
  ring_simplify.
  fold (plus).
  fold (one).
  ring_simplify.
  rewrite plus_0_r.
  rewrite mult_1_r.
  rewrite mult_1_r.
  reflexivity.
Qed.

(* Require Export MathClasses.orders.rings. *)
End BooleanAlgebraProps.

(*
Lemma BooleanAlgebraXplusXHint : ∀ (R : Type) (Ae : Equiv R) (Aplus : Plus R) (Amult : Mult R)
(Azero : Zero R) (Aone : One R) (Anegate : Negate R) 
(H0 : Ring R)
(H : BooleanAlgebra R)  (x : R), x + x = 0.
Proof.
  intros. apply BooleanAlgebraXplusX.
Qed.

Hint Rewrite BooleanAlgebraXplusXHint.
*)