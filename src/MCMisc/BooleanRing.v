Require Export MathClasses.theory.rings.
Require Export MathClasses.interfaces.abstract_algebra.
Require Import Ring.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.interfaces.orders.
Require Export MathClasses.orders.rings.
Class BooleanRing (A:Type) `{Ring A} :=
  boolean_mult : ∀ x:A, x*x=x.

Section BooleanRingNotations.

Context `{BooleanRing R}.

Require Export SetNotations.

Global Instance BooleanAlgUnion : SetUnion R :=
    λ (a b : R), a + b + a*b .
Global Instance BooleanAlgIntersection : SetIntersection R :=
    mult.


Notation "b \ x " := (b + b * x) (at level 100).

Notation "x ᶜ  " := (1 \ x) (at level 100).

End BooleanRingNotations.

Section BooleanRingProps.
  Context `{BooleanRing R}.

Add Ring  stdlib_ring_theoryldsjfsd : (rings.stdlib_ring_theory R).


Lemma BooleanRingXplusX : ∀ (x : R), x + x = 0.
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

Lemma BooleanRingMinusX : ∀ (x : R), - x = x.
Proof.
  intros x.
  apply equal_by_zero_sum.
  rewrite <- negate_plus_distr.
  rewrite BooleanRingXplusX.
  ring.
Qed.

Lemma BooleanRing1Max : ∀ (x : R), x ⊆ 1.
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
  rewrite BooleanRingXplusX.
  ring_simplify.
  repeat (rewrite boolean_mult).
  setoid_rewrite  <- (mult_assoc u v v).
  setoid_rewrite  <- (mult_assoc x v v).
  setoid_rewrite  <- (mult_assoc y u u).
  setoid_rewrite  <- (mult_assoc x y y).
  repeat (rewrite boolean_mult).
  ring_simplify.
  rewrite BooleanRingXplusX.
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
  rewrite BooleanRingXplusX.
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
  rewrite BooleanRingXplusX.
  ring_simplify.
  repeat (rewrite boolean_mult).
  setoid_rewrite  <- (mult_assoc u v v).
  setoid_rewrite  <- (mult_assoc x y y).
  repeat (rewrite boolean_mult).
  ring_simplify.
  rewrite BooleanRingXplusX.
  ring_simplify.
  setoid_rewrite  <- (mult_assoc (x*u)).
  repeat (rewrite boolean_mult).
  ring_simplify.
  rewrite BooleanRingXplusX.
  ring_simplify.
  fold (plus).
  fold (one).
  ring_simplify.
  rewrite plus_0_r.
  rewrite mult_1_r.
  rewrite mult_1_r.
  reflexivity.
Qed.

Require Import tactics.

Lemma normalizeEq2 : forall (a b:R),
 (a = b) <-> a + b= 0.
Proof.
  split; intro Hyp.
- rewrite Hyp. rewrite BooleanRingXplusX. ring.
- fequivHyp Hyp (plus a).
  ring_simplify in Hype. rewrite BooleanRingXplusX in Hype.
  ring_simplify in Hype. auto.
Qed.

Lemma normalizeEq : forall (a b:R),
 (a = b) <-> a + b + 1 = 1.
Proof.
  split; intro Hyp.
- rewrite Hyp. rewrite BooleanRingXplusX. ring.
- rewrite normalizeEq2. fequivHyp Hyp (plus 1). clear Hyp.
  rewrite BooleanRingXplusX in Hype.
  ring_simplify in Hype. rewrite BooleanRingXplusX in Hype.
  ring_simplify in Hype. assumption.
Qed.




(* doesn't seem to hold for all boolean rings rings 
Lemma elimEqHyp : forall (h c:R),
  (h = 1 -> c = 1) <-> (h * c + h + 1 = 1).
Proof.
  intros. rewrite <- normalizeEq.
  split; intro Hyp.
- SearchAbout mult Ring. Print RightCancellation. 
*)

(* Require Export MathClasses.orders.rings. *)
End BooleanRingProps.
