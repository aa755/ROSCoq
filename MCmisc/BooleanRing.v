Require Export MathClasses.theory.rings.
Require Export MathClasses.interfaces.abstract_algebra.
Require Import Ring.
Require Export MathClasses.interfaces.canonical_names.

Class BooleanRing `{Ring A} :=
  boolean_mult : ∀ x:A, x*x=x.

Section BoolRingProps.
  Context `{BooleanRing R}.

Add Ring  stdlib_ring_theoryldsjfsd : (rings.stdlib_ring_theory R).


Lemma BooleanRingXplusX : ∀ (x : R), x + x =0.
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

End BoolRingProps.
