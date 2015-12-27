Require Import MathClasses.theory.fields.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

Lemma equal_quotientsl `{Field A}
(a c: A) b : a = c * `b ↔ a // b = c.
Proof.
  intros.
  pose proof (fields.reciperse_alt (1:A)) as Hh.
  simpl in Hh.
  specialize (Hh (@field_nontrivial A _ _ _ _ _ _ _ _ _)).
  rewrite <- (rings.mult_1_r c) at 2.
  rewrite <- Hh.
  rewrite (@simple_associativity _ _ mult _ _).
  rewrite rings.mult_1_r.
  rewrite <- fields.equal_quotients.
  simpl. rewrite rings.mult_1_r.
  tauto.
Qed.