Section RingMisc.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MCMisc.tactics.
Require Import Ring.

(**some miscelleneous convenience props about rings.*)
Context `{Ring A}.
Add Ring tempRing : (stdlib_ring_theory A).

Lemma RingShiftMinusR  : forall 
  a b c : A,
  a - b  = c -> a = b+ c.
Proof.
  intros ? ? ?  Hh.
  (**the ring tactic does not seem to look at hyps*)
  rewrite <- Hh. 
  ring.
Qed.

End RingMisc.
