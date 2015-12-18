Section RingMisc.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MCMisc.tactics.
Require Import Ring.

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


End Le.


End RingMisc.
