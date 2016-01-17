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

Lemma reciperse_altL `{Field F} (x : F) Px : (// x↾Px) * x = 1.
Proof using. 
  rewrite commutativity.
  now rewrite <-(recip_inverse (x↾Px)). 
Qed.


Section FieldProps.
Context `{Field A}.
Add Ring tempRing : (stdlib_ring_theory A).
Require Import MathClasses.interfaces.orders.

Context `{Le A}
    `{@orders.SemiRingOrder A equiv plus mult zero one le}.
    
Context `{Lt A} {FPSRO:@FullPseudoSemiRingOrder A 
equiv apart plus mult zero one le lt}.

Require Import MathClasses.interfaces.orders.
Require Import MCMisc.rings.
Require Import Ring.

Lemma FieldLeRecipMultIff : forall 
  (a b k kinv : A),
  0 < k
  → kinv*k =1
  → (k*a ≤ b ↔ a ≤ kinv*b).
Proof using All.
  intros.
  apply RingLeRecipMultIff; eauto.
Qed.

Definition posrecip (k:A) (p:0<k): A.
  apply recip.
  exists k.
  apply apart_iff_total_lt.
  right. assumption.
Defined.

Lemma FieldLeRecipMultIff2 : forall 
  (a b k : A)
  (p:0 < k),
  let kinv := posrecip k p in
  (k*a ≤ b ↔ a ≤ kinv*b).
Proof using All.
  intros.
  apply FieldLeRecipMultIff; auto.
  apply reciperse_altL.
Qed.


End FieldProps.
