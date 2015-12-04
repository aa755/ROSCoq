Require Import geometry2D.
Require Import Vector.
Require Import fastReals.misc.
Require Import MCInstances.
Require Import fastReals.interface.

Open Scope mc_scope.


Lemma Min_plusl: ∀ a b c : ℝ, min (c + a) (c + b) =  c + min a b.
Proof.
  intros.
  rewrite (plus_comm c).
  rewrite (plus_comm c).
  setoid_rewrite Min_plus.
  rewrite (plus_comm c).
  reflexivity.
Qed.

Lemma Max_plusl: ∀ a b c : ℝ, max (c + a) (c + b) =  c + max a b.
Proof.
  intros.
  rewrite (plus_comm c).
  rewrite (plus_comm c).
  setoid_rewrite max_plus.
  rewrite (plus_comm c).
  reflexivity.
Qed.

Lemma minCartSum : forall c a b : Cart2D IR,
  minCart (c+a) (c+b) = c + minCart a b.
Proof.
  intros. unfold minCart. simpl.
  rewrite Min_plusl.
  rewrite Min_plusl.
  split; reflexivity.
Qed.

Lemma maxCartSum : forall c a b : Cart2D IR,
  maxCart (c+a) (c+b) = c + maxCart a b.
Proof.
  intros. unfold maxCart. simpl.
  rewrite Max_plusl.
  rewrite Max_plusl.
  split; reflexivity.
Qed.

Global Instance ProperMinCart : 
  Proper (equiv ==> equiv  ==> equiv) (@minCart IR _).
Proof.
  intros ? ? h1  ? ? h2.
  destruct h1. destruct h2.
  split; simpl; apply Max_AbsIR.Min_wd_unfolded; tauto.
Qed.

Global Instance ProperMaxCart : 
  Proper (equiv ==> equiv  ==> equiv) (@maxCart IR _).
Proof.
  intros ? ? h1  ? ? h2.
  destruct h1. destruct h2.
  split; simpl; apply Max_AbsIR.Max_wd_unfolded; tauto.
Qed.

Global Instance AssociativeMinIR : `{Associative  (@min IR _)}.
  intros ? ? ?. apply MinAssoc.
Qed.

Global Instance AssociativeMaxIR : `{Associative  (@max IR _)}.
  intros ? ? ?. apply MaxAssoc.
Qed.

Global Instance AssociativeMinCart `{MinClass R} `{Associative _ (@min R _)}: 
  Associative  (@minCart R _).
Proof.
  intros ? ? ?. split; simpl;
  apply simple_associativity.
Qed.

Global Instance AssociativeMaxCart `{MaxClass R} `{Associative _ (@max R _)}: 
  Associative  (@maxCart R _).
Proof.
  intros ? ? ?. split; simpl;
  apply simple_associativity.
Qed.

Global Instance CommutativeMinIR : `{Commutative  (@min IR _)}.
  intros ? ?. apply Min_comm.
Qed.

Global Instance CommutativeMaxIR : `{Commutative  (@max IR _)}.
  intros ? ?. apply Max_comm.
Qed.

Global Instance CommutativeMinCart `{MinClass R} `{Commutative _ _ (@min R _)}: 
  Commutative  (@minCart R _).
Proof.
  intros ? ?. split; simpl;
  apply commutativity.
Qed.

Global Instance CommutativeMaxCart `{MaxClass R} `{Commutative _ _ (@max R _)}: 
  Commutative  (@maxCart R _).
Proof.
  intros ? ?. split; simpl;
  apply commutativity.
Qed.

Hint Unfold cos CosClassIR sin SinClassIR min MinClassIR max MaxClassIR: IRMC.

Require Import IRTrig.
Lemma unitVecNonNeg : forall θ, 0 ≤ θ ≤ (½ * π)
  -> 0 ≤ unitVec θ.
Proof.
  intros ? hh.
  pose proof (less_leEq ℝ [0] Pi pos_Pi) as h.
  apply nonneg_div_two' in h.
  autounfold with IRMC in hh.
  unfold Zero_instance_IR in hh.
  destruct hh as [x y]. 
  rewrite PiBy2DesugarIR in y.
  pose proof MinusPiBy2Le0.
  split; simpl;
  [apply Cos_nonneg | apply Sin_nonneg]; eauto 3 with CoRN.
Qed.

  Lemma unitVecMinus90 :  ∀ θ:IR, 
    unitVec (θ - ½ * π) = {|X:= sin θ; Y:=- cos θ|}.
  Proof.
    intros ?. split; simpl;
    autounfold with IRMC.
    - rewrite <- Cos_inv.
      setoid_rewrite minusInvR.
      rewrite PiBy2DesugarIR.
      apply Cos_HalfPi_minus.
    - rewrite <- (cg_inv_inv _ (Sin (θ [+] [--] (½ [*] π)))).
      rewrite <- Sin_inv.
      setoid_rewrite minusInvR.
      rewrite PiBy2DesugarIR.
      rewrite Sin_HalfPi_minus.
      reflexivity.
  Qed.

Lemma unitVecMinDistr :  forall θ a b:IR, 0 ≤ θ ≤ (½ * π)
  ->
  minCart ((unitVec θ) * 'a) ((unitVec θ) * 'b)
     = (unitVec θ) * '(min a b).
Proof.
  intros ? ? ? hh.
  apply unitVecNonNeg in hh. unfold unitVec in hh.
  destruct hh as [x y]. simpl in x, y. 
  unfold minCart. split; simpl;
  autounfold with IRMC;
  rewrite MinMultLeft; try reflexivity; try assumption.
Qed.


Lemma unitVecMaxDistr :  forall θ a b:IR, 0 ≤ θ ≤ (½ * π)
  ->
  maxCart ((unitVec θ) * 'a) ((unitVec θ) * 'b)
     = (unitVec θ) * '(max a b).
Proof.
  intros ? ? ? hh.
  apply unitVecNonNeg in hh. unfold unitVec in hh.
  destruct hh as [x y]. simpl in x, y. 
  unfold maxCart. split; simpl;
  autounfold with IRMC;
  rewrite MaxMultLeft; try reflexivity; try assumption.
Qed.
