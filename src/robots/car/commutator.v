(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)
(** printing ≡ $\equiv$ #≡# *)
(** printing [*] $*$ #*# *)
(** printing ∧ $\wedge$ #∧# *)
(** printing ∀ $\forall$ #∀# *)
(** printing → $\rightarrow$ #→# *)
(** printing ∃ $\exists$ #∃# *)
(** printing ≤ $\le$ #≤# *)
(** printing θ $\theta$ #θ# *)
(** printing eeev $\epsilon_v$ #∊ᵥ# *)
(** printing eeew $\epsilon_w$ #∊w# *)
(** printing tm $t_m$ #tm# *)
(** printing IR $\mathbb{R}$ #IR# *)
(** printing CR $\mathbb{R}$ #CR# *)
(** printing tr $t_r$ #tr# *)
(** remove printing * *)

(** printing ' $ $ #'# *)

Require Import Vector.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import ackermannSteering.
Require Import MCMisc.tactics.
Require Import CartIR.
Require Import ackermannSteering.
Require Import fastReals.interface.
Require Import fastReals.misc.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import ackermannSteeringProp.
Require Import MathClasses.orders.rings.
Require Import MathClasses.interfaces.orders.
Require Import ackermannSteeringProp.
Require Import atomicMoves.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.


(** conjugate of [b] by [a]*)
Definition conjugate `{ApartT R} `{Equiv R} `{Zero R} `{Negate R} 
  (b a: list (DAtomicMove R)) :=
  a++b++(-a).

Require Import MCMisc.rings.

(**use this to simpligy sidewaysMove.SidewaysAuxState*)
Lemma straightConjugateState : ∀  
  (a : list (DAtomicMove ℝ)) (d:ℝ)
  (init : Rigid2DState ℝ), 
  let stMid : Rigid2DState ℝ  
    := stateAfterAtomicMoves a init in
  stateAfterAtomicMoves (conjugate [mkStraightMove d] a) init
  = {|pos2D := pos2D init + ('d) * unitVec (θ2D stMid);
      θ2D := θ2D init |}.
Proof.
  intros ? ? ?. simpl.
  unfold stateAfterAtomicMoves, conjugate.
  rewrite fold_left_app.
  rewrite fold_left_app.
  simpl.
  fold stateAfterAtomicMoves.
  fold stateAfterAtomicMoves.
  pose proof (atomicMovesStateInvertible a) as H.
  unfold MovesStateInverse in H.
  specialize (H init (stateAfterAtomicMove
      (stateAfterAtomicMoves a init)
        (mkStraightMove d))).
  simpl in H.
  rewrite mult_0_l, plus_0_r in H.
  dimp H;[| reflexivity].
  repnd.
  rewrite <- RingShiftMinus in Hl.
  ring_simplify in Hl.
  destruct (stateAfterAtomicMoves (- a)
          (stateAfterAtomicMove (stateAfterAtomicMoves a init)
             (mkStraightMove d))) as [p t].
  simpl in *.
  apply RingNegateProper in Hl.
  ring_simplify in Hl.
  rewrite <- Hl, <- Hr.
  reflexivity.
Qed.

(*Move *)
Lemma carConfinedDuringAMSubset :
∀ cd a init r1 r2,
carConfinedDuringAM cd r1 a init
-> r1 ⊆ r2
-> carConfinedDuringAM cd r2 a init.
Proof.
  intros ? ? ? ? ? Hc Hs.
  destruct a as [a s].
  destruct s as [s|s]; simpl in *.
- unfold straightAMSpaceRequirement.
  eapply transitivity;[apply Hc| apply Hs].
- intros ? Hb. specialize (Hc _ Hb).
  eapply transitivity;[apply Hc| apply Hs].
Qed.

Lemma carConfinedDuringAMsSubset :
∀ cd r1 r2 a init,
carConfinedDuringAMs cd r1 a init
-> r1 ⊆ r2
-> carConfinedDuringAMs cd r2 a init.
Proof.
  induction a; intros ? Hc Hs; simpl in *.
- eapply transitivity;[apply Hc| apply Hs].
- repnd. split; eauto using carConfinedDuringAMSubset.
Qed.


Lemma straightConjugateSpace : ∀  (cd : CarDimensions ℝ)
  (a : list (DAtomicMove ℝ)) (d:ℝ)
  (init : Rigid2DState ℝ)
  (confineRect: Line2D IR), 
  let stMid : Rigid2DState ℝ  
    := stateAfterAtomicMoves a init in
  let cm := (conjugate [mkStraightMove d] a) in
  let rectR := confineRect + '(('d) * unitVec (θ2D stMid)) in
  let cmr := boundingUnion confineRect rectR in
carConfinedDuringAMs cd confineRect a init
-> carConfinedDuringAMs cd cmr cm init.
Proof.
  intros ? ? ? ? ?.
  simpl. intros Hc.
  apply strMoveSandwichedConfined.
- eapply carConfinedDuringAMsSubset;
    [apply Hc| apply  boundingUnionLeft].
- eapply carConfinedDuringAMsSubset;
    [| apply  boundingUnionRight].
  pose proof (atomicMovesSpaceInvertible a init
  (stateAfterAtomicMoves (a ++ [mkStraightMove d]) init)
  cd confineRect)
  as Hs. simpl in Hs.
  unfold stateAfterAtomicMoves in Hs.
  rewrite <- fold_left_app in Hs.
  fold stateAfterAtomicMoves in Hs.
  rewrite <- app_assoc in Hs.
  fold (conjugate [mkStraightMove d] a) in Hs.
  rewrite straightConjugateState in Hs.
  unfold stateAfterAtomicMoves in Hs.
  rewrite fold_left_app  in Hs at 1.
  repeat (progress fold stateAfterAtomicMoves in Hs).
  simpl in Hs.
  rewrite mult_0_l, plus_0_r in Hs.
  dimp Hs;[|reflexivity].
  specialize (Hs Hc). clear Hc.
  ring_simplify
    (pos2D init +
           ' d *
           unitVec (θ2D (stateAfterAtomicMoves a init)) -
           pos2D init) in Hs.
  exact Hs.
Qed.
