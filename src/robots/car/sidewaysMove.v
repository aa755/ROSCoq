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
Require Import atomicMoves.
Require Import IRMisc.LegacyIRRing.
Require Import wriggle.
Hint Unfold One_instance_IR : IRMC.

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  Local Notation  "∫" := Cintegral.
  Local Notation ConfineRect := (Line2D).

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Section Sideways.


(** * The sideways move

Adding just one atomic move to the [SidewaysAux] move defined below
will get us to the sideways move. After [SidewaysAux],
as we will prove,
the car's orientation is same as that in the original state, but
it's position has shifted a bit, both along the car's orientaition and orthogonal to it.
[SidewaysAux] is just a straight-drive move inserted between
a wriggle and its inverse.
Note that without this insertion, we would have been back
to where we started.
*)
  Variable α : IR.
  Hypothesis tcNZ : α[#]0.
  Variable d : IR.
  Variable d' : IR.
  
  Local Notation SWriggle := (Wriggle α tcNZ d).
  
  Require Import commutator.
  (** Drive a distance of [ddistance]
    with front wheels perfectly straight.*)  
  Definition SidewaysAux : list (DAtomicMove  IR) 
    := conjugate [mkStraightMove d'] SWriggle.

  (** The car's orientation at the end is same as that at the start.
     [θAtW] denotes the car's orientation at the completion of the [SWriggle] move. 
     For any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
     *)
  Definition sidewaysDisp (init : Rigid2DState ℝ) : Cart2D IR :=
     '(d') * unitVec ((θ2D init) + 2 * α * d).

  Lemma SidewaysAuxState : forall init,
  stateAfterAtomicMoves SidewaysAux init
  = {|pos2D := pos2D init 
      + sidewaysDisp init;
      θ2D := θ2D init |}.
  Proof using.
    intros.
    unfold SidewaysAux.
    rewrite straightConjugateState.
    rewrite WriggleState.
    simpl.
    reflexivity.
  Qed.

    Local Opaque conjugate.
    Local Opaque Wriggle.
  
  Definition sidewaysRect (w1rect : Line2D IR) (init : Rigid2DState ℝ) :=
  let w2rect := w1rect + 'sidewaysDisp init in
  boundingUnion w1rect w2rect.
  
  Lemma SidewaysAuxSpace :
  ∀  (cd : CarDimensions ℝ)
  (init : Rigid2DState ℝ)
  (w1rect: Line2D IR), 
carConfinedDuringAMs cd w1rect SWriggle init
-> carConfinedDuringAMs cd (sidewaysRect w1rect init) SidewaysAux init.
  Proof using.
    intros ? ? ?. simpl. intros H.
    eapply straightConjugateSpace with (d:=d')in H.
    rewrite WriggleState in H.
    simpl in H.
    exact H.
  Qed.

  (** After [SidewaysAux], the car is in the same orientation as before, but it has position
    has changed. For a sideways move, we just have drive straight to cancel
    the component of that position change along the car's orientation.
    We get this component by taking the dot product of the position change with the unit vector
    along the car's orientation.
    Formally, a sideways move is one where the car's position shifts in a direction
    orthogonal to its orientation.
    *)
  Local Notation DriveStraightRev 
    := (mkStraightMove (- d' * cos (2 * α * d))).

  Definition SidewaysMove : list (DAtomicMove  IR) 
    := SidewaysAux ++ [DriveStraightRev].
    
  (** The car's final orientation is same as before, and 
  its position changes in the direction that is at a right angle [(½ * π)]
  to its orientation, i.e., it is a sideways move. 
  The distance moved is [ddistance * Sin  θw].

  As mentioned before, for any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
  *)

(* maybe delete from CartIR *)
Lemma unitVecLemma1 : forall θs θw:IR, 
  (unitVec (θs + θw)  - '(cos θw) * unitVec θs)
  = ('(sin  θw)) * unitVec (θs + (½ * π)).
Proof using.
  intros ? ?.
  unfold cast,castCRCart2DCR,
     sameXY, unitVec.   autounfold with IRMC.
  rewrite PiBy2DesugarIR.  
  rewrite Sin_plus_HalfPi.
  rewrite Cos_plus_HalfPi.
  simpl. split; simpl; autounfold with IRMC;
  [rewrite Cos_plus | rewrite Sin_plus]; try IRring.
Qed.

    Local Opaque SidewaysAux.
  Lemma SidewaysState : forall init,
  let θw := 2 * α * d  in
  stateAfterAtomicMoves SidewaysMove init
  = {|pos2D := pos2D init 
      + ('(d' * sin  θw)) * unitVec (θ2D init + (½ * π));
      θ2D := θ2D init |}.
  Proof using Type.
    intros ?.
    simpl.
    unfold SidewaysMove, mkStraightMove,
      stateAfterAtomicMoves.
    rewrite fold_left_app.
    simpl.
    fold stateAfterAtomicMoves.
    rewrite SidewaysAuxState.
    unfold stateAfterAtomicMove.
    simpl. unfold sidewaysDisp.
     rewrite mult_0_l, plus_0_r.
    split;[| reflexivity].
    simpl. 
    rewrite <- (@simple_associativity  _ _ plus _ _).
    fequiv.
    remember (2 * α * d) as θw. clear Heqθw.
    rewrite <- negate_mult_distr_l.
    rewrite  preserves_negate.
    rewrite  preserves_mult.
    rewrite negate_mult_distr_r.
    rewrite <- (@simple_associativity _ _ mult _ _ _).
    rewrite <- (@simple_distribute_l _ _  mult plus _ _ _ _).
    rewrite <- negate_mult_distr_l.
    rewrite unitVecLemma1.
    rewrite  preserves_mult.
     ring.
  Qed.
  (** * space analysis *)
End Sideways.

Section SidewaysSpace.

Variable α : Q.
Hypothesis αPos : ' α [#] (0 : ℝ).
Variable d : Q.
Variable cd : CarDimensions Q.
Hypothesis ntriv : nonTrivialCarDim cd.
Hypothesis firstQuadW : (0 : ℝ) ≤ 2 * ' α * ' d ≤ ½ * π.
Let tr := (/ α)%Q : Q.

Hypothesis turnCentreOut : (width cd <= tr)%Q.

Let αNZ := αPos : ' α [#] (0 : ℝ).
Let βMinusBack := βMinusBack cd tr : Cart2D Q.
Let βMinusFront := βMinusFront cd tr : Cart2D Q.
Let βPlusBack := βPlusBack cd tr : Cart2D Q.
Let βPlusFront := βPlusFront cd tr : Cart2D Q.
Hypothesis lengthFrontGreater : (lengthBack cd <= lengthFront cd)%Q.
Hypothesis  maxNeededTurn : (0 : ℝ) ≤ 2 * ' α * ' d ≤ ' polarTheta βPlusFront.

Let adNN := adNN (' α) (' d) firstQuadW : 0 ≤ ' α * ' d.


Variable d':IR.
Hypothesis d'NN : 0 ≤ d'.

Let sidewaysMove : list (DAtomicMove  IR) 
  := SidewaysAux ('α) αNZ ('d) (d').

Print WriggleSpaceFirstQ.

Let WriggleSpaceFirstQ := WriggleSpaceFirstQ α d cd.

Definition sidewaysRectFirstQ bottomBound :=
(sidewaysRect  ('α) ('d) (d') (WriggleSpaceFirstQ bottomBound) 0).

Print minYCriticalAngle.

Let bottomBoundCase1 := bottomBoundCase1 α d cd.
Let bottomBoundCase2 := bottomBoundCase2 α d cd.
Let minYCriticalAngle := minYCriticalAngle α cd.

Lemma SidewaysSpaceFirstQCase1Correct :
('α * 'd ≤ minYCriticalAngle)
→ carConfinedDuringAMs ('cd) 
    (sidewaysRectFirstQ bottomBoundCase1)
    sidewaysMove
    (0 : Rigid2DState ℝ).
Proof using firstQuadW  maxNeededTurn
     ntriv turnCentreOut αNZ lengthFrontGreater.
  intro Hcase1. unfold sidewaysRectFirstQ.
  apply SidewaysAuxSpace.
  apply WriggleSpaceFirstQCase1Correct; auto.
Qed.

Lemma SidewaysConfineRectFirstQCase2Correct :
(minYCriticalAngle ≤ 'α * 'd)
→ carConfinedDuringAMs ('cd) 
    (sidewaysRectFirstQ bottomBoundCase2)
    sidewaysMove
    (0 : Rigid2DState ℝ).
Proof using firstQuadW lengthFrontGreater 
    maxNeededTurn ntriv turnCentreOut αNZ.
  intro Hcase1. unfold sidewaysRectFirstQ.
  apply SidewaysAuxSpace.
  apply WriggleSpaceFirstQCase2Correct;
  assumption.
Qed.

Lemma sidewaysRectFirstQSimpl1 : forall  b,
sidewaysRectFirstQ b =
  {| minxy := minxy (WriggleSpaceFirstQ b);
     maxxy := maxxy (WriggleSpaceFirstQ b) + ' (d') * unitVec (2 * ' α * ' d)
  |}.
Proof using d'NN firstQuadW.
  intro. unfold sidewaysRectFirstQ, sidewaysRect.
  unfold sidewaysDisp.
  simpl θ2D.
  rewrite plus_0_l.  
  rewrite unionWithNonNegDisplacement;[reflexivity|].
  apply nonneg_mult_compat; unfold PropHolds;[split; assumption|].
  apply unitVecNonNeg.
  assumption.
Qed.

Let leftBound := leftBound α d cd.
Let rightBound := rightBound α d cd.

Definition sidewaysTotalSpaceX : IR :=
rightBound - leftBound +  (d') * cos (2 * ' α * ' d).

Lemma sidewaysTotalSpaceXCorrect : forall  b,
totalSpaceX (sidewaysRectFirstQ b) =
 rightBound - leftBound +  (d') * cos (2 * ' α * ' d).
Proof using d'NN firstQuadW.
  intro. unfold totalSpaceX, sidewaysTotalSpaceX.
  rewrite sidewaysRectFirstQSimpl1. simpl.
  unfold rightBound, leftBound.
  IRring.
Qed.

Print extraSpaceX1.

Definition extraSpaceXSidewaysCase1 
`{CosClass R} `{Ring R}
`{Cast (Cart2D Q) (Polar2D R)}
`{Cast Q R} (d d':R) : R :=
extraSpaceX1 α cd ('α *  d)
+  d'* cos (2 * 'α *  d).

Let leftCriticalAngle := leftCriticalAngle α cd.

Lemma extraSpaceXSidewaysCase1Correct :
' α * ' d ≤ leftCriticalAngle
->
extraSpaceXSidewaysCase1 ('d) d'=
sidewaysTotalSpaceX 
- ' totalLength cd (** subtracting the initially needed space*).
Proof using  firstQuadW ntriv turnCentreOut  αNZ.
  intros Hle. unfold extraSpaceXSidewaysCase1.
  rewrite <- extraSpaceXWriggleCase1Simpl2; auto.
  rewrite extraSpaceXWriggleCase1Correct; auto.
  unfold extraSpaceXWriggle, leftExtraSpaceWriggle, rightExtraSpaceWriggle,
    sidewaysTotalSpaceX.
  unfold totalLength.
  rewrite preserves_plus.
  unfold rightBound, leftBound.
  IRring.
Qed.

End SidewaysSpace.
