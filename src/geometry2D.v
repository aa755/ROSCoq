

Require Import ROSCOQ.Vector.

Require Export ROSCOQ.fastReals.interface.

Set Implicit Arguments.

Definition unitVec {R:Type} `{SinClass R}`{CosClass R} (θ : R) : Cart2D R 
  := {| X := cos θ; Y := sin θ |}.

Record Rigid2DState (A:Type): Type :=
{
  pos2D : Cart2D A;
  θ2D :  A
}.

(*Move the cartesian to polar
conversion to this file.*)


Record Line2D (A:Type):=
{
  lstart : Cart2D A;
  lend : Cart2D A
}.

Require Import MCMisc.PairLike.

Global Instance PairLikeLine2D (A:Type): 
    PairLike  (@Build_Line2D A) (@lstart A) (@lend A).
Proof.
  constructor; auto.
Qed.

Section LineInstances.
Context `{Ring A}.

Global Instance llll1 : Cast (Cart2D A) (Line2D A) :=
  @CastPairLikeSame _ _ _ _ _ (PairLikeLine2D A).

Global Instance llll2 : Equiv (Line2D A) :=
  @EquivPairLike _ _ _ _ _ _ (PairLikeLine2D A) _ _.

Global Instance llll3
 : Equivalence (@equiv  (Line2D A) _).
  apply (@EquivalencePairLike _ _ _ _ _ _ (PairLikeLine2D A));
  apply Equivalence_instance_Cart2D2.
Qed.

Global Instance llll4 : Proper (equiv ==> equiv) (@lstart A).
 eapply ProperPairLikeFst; eauto using typeclass_instances.
Qed.

Global Instance llll5 : Proper (equiv ==> equiv) (@lend A).
 eapply ProperPairLikeSnd; eauto using typeclass_instances.
Qed.

Global Instance llll6 : Zero (Line2D A).
  eapply ZeroPairLike; eauto.
Defined.

Global Instance llll7 : One (Line2D A).
 apply (@OnePairLike _ _ _ _ _ _  (PairLikeLine2D A));
   eauto with typeclass_instances.
Defined.

Global Instance llll8 : Plus (Line2D A).
 apply (@PlusPairLike _ _ _ _ _ _  (PairLikeLine2D A));
  apply Plus_instance_Cart2D.
Defined.

Global Instance MultLine : Mult (Line2D A).
 apply (@MultPairLike _ _ _ _ _ _  (PairLikeLine2D A));
  apply Mutt_instance_Cart2D.
Defined.

Global Instance NegateLine : Negate (Line2D A).
 apply (@NegatePairLike _ _ _ _ _ _  (PairLikeLine2D A));
   eauto with typeclass_instances.
Defined.

Global Instance RingLine : Ring (Line2D A).
 apply (@RingPairLike _ _ _ _ _ _  (PairLikeLine2D A)
  _ _ _ _ _ _   Ring_instance_Cart2D 
  _ _ _ _ _ _   Ring_instance_Cart2D).
Qed.

Global Instance ProperCastCartLine :
 Proper (equiv ==> equiv) (cast  (Cart2D A) (Line2D A)).
apply ProperCastPairLikeSame.
Qed.

Global Instance ProperLine2D : 
  Proper (equiv ==> equiv  ==> equiv) (@Build_Line2D A).
Proof.
  intros ? ? h1  ? ? h2. split; simpl; assumption.
Qed.

End LineInstances.


Global Instance castCRCart2DCR (R:Type): Cast R (Cart2D R) := sameXY.


Definition centredLineAtAngle {R:Type} `{SinClass R}`{CosClass R} `{Ring R} 
  (angle halfLength : R) (p: Cart2D R)
   : (Line2D R) := 
   let v := 'halfLength * (unitVec angle) in
   {| lstart := p-v ; lend := p+v |}.

Fixpoint linesConsecutive {A:Type}
   (pts : list (Cart2D A)): list (Line2D A) :=
match pts with
| nil => []
| h1::tl => match tl with
            | nil => []
            | h2::_ =>  {|lstart := h1 ; lend := h2|}::(linesConsecutive tl)
            end
end.


Definition BoundingRectangle := Line2D.

Global Instance SubsetBoundingRect `{Le A} : Subset (Line2D A) :=
  fun a b => lstart b ≤ lstart a /\ lend a ≤ lstart b.

Definition minCart `{MinClass A} (a b : Cart2D A) := 
  {|X:= min (X a) (X b); Y:= min (Y a) (Y b)|}.

Definition maxCart `{MaxClass A} (a b : Cart2D A) := 
  {|X:= max (X a) (X b); Y:= max (Y a) (Y b)|}.



Definition boundingUnion `{MinClass A}`{MaxClass A}
 (a b : BoundingRectangle A) : BoundingRectangle A:=
  {|lstart := minCart (lstart a) (lstart b); 
    lend := maxCart  (lend a) (lend b)|}.

Fixpoint computeBoundingRect `{MinClass A}`{MaxClass A} `{Zero A}
  (pts : list (Cart2D A)) : BoundingRectangle A :=
match pts with
| pt::[] => {|lstart := pt; lend := pt|}
| h::tl => let b := computeBoundingRect tl in
        boundingUnion b {|lstart := h; lend := h|}
| [] => {|lstart := 0; lend := 0|}
end.