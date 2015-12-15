

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

Require Import MCMisc.PairLike.

Section Rigid2DStateInstances.
Context `{Ring A}.


Global Instance PairLikeRigid2DState (A:Type): 
    PairLike  (@Build_Rigid2DState A) (@pos2D A) (@θ2D  A).
Proof.
  constructor; auto.
Qed.

Global Instance EquivRigid2D : Equiv (Rigid2DState A) :=
  @EquivPairLike _ _ _ _ _ _ (PairLikeRigid2DState A) _ _.

Global Instance EquivalenceRigid2D
 : Equivalence (@equiv  (Rigid2DState A) _).
  apply (@EquivalencePairLike _ _ _ _ _ _ (PairLikeRigid2DState A)).
  eauto using Equivalence_instance_Cart2D2.
  split; auto.
Qed.

Global Instance ProperPos2D : Proper (equiv ==> equiv) (@pos2D A).
 eapply ProperPairLikeFst; eauto using typeclass_instances.
Qed.

Global Instance Properθ2D : Proper (equiv ==> equiv) (@θ2D A).
 eapply ProperPairLikeSnd; eauto using typeclass_instances.
Qed.

Global Instance ZeroRigid2D : Zero (Rigid2DState A).
  eapply ZeroPairLike; eauto.
Defined.

Global Instance OneRigid2D : One (Rigid2DState A).
 apply (@OnePairLike _ _ _ _ _ _  (PairLikeRigid2DState A));
   eauto with typeclass_instances.
Defined.

Global Instance PlusRigid2D : Plus (Rigid2DState A).
 apply (@PlusPairLike _ _ _ _ _ _  (PairLikeRigid2DState A));
  [apply Plus_instance_Cart2D| assumption].
Defined.

Global Instance MultRigid2D : Mult (Rigid2DState A).
 apply (@MultPairLike _ _ _ _ _ _  (PairLikeRigid2DState A));
  [apply Mutt_instance_Cart2D| assumption].
Defined.

Global Instance NegateRigid2D : Negate (Rigid2DState A).
 apply (@NegatePairLike _ _ _ _ _ _  (PairLikeRigid2DState A));
   eauto with typeclass_instances.
Defined.

Global Instance RingRigid2D : Ring (Rigid2DState A).
 apply (@RingPairLike _ _ _ _ _ _  (PairLikeRigid2DState A)
  _ _ _ _ _ _   Ring_instance_Cart2D 
  _ _ _ _ _ _   _).
Qed.


Global Instance ProperRigid2DState : 
  Proper (equiv ==> equiv  ==> equiv) (@Build_Rigid2DState A).
Proof.
  intros ? ? h1  ? ? h2. split; simpl; assumption.
Qed.

End Rigid2DStateInstances.

Record Line2D (A:Type):=
{
  lstart : Cart2D A;
  lend : Cart2D A
}.


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

Instance srmSameStartEnd `{Ring A} : SemiRing_Morphism (cast (Cart2D A) (Line2D A)).
Proof.
repeat (split; try apply _); reflexivity.
Qed.



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

Global Instance LeAsSubset `{Le A} : Le (Line2D A) :=
  fun a b => lstart b ≤ lstart a /\ lend a ≤ lend b.


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

    
Require Import CoRN.logic.Stability.

Global Instance StableSubsetLine2D `{Le A} : 
    (forall x y : A, Stable (x≤y))
    -> (forall a b : Line2D A, Stable (a ≤ b)).
Proof.
     intros Hc a b.
     apply stable_conjunction; eauto using StableLeCart2D.
Qed.

Require Import MathClasses.interfaces.orders.

Infix "⊆" := (@le _ LeAsSubset)  (at level 70, no associativity): mc_scope.

Global Instance LeSubsetPreorder `{Ring A}
  `{l:Le A} `{PreOrder A l}
  : @PreOrder (Line2D A) LeAsSubset.
Proof.
  split; intros ?; unfold le, LeAsSubset;
   eauto 2 with typeclass_instances;[].
  intros a b ? ?. repnd. split;
  eauto with relations typeclass_instances.
Qed.


Global Instance PartialOrderSubset `{Ring A}  `{l: Le A}
  `{@PartialOrder A equiv l} :
      @PartialOrder (Line2D A) _ _.
Proof.
  split; eauto with typeclass_instances.
  - split; eauto with typeclass_instances.
  - intros ? ? H1e ? ? H2e; unfold le,LeAsSubset.
    rewrite H1e,  H2e. tauto.
  - intros ? ?. unfold le, LeAsSubset. intros ? ?.
    repnd. split; simpl; eapply  po_antisym; eauto.
Qed.

(* Exact same proof as Vector.MultLeSemiRingOrderCart2D,
    except for LeAsSubset *)
Global Instance OrderPreservingLePlusCart2D
  `{Ring A} `{Le A}
    `{@orders.SemiRingOrder A equiv plus mult zero one le}
  (z : Line2D A): 
  OrderPreserving (plus z).
Proof.
  split; eauto  with typeclass_instances.
  - split; eauto with typeclass_instances.
    split;  eauto with typeclass_instances;
    split;  eauto with typeclass_instances.
  - intros ? ?. unfold le, LeAsSubset.
    intros. repnd;
    simpl.
    split;
    eauto with typeclass_instances.
Qed.

Require Import MathClasses.orders.rings.
(** does not hold for subset
Global Instance MultLeSemiRingOrderCart2D
  `{Ring A} `{Le A}
    `{@orders.SemiRingOrder A equiv plus mult zero one le} :  
  ∀ x y : (Line2D A) , PropHolds (0 ≤ x) 
      → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y)
 .
Proof.
    unfold le, LeAsSubset, PropHolds.
    simpl.
    intros. repnd; 
    simpl.
    split.
    - NOT TRUE
    - eapply nonneg_mult_compat; assumption.  
Qed.
*)

Global Instance SemiRingorderLeCart `{Ring A} `{Le A}
    `{@orders.SemiRingOrder A equiv plus mult zero one le}:
    `{orders.SemiRingOrder (@canonical_names.le (Cart2D A) _)}.
Proof.
  apply from_ring_order;
  eauto with typeclass_instances.
Qed.

Lemma foldPlusLine `{Ring A} : forall xa xb ya yb: Cart2D A,
   {| lstart := xa + xb; lend :=ya + yb |} = {|lstart :=xa; lend :=ya|} 
    + {|lstart:=xb; lend:=yb|}.
  Proof.
    intros. reflexivity.
  Qed.

