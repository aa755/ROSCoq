Require Import CartCR.
Require Import MCInstances.
Require Import IRMisc.LegacyIRRing.


(**Ideally, this file should be a part of CartIR.v
However, many other old files depend on CartIR.v,
and changing it may break stuff. Eventually 
this file should be apended to it. *)

Require Import CartIR.
Require Import geometry2D.
Require Import geometry2DProps.
Require Import MathClasses.interfaces.vectorspace.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCMisc.tactics.
Hint Unfold One_instance_IR : IRMC.

Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Global Instance castPolar `{Cast A B} 
  : Cast (Polar2D A) (Polar2D B) :=
  fun c => {|rad := cast A B (rad c) ;  θ := cast A B (θ c) |}.

Global Instance cart2PolarIR : Cast (Cart2D Q) (Polar2D IR):=
fun c => '(Cart2Polar c).

Global Instance NormCart2DQ : Norm IR (Cart2D Q)
 := fun c => '(|c|).

Require Import fastReals.interface.
Require Import fastReals.misc.

Definition polar2CartIR (c:Polar2D IR) : Cart2D IR :=
  '(rad c) * (unitVec (θ c)).
  
Lemma CartToPolarCorrect : ∀ (q : Cart2D Q),
  let θ:IR := '(polarTheta q) in 
  'q  = '(∥q∥) * (unitVec θ).
Proof.
  intros ?. simpl.
  apply CartToPolarToXIR.
Qed.

Lemma CartToPolarCorrect2 : ∀ (q : Cart2D Q),
  'q  = polar2CartIR (cart2PolarIR (q)).
Proof.
  intros ?. simpl.
  apply CartToPolarToXIR.
Qed.

Lemma multDotRight : forall (a:IR) (b c : Cart2D IR),
a * (⟨b,c⟩) = ⟨('a) * c, b⟩.
Proof using.
  intros.   unfold inprod, InProductCart2D.
  simpl. IRring.
Qed.


Lemma CartToPolarCorrect90Minus : ∀ (q : Cart2D Q),
  let θ:IR := '(polarTheta q) in 
  (transpose ('q))  = '(∥q∥) * (unitVec (½ * π -θ)).
Proof using.
  intros ?. simpl.
  setoid_rewrite unitVec90Minus at 1.
  unfold transpose.
  rewrite CartToPolarCorrect.
  simpl. reflexivity.
Qed.

Lemma unitVDot : ∀ (α β:IR) ,
  ⟨unitVec α, unitVec β⟩
  = cos (α-β).
Proof.
  intros ? ?.
  unfold inprod, InProductCart2D, unitVec.
  simpl.
  symmetry.
  apply Cos_minus.
Qed.


Lemma unitVDot2 : ∀ (α β:IR) ,
  ⟨ {|X:=1;Y:=-1|} * unitVec α , unitVec β⟩
  = cos (α+β).
Proof.
  intros ? ?.
  unfold inprod, InProductCart2D, unitVec.
  simpl. autounfold with IRMC.
  rewrite  Cos_plus.
  IRring.
Qed.


