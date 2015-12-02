

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


Global Instance EquivLine2D `{Equiv A} : Equiv (Line2D A) := 
  fun a b => lstart a = lstart b /\ lend a = lend b.


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