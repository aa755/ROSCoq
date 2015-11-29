Require Export ROSCOQ.fastReals.interface.


Require Import ROSCOQ.Vector.

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
