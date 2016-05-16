Set Suggest Proof Using.

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
(*Require Import atomicMoves.*)
Require Import IRMisc.LegacyIRRing.



  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).
  
Set Implicit Arguments.
(** Some proofs, especially about the space needed to execute 
  a sequence of moves, e.g. during parallel parking usually involve
  cases dependent on the car's geomtry. Some of those cases are
  unlikely, because a car's dimensions follow some pattern.
  For example, usually [lengthBack] is much smaller than [lengthFront].
  (recall that both of them are measured w.r.t. 
  the line joining the rear wheels.)
  
  To decide on which cases are unusual, in this file we
  record actual measurements for some cars.
  *)
Record CarGeometry (A:Type) := {
 carDim : CarDimensions A;
 minTR : A (**minimum turn radius, on either side*)
}.

Definition nonTrivialCarGeometry (cd : CarGeometry Q) : Prop := 
nonTrivialCarDim (carDim cd) /\ 0 < minTR cd.

Global Instance CastCarGeometry `{Cast A B} 
  : Cast (CarGeometry A) (CarGeometry B) :=
fun a =>  Build_CarGeometry
            ('carDim a)
            ('minTR a).

Open Scope Z_scope.
(**dimensions are in inches. always rounding up for safety. *)
Definition Mazda3Sedan2014sGT_Dim : CarDimensions Z := {|
  width := 37; (* excluding the side mirrors. fix! *)
  lengthBack := 36; 
  lengthFront := 142;
|}.

Locate βPlusFront.

Definition Mazda3Sedan2014sGT : CarGeometry Z := {|
  carDim := Mazda3Sedan2014sGT_Dim;
  (**  To measure this, I turned the steering wheel fully left and 
  executed a U turn in a single move, in a parking lot. During this,
  the midpoint of the car moved sideways by 300 inches 
  (about 2.75 parking slots, each 110 inches wide).
  This displacement is equal to the diameter of the circle in
  which the midpoint (of the line segment joining the rear wheels) 
  of the car was moving.
  *)
  minTR := 150
|}.

Definition Mazda3Sedan2014sGTWheelsBound : CarGeometry Z := {|
  carDim := {|
  width := 37; (* excluding the side mirrors -- which is okay unless the curb is too high *)
  lengthBack := 12 
  (* radius of wheel :=
     16/2 + 0.55*195mm converted to inches
http://www.mycarhelpline.com/images/Tyre_Size_details.png     
     *); 
  lengthFront := 142;
  |};
  (**  To measure this, I turned the steering wheel fully left and 
  executed a U turn in a single move, in a parking lot. During this,
  the midpoint of the car moved sideways by 300 inches 
  (about 2.75 parking slots, each 110 inches wide).
  This displacement is equal to the diameter of the circle in
  which the midpoint (of the line segment joining the rear wheels) 
  of the car was moving.
  *)
  minTR := 150
|}.

Example Mazda3Sedan2014sGT_dims : 
  let cdq := (cast _ (CarDimensions Q) (Mazda3Sedan2014sGT_Dim)) in
  let trq :Z := minTR Mazda3Sedan2014sGT in
  let w:Z := width Mazda3Sedan2014sGT_Dim in
  totalLength Mazda3Sedan2014sGT_Dim =178 
  /\ totalCarWidth Mazda3Sedan2014sGT_Dim =74
  /\
  let d :CR := (carDiagonal cdq) in
  let da : Z := R2ZApprox d (QposMake 1 100) in
  da = 193
  /\ da - totalLength Mazda3Sedan2014sGT_Dim = 15 /\
  let pb :CR:= (polarTheta (transpose (βPlusBack cdq trq))) in
  let mb :CR := (polarTheta (transpose (βMinusBack cdq trq))) in
  let dex : CR :=  ((norm (βMinusBack cdq trq)) * (CRcos.cos (pb+mb)))%mc in
  let dex2 : CR :=  ((norm (βMinusBack cdq trq)) * (CRcos.cos (mb)))%mc in
  11= approximateAngleAsDegrees pb
  /\ 18 = approximateAngleAsDegrees mb
  /\ 9 = (( trq) - w) - R2ZApprox dex (QposMake 1 100)
    (* 9 inches from the curb needed, else increase turn radius in second move,
      or don't hit the curb in first move.
     This assumes that the curb is a wall of \inf height. 
     Usually, the curb has much lower height (h).
     Consider the common case where 0<h<r, where r is the radius of the wheel.
     Then lengthBack should instead be half the length of the chord of the wheel
     (as a circle) that is formed by intersection of the horizontal plane that denotes
     the top surface of the curb.
     Use the following phythagoras equation: lengthBack^2 + (r-h)^2 = r^2
     Take the radius of the wheel as a safe approximation?
     See below.
      *)
  /\ 0 = (( trq) - w) - R2ZApprox dex2 (QposMake 1 100) (* sanity check *).
Proof using.
  vm_compute. dands; reflexivity.
Abort.

Example Mazda3Sedan2014sGTWheelsBound_dims : 
  let cdq := (cast _ (CarDimensions Q) (carDim Mazda3Sedan2014sGTWheelsBound)) in
  let trq :Z := minTR Mazda3Sedan2014sGTWheelsBound in
  let w:Z := width Mazda3Sedan2014sGT_Dim in
  let pb :CR:= (polarTheta (transpose (βPlusBack cdq trq))) in
  let mb :CR := (polarTheta (transpose (βMinusBack cdq trq))) in
  let dex : CR :=  ((norm (βMinusBack cdq trq)) * (CRcos.cos (pb+mb)))%mc in
  let dex2 : CR :=  ((norm (βMinusBack cdq trq)) * (CRcos.cos (mb)))%mc in
  4= approximateAngleAsDegrees pb
  /\ 6 = approximateAngleAsDegrees mb
  /\ 1 = (( trq) - w) - R2ZApprox dex (QposMake 1 100)
    (* 1 inches from the curb needed, else increase turn radius in second move,
      or don't hit the curb in first move.*)
  /\ 0 = (( trq) - w) - R2ZApprox dex2 (QposMake 1 100) (* sanity check *).
Proof using.
  vm_compute. dands; reflexivity.
Abort.

Close Scope Z_scope.
