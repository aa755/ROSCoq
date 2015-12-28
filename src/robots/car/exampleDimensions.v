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
Require Import atomicMoves.
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

Global Instance CastCarGeometry `{Cast A B} 
  : Cast (CarGeometry A) (CarGeometry B) :=
fun a =>  Build_CarGeometry
            ('carDim a)
            ('minTR a).

Open Scope Z_scope.
(**dimensions are in inches. always rounding up for safety. *)
Definition Mazda3Sedan2014sGT_Dim : CarDimensions Z := {|
  width := 28; (* actually, half of the width of the car. originally measured as 70cm *)
  lengthBack := 32; (* originally measured as 80cm. *)
  lengthFront := 140; (* 60+60+20 *)
|}.

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

Close Scope Z_scope.
