Require Export Coq.Program.Tactics.
Require Export LibTactics.
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
Require Import CPS.
Require Import CPSUtils.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import CartCR.


Require Export CartIR.


Notation FConst := ConstTContR.
Notation FSin:= CFSine.
Notation FCos:= CFCos.

(** [TContR] is a type of continuous functions from [Time] to reals ([R]).
It denotes how a physical quantity evolved over time.
Recall that [Time] is a type of non-negative reals.
For a detailed example, see Sec. 2 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#.

Also, see the #<a href="https://github.com/aa755/ROSCoq/wiki">ROSCoq wiki</a> for 
a more complete example of how robots are specified in ROSCoq.

This file is experimental.
*)

Local Notation "Time -c-> R" := TContR (at level 100).


(**
* #<a href="https://en.wikipedia.org/wiki/Ackermann_steering_geometry">Ackermann Steering</a>#
The geometry of Ackermann steering is illustrated in the figure below:


#<img src="ackermannSteering.svg"/>#

The key idea is that while turning, the rotation axes of all 4 wheels
meet at a point, which is denoted by turnCenter in the figure.
This point must lie on the line joining the rear wheels, because
they are fixed relative to the car. 
While turning, the whole car rotates around this point.
Note that while turning
the front wheels are NOT parallel to each other.
*)

Section Robot.


(** Because of the limited range of the steering wheel, 
turn radius cannot be made arbitrary small. 
Thus, the turn curvature, which is its inverse,
 cannot be made arbitrary large*)

Variable maxTurnCurvature : Qpos.

Set Implicit Arguments.

Record AckermannCar  : Type := {

(** instantaneous linear velocity of the midpoint of the 2 rear wheels *)

  linVel : (Time -c-> R);

(** We also need to model the 
position of the turning center.
As mentined and illustrated in the figure above, 
we know that it lies on the line joining the 2 rear wheels.
One way to model it is to have a physical quantity denoting
the turn radius (at time [t]), 
which is the  displacement from the midpoint from the 2 wheels, along that line, as shown in the figure above.
A positive value indicates that the turn center is on the left side of the car. 

However, this turn radius is a poorly behaved function. When one moves the
steering wheel from a little left of the midpoint to a little right, the
turn radious goes discontinuously from a very large negative value, to undefined, 
to a very large positive value.

Note that the turn radius is always larger than a positive quantity,
because of physical constraints.
Hence, we can model its (multiplicative) inverse, which can be understood as "curvature".
Curvature is much more well-behaved.
During the above process,
it goes continuously from a small negative value to 0 to a small positive value.
*)

  turnCurvature : (Time -c-> R);



(** 
The above two physical quantities are the only controllable ones for the car.
[linVel] is controlled via the gears, gas pedal and the brake pedal.
[turnCurvature] is coltrolled via the steering wheel. *)

  turnCurvatureUB : forall t:Time, |{turnCurvature} t| ≤ (Q2R maxTurnCurvature);


(** Position of the midpoint of the 2 rear wheels, as shown the figure above *)

  position :> Cart2D (Time -c-> R);

(** The angle (w.r.t X axis) made by the
  the line fron the  the midpoint of the back of the car
  to the midpoint of the front of the car   *)
  theta : (Time -c-> R);

  
(** differential equations *)

  derivX : isDerivativeOf (linVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (linVel * (FSin theta)) (Y position);

(** w = v/r. Recall that curvature = 1/r, where r is the turn radius. *)
  derivRot : isDerivativeOf (linVel * turnCurvature) theta

}.

Record CarDimensions (A:Type):=
{
(** length of the car w.r.t. the line joining the rear wheels *)
   lengthFront : A;
   lengthBack : A;
   
   (** width of the car*)
   width :A
}.

Require Import geometry2D.

(** enough data to render a car in a picture, which will be a part of an animation*)
Record carState (A:Type) : Type :=
{
  csrigid2D : Rigid2DState A;  
  cs_tc :  A (*turn curvatire, determines the position of steering wheel*)
}.

Definition posAtTime (acs :AckermannCar) (t: Time): Cart2D IR :=
  {| X:= {X (position acs)} t ; Y := {Y (position acs)} t |}.

Definition rigidStateAtTime (acs :AckermannCar) (t: Time) : Rigid2DState IR :=
  {| pos2D := posAtTime acs t ; θ2D := {theta acs} t|}.


Section CornerPos.

(** R will be instantiated with both reals and continuous functions from
time to reals.*)
Context `{SinClass R} `{CosClass R} `{Ring R} `{RealNumberPi R} `{HalfNum R}.

Variable cs :Rigid2DState R.

Definition frontUnitVec : Cart2D R := unitVec (θ2D cs).
Definition rightSideUnitVec : Cart2D R := unitVec ((θ2D cs) - (½ * π)).

Variable cd :CarDimensions R.

Definition frontRight : Cart2D R := 
  (pos2D cs) 
    + frontUnitVec* '(lengthFront cd)
    + rightSideUnitVec * '(width cd).

Definition frontLeft : Cart2D R := 
  (pos2D cs) 
    + frontUnitVec* '(lengthFront cd)
    - rightSideUnitVec * '(width cd).

Definition backLeft : Cart2D R := 
  (pos2D cs) 
    - frontUnitVec* '(lengthBack cd)
    - rightSideUnitVec * '(width cd).

Definition backRight : Cart2D R := 
  (pos2D cs) 
    - frontUnitVec* '(lengthBack cd)
    + rightSideUnitVec * '(width cd).

Definition carOutline : list (Line2D R) := 
  {|lstart := frontRight ; lend := backRight|}
  ::(linesConsecutive [frontRight;frontLeft;backLeft;backRight]).

Context `{MaxClass R} `{MinClass R}.
Definition carMinMaxXY : BoundingRectangle R :=
  computeBoundingRect  [frontRight;frontLeft;backLeft;backRight].

End CornerPos.


End Robot.