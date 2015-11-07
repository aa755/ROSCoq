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

(** [TContR] is a type of continuous functions from [Time] to reals ([R])
It denotes how a physical quantity evolved over time *)

Local Notation "Time -c-> R" := TContR (at level 100).


(**
* #<a href="https://en.wikipedia.org/wiki/Ackermann_steering_geometry">Ackermann Steering</a>#

This file is highly experimental.
*)

Section Robot.


(** length of the car *)

Variable length : Q.

(** width of the car *)

Variable width :Q.


(** Because of the limited range of the steering wheel, 
turn radius cannot be made arbitrary small. 
Thus, the turn curvature, which is its inverse cannot be made arbitrary large*)

Variable maxTurnCurvature : Qpos.

Set Implicit Arguments.

Record AckermannCar  : Type := {

(** instantaneous linear veloccity of the midpoint of the 2 rear wheels *)

  linVel : (Time -c-> R);

(** We also need to model the 
position of the turning center.
We know that it lies on the line joining the 2 rear wheels.
One way to model it is to have a physical quantity denoting
the turn radius (at time [t]), 
which is the  displacement from the midpoint from the 2 wheels, along that line.
A positive value indicates that the turn center is on the right side. 

However, this turn radius is a poorly behaved function. When one moves the
steering wheel from a little left of the midpoint to a little right, the
turn radious goes discontinuously from a very large negative value, to undefined, 
to a very large positive value.

Note that the turn radious is always larger than a positive quantity,
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


(** Position of the midpoint of the 2 rear wheels *)

  position :> Cart2D (Time -c-> R);

(** orientation of line joining the left (driver side) rear wheel to the right rear wheel *)

  theta : (Time -c-> R);

  
(** differential equations *)

  derivX : isDerivativeOf (linVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (linVel * (FSin theta)) (Y position);

(** w = v/r. Recall that curvature = 1/r *)
  derivRot : isDerivativeOf (linVel * turnCurvature) theta

}.

End Robot.