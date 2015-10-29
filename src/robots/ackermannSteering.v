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

(** because of the limited range of the steering wheel, 
turn radius cannot be made arbitrary small. This is the bound*)

Variable minTurnRadius : Qpos.


Record AckermannCar  : Type := {
(** position of the midpoint of the 2 rear wheels *)

  position :> Cart2D (Time -c-> R);

(** orientation of line joining the left (driver side) rear wheel to the right rear wheel *)

  theta : (Time -c-> R);

(** instantaneous linear veloccity of the midpoint of the 2 rear wheels *)

  linVel : (Time -c-> R);


(** position of the turning center.
We know that it lies on the line joining the 2 rear wheels.
This value (at time [t]) is the displacement from the midpoint from the 2 wheels, along that line.
A positive value indicates that the turn center is on the right side*)

(*
This turn radius is a poorly behaved function. When one moves the
steering wheel from a little left of the midpoint to a little right, the
turn radious goes from a very large negative value, undefined, 
to a very large positive value.

It's reciprocal, which is "curvature", seems to be much better.
During the above process,
It goes continuously from a small negative value to 0 to a small negative value.
*)
  turnCenter : (Time -c-> R);

(** apart from capturing a physical constraint, it is implies
the non-zerohood of [turnCenter] at all times, which is needed for
the division below in [derivRot] to be well-typed.
*)

  turnCenterNonZero : forall t:Time, (Q2R minTurnRadius) ≤ |{turnCenter} t|;
  
(** differential equations *)

  derivX : isDerivativeOf (linVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (linVel * (FSin theta)) (Y position);

(** w = v/r *)
  derivRot : isDerivativeOf (linVel (*/turnCenterDist *)) theta

}.

End Robot.