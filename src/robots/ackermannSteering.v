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
*)


Record AckermannCar (length : Q) (width :Q) : Type := {
(** position of the midpoint of the 2 rear wheels *)

  position :> Cart2D (Time -c-> R);

(** orientation of line joining the left (driver side) rear wheel to the right rear wheel *)

  theta : (Time -c-> R);

(** instantaneous linear veloccity of the midpoint of the 2 rear wheels *)
  linVel : (Time -c-> R);


(** distance of the turning center from the midpoint of the 2 rear wheels *)
  turnCenterDist : (Time -c-> R);

(** especially needed to make the devision below in [derivRot]  well-typed *)
  turnCenterDistPos : forall t:Time, 0 [<] ({turnCenterDist} t);
  
(** differential equations *)

  derivX : isDerivativeOf (linVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (linVel * (FSin theta)) (Y position);

(** w = v/r *)
  derivRot : isDerivativeOf (linVel (*/turnCenterDist *)) theta

}.

