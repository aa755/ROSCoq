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


(**
* #<a href="https://en.wikipedia.org/wiki/Ackermann_steering_geometry">Ackermann Steering</a>#
*)


Record AckermannCar (length : Q) (width :Q) : Type := {
(** position of the midpoint of the 2 rear wheels *)

  position :> Cart2D TContR;

(** orientation of line joining the left (driver side) rear wheel to the right rear wheel *)

  theta : TContR;

(** instantaneous linear veloccity of the midpoint of the 2 rear wheels *)
  linVel : TContR;


(** distance of the turning center from the midpoint of the 2 rear wheels *)
  turnCenterDist : TContR

}.

