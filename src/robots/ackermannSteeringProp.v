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
Require Export ackermannSteering.


Require Export CartIR.


(** 
* Characterizing the motion under Ackermann steering.

This file is highly experimental.
*)

Section Props.
Variable maxTurnCurvature : Qpos.
Variable acs : AckermannCar maxTurnCurvature.


(** 
We characterize the motion of a car at a particular fixed speed, and
at a particular fixed turn curvature.
Ideally, we should let both of them vary a bit (upto some epsilon) during the process.
*)


Section FixedSpeedFixedCurv.
  Variable tstart : QTime.
  Variable tend : QTime.

  Variable lv : IR.
  Variable tc : IR.

  Hypothesis fixed : forall (t :QTime), {linVel acs} t = lv /\ {turnCurvature acs} t = tc.
  

End FixedSpeedFixedCurv.

End Props.