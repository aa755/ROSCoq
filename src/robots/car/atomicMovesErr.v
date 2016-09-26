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
Require Export Coq.Program.Tactics.
Require Export LibTactics.
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
Require Import IRMisc.LegacyIRRing.
Require Import errorBounds.
Require Import MCMisc.rings.
Require Import atomicMoves.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.theory.setoids.
Set Implicit Arguments.

Set Suggest Proof Using.

    Ltac dimp H :=
    lapply H;[clear H; intro H|].



Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Local Notation minxy := (lstart).
Local Notation maxxy := (lend).
Local Notation  "∫" := Cintegral.



Section AtomicMoveExec.

  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).
  Variable am : AtomicMove IR.  
  Variable tstart : Time.
  Variable tend : Time.

(* check that there we dont redefine the concepts in atomicMoves.v *)

  Set Implicit Arguments.

  Section Error.
    Variable tcErr : IR.
    Variable distErr : IR.

  (** This defines what it means for the car's controls to 
    realistically follow the atomic move [am] during time [tstart] to [tend] *)
    Record CarExecutesAtomicMoveDuring (p: tstart < tend) : Type :=
    {
      am_tdrive : Time;
  
      (**strict inequalities prevents impossilities like covering non-zero distance in 0 time.
        Note that [linVel] and [turnCurvature] evolve continuously.
       *)
      am_timeInc : (tstart < am_tdrive < tend);

    (** From time [tsteer] to [drive], the steerring wheel rotates to attain a configuration 
      with turn curvature [tc]. The brakes are firmly placed pressed.*)
      am_steeringControls : forall (t:Time), (tstart ≤ t ≤ am_tdrive) 
            -> {linVel acs} t = 0;

    (** From time [tdrive] to [tend], the steering wheel is held NEARLY fixed*)
      am_driveControls :  steeringAlmostFixed acs tstart tend (am_tc am) tcErr;

      am_driveDistance : 
        let driveIb := (@mkIntBnd _ tstart tend (timeLtWeaken p)) in 
           AbsSmall distErr ((am_distance am) - (∫ driveIb (linVel acs)))
    }.


  End Error.
End AtomicMoveExec.
