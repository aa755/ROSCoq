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
      am_driveControls :  steeringAlmostFixed acs am_tdrive tend (am_tc am) tcErr;

      am_driveDistance : 
        let driveIb := (@mkIntBnd _ tstart tend (timeLtWeaken p)) in 
           AbsSmall distErr ((am_distance am) - (∫ driveIb (linVel acs)))
    }.



  Hypothesis pr : tstart < tend.
  
  (** Now, we assume that the car executes the atomic move [am] from [tstart] to [tend],
    and characterize the position and orientation at [tend], in terms of their values at [tstart]. *)
  Hypothesis amc : CarExecutesAtomicMoveDuring pr.
  
  Local Notation tc := (am_tc am).
  Local Notation distance := (am_distance am).
  Local Notation tdrive := (am_tdrive amc).
  
  Lemma am_timeIncWeaken : (tstart ≤ tdrive ≤ tend).
  Proof using Type.
    pose proof (am_timeInc amc).
    split; apply timeLtWeaken; tauto.
  Qed.

  Local Notation timeInc := am_timeIncWeaken.
  Ltac timeReasoning :=
    autounfold with IRMC; unfold Le_instance_Time;
      destruct timeInc; eauto 2 with CoRN; fail.

  Lemma am_timeStartEnd : (tstart  ≤ tend).
  Proof using All.
    pose proof (am_timeIncWeaken).
    repnd.  timeReasoning.
  Qed.

(*
   Lemma am_driveDistanceFull : 
      let driveIb := (@mkIntBnd _ tstart tend am_timeStartEnd) in 
          (am_distance am) = ∫ driveIb (linVel acs).
   Proof using Type.
    simpl.
    pose proof (am_steeringControls amc) as steeringControls.
    rewrite <- CintegralSplitTrivialL with (m:=tdrive) (pr:= proj2 am_timeIncWeaken);
    [ | apply am_timeIncWeaken | ].
    Focus 2.
      intros x Hb. simpl. destruct Hb as [Hbl Hbr].
      simpl in Hbl, Hbr. apply steeringControls.
      split; timeReasoning; fail.
    rewrite (am_driveDistance).
    apply Cintegral_wd;[| reflexivity].
    simpl. split;
    reflexivity.
  Qed.
*)


  Local Notation θs := ({theta acs} tstart).
  Local Notation Xs := ({X (position acs)} tstart).
  Local Notation Ys := ({Y (position acs)} tstart).
  Local Notation Ps := (posAtTime acs tstart).


  Lemma rigidStateNoChange : forall t:Time, 
    tstart ≤ t ≤ tdrive
    -> (rigidStateAtTime acs t) = (rigidStateAtTime acs tstart).
  Proof using Type.
    apply LV0. destruct amc.
    simpl in *.
    tauto.
  Qed.

  Hypothesis nsc : noSignChangeDuring (linVel acs) tstart tend.
  (** 2 cases, based on whether the steering wheel is perfectly straight before driving.
    To avoid a  divide-by-0, the integration has to be done differently in these cases. *)
  Section TCNZ.
  Hypothesis (tcNZ : amTurn am).
    Let turnRadius  :IR  := (f_rcpcl tc tcNZ).

  Let adist := (|am_distance am|) + (|distErr|).


Require Import MathClasses.interfaces.functors.

(* finish and move *)
Global Instance proper_pnorm:
  Proper (equiv ==> equiv) (@pNorm IR _).
Proof.
  unfold pNorm.
  eapply sfmap_proper.
  intros ? ? H. setoid_rewrite H. reflexivity.
Print SFunctor.
Admitted.

  Lemma turnErrMono e d1 d2 r: 
  (|d1|) ≤ (|d2|)
  -> turnErr e d1 r ≤ turnErr e d2 r.
  Proof.
    intro H1.
    split; [split|]; simpl;
    try rewrite (MultShuffle3r _ d1);
    try rewrite (MultShuffle3r _ d2);
    setoid_rewrite AbsIR_resp_mult; apply mult_resp_leEq_lft; 
    eauto using AbsIR_nonneg.
  Qed.


  Lemma AtomicMoveTurn :
  let rs:= rigidStateAtTime acs in
    pNorm (rs tend - 
            (turnRigidStateAtθ (rs tstart) turnRadius ({theta acs} tend)))
    ≤ turnErr tcErr adist turnRadius.
  Proof using pr nsc amc.
    simpl.
    setoid_rewrite <- (rigidStateNoChange tdrive);
      [ | split; eauto with relations; apply am_timeIncWeaken].
    eapply transitivity;
     [apply fixedSteeeringTurn with (tcErr0:=tcErr) (timeInc := proj2 am_timeIncWeaken);
      apply am_driveControls |].
    apply turnErrMono.
    eapply noSignChangeDuringWeaken with (a2:=tdrive) (b2:=tend)in nsc; auto;
    [| eauto with relations; apply am_timeIncWeaken].
    rewrite noChangeAbs by assumption.
    unfold norm, NormSpace_instance_IR.
    rewrite AbsIR_eq_x by apply AbsIR_nonneg.
    pose proof (am_driveDistance amc) as amd. simpl in amd.
    apply AbsSmall_imp_AbsIR in amd.
    subst adist.    
    setoid_rewrite AbsIR_eq_x at 2;[| apply plus_resp_nonneg; apply AbsIR_nonneg].
    rewrite plus_comm.
    apply shift_leEq_plus.
    setoid_rewrite AbsIR_minus in amd.
    eapply transitivity; [| apply leEq_AbsIR].
    rewrite <- CintegralSplitTrivialL with (m:=tdrive) (pr:= proj2 am_timeIncWeaken) in amd;
    [ | apply am_timeIncWeaken | apply am_steeringControls].
    eapply transitivity; [| apply amd].
    apply triangle_IR_minus'.
  Qed.

  End TCNZ.

End AtomicMoveExec.
