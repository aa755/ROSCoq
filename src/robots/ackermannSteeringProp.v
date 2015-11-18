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

  Add Ring RisaRing: (CRing_Ring IR).

Require Export CartIR.

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

(** 
* Characterizing the motion under Ackermann steering.

This file is highly experimental.
*)
  
Section Props.
Variable maxTurnCurvature : Qpos.
Variable acs : AckermannCar maxTurnCurvature.

  Local Notation  "∫" := Cintegral.

(** 
We characterize the motion of a car at a particular fixed turn curvature.
The speed is not fixed, even though it seems like an enticing temporary simpilification.
The assumption that [linSpeed] is continuous makes it impossible to assume
that the car immediately achieves the desired velocity from a state of rest.
Fortunately, the lack of constanthood assumption of [linSpeed] 
does not complicate the integrals.


TODO: Ideally, we should let the turn curvature vary a bit 
(upto some epsilon) during the process.
This will SIGNIFICANTLY complicate the integrals.
*)


Section Cases.

  Variable tstart : Time.
  Variable tend : Time.

  Hypothesis tstartEnd : (tstart ≤ tend).

  Local Notation θ0 := ({theta acs} tstart).
  
  (** We will consider 2 classes of motions between [tstart] and [tend]. These classes suffice for our purpose

    -1) move with fixed steering wheel ([turnCurvature])
    -2) rotate the steering wheel while remaining stationary ([linVel = 0]).

  *)

  Section FixedSteeringWheel.
  Variable tc : IR.

(* TODO: It suffices to assume it for just rational times, because of continuity *)  
  Hypothesis fixed : forall (t :Time), 
    (tstart ≤ t ≤ tend)  -> {turnCurvature acs} t = tc.

  (** [theta] at time [t] is also needed obtain position at time [t] by integration *)
  Lemma fixedSteeringTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
(** ib denotes the pair of numbers that goes at the bottom and at the top of ∫ *)
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({theta acs} t - {theta acs} tstart) = tc* (∫ ib (linVel acs)).
  Proof.
    intros ? Hb ?.
    setoid_rewrite <- TBarrowScale;
      [| apply (derivRot acs)|];[reflexivity|].
    intros tb Hbb.  rewrite mult_comm.
    simpl. apply mult_wd;[| reflexivity].
    apply fixed. unfold intgBndL, intgBndR in Hbb.  simpl in Hbb.
    repnd. autounfold with IRMC. unfold Le_instance_Time.
    split; eauto 2 with CoRN.
  Qed.


  (** We consider the case when the front wheels are not straight, i.e. the 
      turn curvature is nonzero. The other case (front wheels are perfectly straight) is simpler, 
      but needs to be handled differently due to "divide by 0" issues during integration.*)

  Section TCNZ.
  (**Needed because [tc] shows up as a denominator
     during integration below in [fixedCurvX].*)
  Hypothesis tcNZ : (tc [#] 0).


  (** [X] coordinate of the [position] at a given time. Note that in CoRN,
      division is a ternary operator. [a[/]b[//][bp]] denotes the real number [a]
      divided by the non-zero real number [b], where [bp] is the proof of non-zero-hood
      of [b].
   *)
  Lemma fixedSteeeringX : forall (t :Time) (_: tstart ≤ t ≤ tend),
    ({X (position acs)} t - {X (position acs)} tstart) =  
        ((Sin ({theta acs} t) - Sin ({theta acs} tstart)) [/] tc [//] tcNZ).
  Proof.
    intros  ? Hb.
    setoid_rewrite <- TBarrow with (p:= proj1 Hb);[| apply (derivX acs)].
    pose proof (@TContRDerivativeSin _ _ _ _ (derivRot acs)) as X.
    apply mult_cancel_rht with (z:=tc);[exact tcNZ|].
    rewrite div_1.
    rewrite (@mult_commut_unfolded IR).
    rewrite <- CIntegral_scale.
    match type of X with
      isIDerivativeOf ?l _ => rewrite (@Cintegral_wd2 _ _ _ _ l)
    end.
    - rewrite TBarrow;[| apply X]. fold (CFSine (theta acs)).
      rewrite CFSineAp, CFSineAp. reflexivity.
    - intros tb Hbb.
      autounfold with IRMC in Hb.
      unfold Le_instance_Time in Hb. 
      autounfold with TContRMC.
      fold (CFCos (theta acs)).
      (* autorewrite with IContRApDown. *)
      rewrite IContRMultAp,IContRMultAp,IContRMultAp,IContRMultAp, CFCosAp,IContRConstAp.
      rewrite fixed with (t:=tb); [ring |].
      autounfold with IRMC.  unfold Le_instance_Time.
      unfold inBounds in Hbb. simpl in Hbb. repnd.
      split; eauto 2 with CoRN.
  Qed.

  Lemma tcnegNZ : - tc [#] 0.
  Proof. 
    apply inv_resp_ap_zero. exact tcNZ.
  Qed.

  Lemma fixedSteeeringY : forall (t :Time) (_: tstart ≤ t ≤ tend),
    ({Y (position acs)} t - {Y (position acs)} tstart) =  
        ((Cos ({theta acs} tstart) - Cos ({theta acs} t)) [/] tc [//] tcNZ).
  Proof.
    intros  ? Hb.
    setoid_rewrite <- TBarrow with (p:= proj1 Hb);[| apply (derivY acs)].
    pose proof (@IContRDerivativeCos _ _ _ _ (derivRot acs)) as X.
    apply mult_cancel_rht with (z:=-tc);[exact tcnegNZ|].
    autounfold with IRMC.
    symmetry. rewrite cring_inv_mult_lft. symmetry.
    rewrite div_1.
    rewrite (@mult_commut_unfolded IR).
    rewrite <- CIntegral_scale.
    match type of X with
      isIDerivativeOf ?l _ => rewrite (@Cintegral_wd2 _ _ _ _ l)
    end.
    - rewrite TBarrow;[| apply X]. fold (CFCos (theta acs)).
      rewrite CFCosAp, CFCosAp. unfold cg_minus.
      autounfold with IRMC.
      ring.
    - intros tb Hbb.
      autounfold with IRMC in Hb.
      unfold Le_instance_Time in Hb. 
      autounfold with TContRMC.
      rewrite IContRMultAp,IContRMultAp,IContRMultAp,IContRMultAp, CFSineAp,IContRConstAp.
      rewrite composeIContAp.
      simpl. symmetry.
      pose proof (@pfwdef2 _ Sine ({theta acs} tb) (fst Continuous_Sin ({theta acs} tb) I) I) as Hr. 
      rewrite Hr.
      Local Transparent Sin.
      unfold Sin. simpl.
      Local Opaque Sin.
      rewrite fixed with (t:=tb); [ring |].
      autounfold with IRMC.  unfold Le_instance_Time.
      unfold inBounds in Hbb. simpl in Hbb. repnd.
      split; eauto 2 with CoRN.
  Qed.

  End TCNZ.

(*
  Section TC0.
  (** now consider the case when the front wheels are exactly straight *)
  Hypothesis tcNZ : (tc = 0).

  Lemma fixedStraightSteeringTheta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
      {theta acs} t = {theta acs} tstart.
  Proof.
  Abort.


  Lemma fixedStraightSteeeringX : forall (t :Time) (p: tstart ≤ t ≤ tend),
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({X (position acs)} t - {X (position acs)} tstart) =  (∫ ib (linVel acs)) * Cos ({theta acs} tstart).
  Proof.
  Abort.

  Lemma fixedStraightSteeeringY : forall (t :Time) (p: tstart ≤ t ≤ tend),
    let ib := @mkIntBnd _ tstart t (proj1 p) in
    ({Y (position acs)} t - {Y (position acs)} tstart) =  (∫ ib (linVel acs)) * Cos ({theta acs} tstart).
  Proof.
  Abort.

  End TC0.
*)
  
  
  End FixedSteeringWheel.
  
  Section LinVel0.
  (** Now consider the second case where the steering wheel may move, but the car remains stationary *)
    Hypothesis lv0 :  forall (t :Time), 
      (tstart ≤ t ≤ tend)  -> {linVel acs} t = 0.

    Lemma LV0Theta : forall (t :Time)  (p: tstart ≤ t ≤ tend),
        {theta acs} t = {theta acs} tstart.
    Proof.
      intros. eapply TDerivativeEq0;[tauto | apply derivRot|].
      intros tt Hb. simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

 Local Opaque FCos.
    Lemma LV0X : forall (t :Time) (p: tstart ≤ t ≤ tend),
      {X (position acs)} t = {X (position acs)} tstart .
    Proof.
      intros. eapply TDerivativeEq0;[tauto | apply derivX|].
      intros tt Hb.
      simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.

    Lemma LV0Y : forall (t :Time) (p: tstart ≤ t ≤ tend),
      {Y (position acs)} t = {Y (position acs)} tstart .
    Proof.
      intros. eapply TDerivativeEq0;[tauto | apply derivY|].
      intros tt Hb.
      simpl. rewrite lv0;autounfold with IRMC; [ring|].
      repnd. split; eauto 2 with CoRN.
    Qed.


  End LinVel0.
  
(* TODO : given the car's dimensions, confine the whole car within 
  a "small, yet simple" region
  during the above motion. *)

End Cases.

Section AtomicMove.
(** * Atomic Move

We will build complex manueuvers out of the following basic move :
turn the steering wheel so that the turnCurvature has a particular value ([tc]),
and then drive for a particular distance ([distance]).
Note that both [tc] and [distance] are signed -- the turn center can be on the either side,
and one can drive both forward and backward *)
  Record AtomicMove := mkAtomicMove
  {
     am_distance : CR;
     am_tc : CR
  }.

  (** Needed because equality on reals (IR) is different 
      from syntactic equality 
      ([≡]). *)
      
  Global Instance Equiv_AtomicMove : Equiv AtomicMove :=
    fun (ml mr : AtomicMove) => (am_distance ml = am_distance mr) 
          /\ (am_tc ml = am_tc mr).

  (** To make tactics like [reflexivity] work, we needs to show
  that the above defined custom defined equality on [AtomicMove] 
  is an equivalence relation.*)
  Global Instance Equivalence_instance_AtomicMove 
    : @Equivalence (AtomicMove) equiv.
  unfold equiv, Equiv_AtomicMove. split.
  - intros x. destruct x. simpl. split; auto with *.
  - intros x y. destruct x,y. simpl. intros Hd; destruct Hd;
      split; auto with relations.

  - intros x y z. destruct x,y,z. simpl. intros H0 H1.
    repnd.
    split; eauto 10
    with relations.
  Qed.

  Variable am : AtomicMove.
  Definition amTurn := ('am_tc am) [#] (0:IR).
  Definition amNoTurn := ('am_tc am) = (0:IR).
  
  Variable tstart : Time.
  Variable tend : Time.
  

  Set Implicit Arguments.
  (** This defines what it means for the car's controls to follow the atomic move [am] during time [tstart] to [tend] *)
  Record CarExecutesAtomicMoveDuring (p: tstart < tend) : Type :=
  {
    am_tdrive : Time;

    (**strict inequalities prevents impossilities like covering non-zero distance in 0 time.
      Note that [linVel] and [turnCurvature] evolve continuously.
     *)
    am_timeInc : (tstart < am_tdrive < tend);
 
    am_steeringControls : ({turnCurvature acs} am_tdrive) = ('am_tc am) 
      /\ forall (t:Time), (tstart ≤ t ≤ am_tdrive) 
          -> {linVel acs} t = 0;

 
  (** From time [tdrive] to [tend], the steering wheel is held fixed*)
    am_driveControls : forall (t:Time), (am_tdrive ≤ t ≤ tend) 
          ->  {turnCurvature acs} t = {turnCurvature acs} am_tdrive;
          
  (** From time [tsteer] to [drive], the steerring wheel rotates to attain a configuration 
    with turn curvature [tc]. The brakes are firmly placed pressed.*)
   am_driveDistance : 
      let pf := (timeLtWeaken (proj2 (am_timeInc))) in 
      let driveIb := (@mkIntBnd _ am_tdrive tend pf) in 
          ('am_distance am) = ∫ driveIb (linVel acs)
  }.
  
  Hypothesis pr : tstart < tend.
  
  (** Now, we assume that the car executes the atomic move [am] from [tstart] to [tend],
    and characterize the position and orientation at [tend], in terms of their values at [tstart]. *)
  Hypothesis amc : CarExecutesAtomicMoveDuring pr.
  
  Local Notation tc := (am_tc am).
  Local Notation distance := (am_distance am).
  Local Notation tdrive := (am_tdrive amc).
  
  Lemma am_timeIncWeaken : (tstart ≤ tdrive ≤ tend).
    pose proof (am_timeInc amc).
    split; apply timeLtWeaken; tauto.
  Qed.

  Local Notation timeInc := am_timeIncWeaken.
  Ltac timeReasoning :=
    autounfold with IRMC; unfold Le_instance_Time;
      destruct timeInc; eauto 2 with CoRN; fail.

  Lemma am_timeStartEnd : (tstart  ≤ tend).
    pose proof (am_timeIncWeaken).
    repnd.  timeReasoning.
  Qed.

(** we only assumed this displacement from [tdrive] to [tend].
But because the derivative is [0] from [tstart] to [tdrive], 
there is no displacement during that time. *)
   Lemma am_driveDistanceFull : 
      let driveIb := (@mkIntBnd _ tstart tend am_timeStartEnd) in 
          ('am_distance am) = ∫ driveIb (linVel acs).
   Proof.
    simpl. 
    rewrite CintegralSplit
      with (pl:= proj1 am_timeIncWeaken)
           (pr:= proj2 am_timeIncWeaken).
    pose proof (am_steeringControls amc) as steeringControls.
    apply proj2 in steeringControls.
    rewrite (@Cintegral_wd2  _ _ _ _ [0]).
    Focus 2.
      intros x Hb. simpl. destruct Hb as [Hbl Hbr].
      simpl in Hbl, Hbr. apply steeringControls.
      split; timeReasoning.
    rewrite CintegralZero.
    autounfold with IRMC.
    ring_simplify.
    rewrite (am_driveDistance).
    apply Cintegral_wd;[| reflexivity].
    simpl. split;
    reflexivity.
  Qed.

  Local Notation θs := ({theta acs} tstart).
  Local Notation Xs := ({X (position acs)} tstart).
  Local Notation Ys := ({Y (position acs)} tstart).
  Local Notation Ps := (posAtTime acs tstart).

  Lemma AtomicMoveθ : {theta acs} tend =  θs + 'tc * 'distance.
  Proof.
    pose proof (am_driveControls amc) as driveControls.
    eapply  fixedSteeringTheta with (t:= tend) in driveControls.
    Unshelve. Focus 2. timeReasoning.
    simpl in driveControls.
    rewrite Cintegral_wd in driveControls;[| | reflexivity].
    Focus 2. instantiate (1 := let pf := (timeLtWeaken (proj2 (am_timeInc amc))) in 
                (@mkIntBnd _ tdrive tend pf)).
     simpl. split; reflexivity; fail.
    pose proof (am_steeringControls amc) as steeringControls.
    rewrite (proj1 steeringControls) in driveControls.
    rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControls;[| apply (proj2 steeringControls) 
        | timeReasoning ].
    rewrite <- (am_driveDistance amc) in driveControls.
    rewrite <- driveControls. simpl.
    autounfold with IRMC. simpl. ring. 
  Qed.

  (** 2 cases, based on whether the steering wheel is perfectly straight before driving.
    To avoid a  divide-by-0, the integration has to be done differently in these cases. *)
  Section TCNZ.
  Hypothesis (tcNZ : amTurn).
  
    Lemma AtomicMoveXT : {X (position acs)} tend =  Xs +
          ((Sin ({theta acs} tend) - Sin θs) [/] 'tc [//] tcNZ).
    Proof.
      pose proof (am_driveControls amc) as driveControlsb.
      pose proof (am_steeringControls amc) as steeringControls.
      setoid_rewrite (proj1 steeringControls) in driveControlsb.
      eapply  fixedSteeeringX with (t:= tend) (tcNZ:=tcNZ) in driveControlsb.
      Unshelve. Focus 2. timeReasoning.
      unfold cf_div in driveControlsb.
      rewrite (fun p => LV0X tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      setoid_rewrite <- driveControlsb. simpl. autounfold with IRMC. simpl. ring.
    Qed.

    Lemma AtomicMoveX : {X (position acs)} tend =  Xs +
          ((Sin (θs + 'tc * 'distance) - Sin θs) [/] 'tc [//] tcNZ).
    Proof.
      unfold cf_div. rewrite <- AtomicMoveθ.
      exact AtomicMoveXT.
    Qed.

    Lemma AtomicMoveYT : {Y (position acs)} tend =  Ys +
          ((Cos θs - Cos ({theta acs} tend)) [/] 'tc [//] tcNZ).
    Proof.
      pose proof (am_driveControls amc) as driveControlsb.
      pose proof (am_steeringControls amc) as steeringControls.
      setoid_rewrite (proj1 steeringControls) in driveControlsb.
      eapply  fixedSteeeringY with (t:= tend) (tcNZ:=tcNZ) in driveControlsb.
      Unshelve. Focus 2. timeReasoning.
      unfold cf_div in driveControlsb.
      rewrite (fun p => LV0Y tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      rewrite (fun p => LV0Theta tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      setoid_rewrite <- driveControlsb. simpl. autounfold with IRMC. simpl. ring.
    Qed.


    Lemma AtomicMoveY : {Y (position acs)} tend =  Ys +
          ((Cos θs - Cos (θs + 'tc * 'distance)) [/] 'tc [//] tcNZ).
    Proof.
      unfold cf_div. rewrite <- AtomicMoveθ.
      exact AtomicMoveYT.
    Qed.

  End TCNZ.
              
  Section TCZ.
  Hypothesis (tcZ : amNoTurn).
  
    Lemma AtomicMoveZθ : forall t:Time, tstart ≤ t ≤ tend
    -> {theta acs} t =  θs.
    Proof.
      intros ? Hb. eapply TDerivativeEq0;[tauto | apply derivRot|].
      intros tt Hbb.
      apply not_ap_imp_eq.
      pose proof (leEq_or_leEq _ tt tdrive) as Hd.
      intro Hc.
      apply Hd.
      clear Hd. intro Hd.
      apply ap_tight in Hc;[contradiction|]. clear H Hc.
      simpl.
      pose proof (am_steeringControls amc) as steeringControls.
      pose proof (am_driveControls amc) as driveControls.
      destruct Hd as [Hd | Hd].
      - rewrite (proj2 steeringControls);[  IRring | ]. 
        repnd. split; timeReasoning.
      - unfold amNoTurn in tcZ. rewrite (driveControls);
         [|repnd; split; timeReasoning].
         rewrite (proj1 steeringControls),tcZ.  
         IRring.
    Qed.

    Lemma AtomicMoveZX : {X (position acs)} tend =  Xs + 'distance * (Cos θs).
    Proof.
      apply leftShiftEqIR.
      rewrite mult_comm.
      rewrite  (am_driveDistanceFull).
      eapply TBarrowScale with (ib := (mkIntBnd am_timeStartEnd));
        [apply derivX | ].
      intros t Hb. unfold mkIntBnd, intgBndL, intgBndR in Hb. simpl in Hb.
      rewrite mult_comm at 1.
      autounfold with TContRMC.
      rewrite IContRMultAp.
      rewrite CFCosAp.
      apply mult_wd;[| reflexivity].
      apply Cos_wd.
      apply AtomicMoveZθ.  exact Hb.
   Qed.

    Lemma AtomicMoveZY : {Y (position acs)} tend =  Ys + 'distance * (Sin θs).
    Proof.
      apply leftShiftEqIR.
      rewrite mult_comm.
      rewrite  (am_driveDistanceFull).
      eapply TBarrowScale with (ib := (mkIntBnd am_timeStartEnd));
        [apply derivY | ].
      intros t Hb. unfold mkIntBnd, intgBndL, intgBndR in Hb. simpl in Hb.
      rewrite mult_comm at 1.
      autounfold with TContRMC.
      rewrite IContRMultAp.
      rewrite CFSineAp.
      apply mult_wd;[| reflexivity].
      apply Sin_wd.
      apply AtomicMoveZθ.  exact Hb.
   Qed.

  Global Instance castCRCart2DIR: Cast CR (Cart2D ℝ).
  intros x.
  apply sameXY. apply CRasIR. exact x.
  Defined.
  
   Lemma AtomicMoveFinal : {theta acs} tend =  θs /\
     posAtTime acs tend =
     Ps + ('distance) * (unitVec θs).
   Proof.
     split;[apply AtomicMoveZθ;split; timeReasoning|].
     split; simpl; [apply AtomicMoveZX | apply AtomicMoveZY].
   Qed.

  End TCZ.

End AtomicMove.

  Lemma CarExecutesAtomicMoveDuring_wd :
  forall ml mr tstartl tstartr tendl tendr 
      (pl :tstartl < tendl) (pr :tstartr < tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarExecutesAtomicMoveDuring ml pl
    -> ml = mr
    -> CarExecutesAtomicMoveDuring mr pr.
  Proof.
    intros ? ? ? ? ? ? ? ?  tl tr Hl Heq.
    destruct Hl.
    rewrite (proj2 Heq) in  am_steeringControls0.
    simpl in am_driveDistance0.
    setoid_rewrite tl in am_steeringControls0.
    setoid_rewrite tr in am_driveControls0 .
    setoid_rewrite (proj1 Heq) in am_driveDistance0.
   econstructor; eauto. simpl.
   rewrite am_driveDistance0.
   apply Cintegral_wd;[| reflexivity].
   simpl. rewrite tr.
   split; reflexivity.
   Unshelve.
   rewrite <- tl.
   rewrite <- tr. assumption.
  Qed.
  
  
    Lemma CarExecutesAtomicMoveDuring_wdtl :
  forall m tstartl tstartr tend 
      (pl :tstartl < tend) (pr :tstartr < tend),
    tstartl = tstartr
    -> CarExecutesAtomicMoveDuring m pl
    -> CarExecutesAtomicMoveDuring m pr.
  Proof.
  
    intros ? ? ? ? ? ? ? ?. eapply CarExecutesAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.

  Lemma CarExecutesAtomicMoveDuring_wdtr :
  forall m tstart tendl tendr 
      (pl :tstart < tendl) (pr :tstart < tendr),
    tendl = tendr
    -> CarExecutesAtomicMoveDuring m pl
    -> CarExecutesAtomicMoveDuring m pr.
  Proof.
    intros ? ? ? ? ? ? ? ?. eapply CarExecutesAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.

(** * Executing a sequence of atomic moves *)
  Definition AtomicMoves := list AtomicMove.
  
  
  (** This predicate defines what it means for a car to follow 
    a list of atomic moves from time [tstart] to [tend].*)
  Inductive CarExecutesAtomicMovesDuring : AtomicMoves -> forall (tstart tend : Time),  (tstart ≤ tend) -> Prop :=
  | amscNil : forall (tl tr:Time) (pe : tl = tr)(p: tl≤tr), 
        CarExecutesAtomicMovesDuring [] tl tr p
  | amscCons : forall (tstart tmid tend:Time) (pl : tstart < tmid) (pr : tmid ≤ tend) (p : tstart ≤ tend)
      (h: AtomicMove) (tl : AtomicMoves), 
      @CarExecutesAtomicMoveDuring h tstart tmid pl
      -> CarExecutesAtomicMovesDuring tl tmid tend pr
      -> CarExecutesAtomicMovesDuring (h::tl) tstart tend p.

Ltac substAtomicMoves amscrrl :=
    let pll := fresh "pll" in 
    let Hf := fresh "Hf" in 
    match type of amscrrl with
    ?l = _ => match goal with
        [  amscrl: @CarExecutesAtomicMoveDuring _ _ l ?pl0 |- _]
        =>
    pose proof pl0 as pll;
    rewrite amscrrl in pll;
    pose proof (@CarExecutesAtomicMoveDuring_wdtr _ _ _ _ 
      pl0 pll amscrrl amscrl) as Hf; clear dependent l
      end
      end.

Ltac invertAtomicMoves :=
  (repeat match goal with
    [ H: CarExecutesAtomicMovesDuring _ _ _ _ |- _] =>
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      let pl := fresh H "pl" in
      let pr := fresh H "pr" in
      (inverts H as Hl Hr pl pr;[]);
      try  substAtomicMoves Hl
  (* invert only if only 1 case results. o/w inf. loop will result if there are fvars*)
  end);
  repeat match goal with
    [ H: eq ?x ?x |- _] => clear H
    | [ H: le ?x ?x |- _] => clear H
  end.
  
  (*
  Lemma BetterInvertCarExecutesAtomicMovesDuringSingeton : 
    forall (m:AtomicMove) (tstart tend : Time)  (p:tstart ≤ tend),
    CarExecutesAtomicMovesDuring [m] tstart tend p
    ->  {pr : tstart < tend | CarExecutesAtomicMoveDuring m pr}.
  Proof.
    intros? ? ? ? Ha.
    inverts Ha.
  *)
    Lemma CarExecutesAtomicMovesDuring_wd :
    forall ml mr,
         ml = mr
 -> forall tstartl tstartr tendl tendr 
      (pl :tstartl ≤ tendl) (pr :tstartr ≤ tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarExecutesAtomicMovesDuring ml _ _ pl
    -> CarExecutesAtomicMovesDuring mr _ _ pr.
  Proof.
   intros ? ? meq.
   induction meq; intros ? ? ? ? ? ? ? ? Hl.
   - inverts Hl. constructor. rewrite <- H, pe. assumption.
   - inverts Hl as Hl1 Hl2.
    eapply IHmeq in Hl2; eauto; [| reflexivity].
     eapply CarExecutesAtomicMoveDuring_wd in Hl1; eauto; [| reflexivity].
    econstructor; eauto.
    Unshelve. Focus 2. rewrite <- H1. assumption.
    rewrite <- H0. assumption.
  Qed.
    
  Global Instance CarExecutesAtomicMovesDuring_ProperM (tstart tend : Time)  (p :tstart ≤ tend) :
    Proper (equiv ==> iff) (fun m => CarExecutesAtomicMovesDuring m tstart tend p).
  Proof.
    intros ? ? ?. split; apply CarExecutesAtomicMovesDuring_wd; 
    eauto 1 with relations.
  Qed.

  

Section Wriggle.
(** * The Wriggle move
Now consider a 
#<href="https://rigtriv.wordpress.com/2007/10/01/parallel-parking/">wiggle motion</a>#
and characterize the the change in car's position and orientation caused
by this motion. 
The word "wriggle" was perhaps coined by Nelson in his 1967 book Tensor analysis.
Informally it denotes the following motion : 

  -steer (i.e rotate the steering wheel with brakes firmly pushed), 
  -drive (while keeping the steering wheel fixed),
  -reverse steer,
  -reverse drive

  Wiggle is parametrized by a nonzero [turnCurvature] and a drive distance,
  both of which may be signed.
  *)
  Variable tc : CR.
  Hypothesis tcNZ : 'tc[#](0:IR).
  Variable distance : CR.
  

(** In our formalism, wriggle is a composition of the following 2 atomic moves.
  *)
  
  Definition steerAndDrive : AtomicMove
    := {|am_tc := tc; am_distance := distance |}.
  Definition revSteerAndrevDrive : AtomicMove
    := {|am_tc := -tc; am_distance := -distance |}.

(** the distance covered during driving and reverse driving is exactly the same.
  TODO: let them be slightly different, e.g. upto epsilon
 *)
  Definition Wriggle : AtomicMoves 
    :=  [steerAndDrive; revSteerAndrevDrive].
  
  Variable tstart : Time.
  Variable tend : Time.
  Hypothesis timeInc : tstart ≤ tend.
  
  (** Now, we assume that the car executes the [Wriggle] move from time [tstart] to [tend],
    and characterize the position and orientation at [tend], in terms of their values at [tstart]. 
     In this document When we say "move" in natural language, we mean [AtomicMoves].
    *)
  Hypothesis amsc : CarExecutesAtomicMovesDuring Wriggle tstart tend 
                      (timeInc).
  
  
  Local Notation θs := ({theta acs} tstart).
  Local Notation Xs := ({X (position acs)} tstart).
  Local Notation Ys := ({Y (position acs)} tstart).

  
  Hint Unfold One_instance_IR : IRMC.
      
      
  
  Lemma Wriggleθ : {theta acs} tend =  θs + 2 * 'tc * 'distance.
  Proof.
    invertAtomicMoves. rename Hf into amscrl.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl. rewrite amscl in amscrl.
    rewrite amscrl.
    autounfold with IRMC.
    autorewrite with CRtoIR. unfold cast,Cart_CR_IR.
     ring.    
  Qed.

  (** just to show that the car doesn't end up to the initial position after wriggle.
     This equation is not needed for anything else. 
  Lemma WriggleX : {X (position acs)} tend =  Xs +
        ((2* Sin (θs + 'tc * 'distance) 
            - Sin (θs + 2 * 'tc * 'distance)  - Sin θs) [/] 'tc [//] tcNZ).
  Proof.
    pose proof Wriggleθ as XX.
    invertAtomicMoves.
    rename amscl into Hl.
    rename Hf into Hrr.
    pose proof Hl as Hlt.
    apply AtomicMoveθ in Hlt.
    apply AtomicMoveX with (tcNZ:= tcNZ) in Hl.
    apply AtomicMoveXT with (tcNZ:= tcnegNZ _ tcNZ) in Hrr.
    Local Opaque Cos Sin.
    simpl in Hl, Hrr, Hlt.
    unfold cf_div in Hrr.
    rewrite XX in Hrr.
    rewrite Hrr. rewrite Hl.
    autounfold with IRMC. unfold cf_div.
    rewrite reciprocalNeg with (xp:=tcNZ).
    rewrite cring_inv_mult_lft.
    rewrite <- cring_inv_mult_rht.
    setoid_rewrite minusInvR.
    rewrite Hlt.
    autounfold with IRMC. unfold cg_minus. simpl.
     ring.
  Qed.
 *)
End Wriggle.

(*  Lemma Wriggleθ2  
  `{CarExecutesAtomicMovesDuring (Wriggle tc distance) tstart tend p} :
  {theta acs} tend =  {theta acs} tstart + 2 * tc * distance.
  Proof.
    
    invertAtomicMoves. rename Hf into amscrl.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl. rewrite amscl in amscrl.
    rewrite amscrl.
    autounfold with IRMC. ring.    
  Qed.
*)

Add Ring cart2dir : Cart2DIRRing.

Section Invertability.
(** * Invertability of moves 

It turns out that any Wriggle move is reversible (invertible).
Wriggle-inverse is a part of the sideways-move we will study next.
The sideways move comprises of 6 atomic moves and makes the car move sideways in little space.

To define Wriggle-inverse, we study invertability of moves in general,
and prove:
 -1) Every atomic move is inverible : keep the steering wheel at
the same position as before and then drive the same amount in 
the opposite direction.
 -2) The inverse of a list of atomic moves is the reverse of
the list of iverses of those atomic moves.


First we define what it means for a move to be an inverse of another.
*)

  Definition MovesIdentity (ams : AtomicMoves) :=
    ∀ (tstart tend : Time)  (p: tstart ≤ tend),
      CarExecutesAtomicMovesDuring ams tstart tend p
      -> (posAtTime acs tstart = posAtTime acs tend 
          /\ {theta acs} tstart = {theta acs} tend).

  (** [MovesIsInverse ams amsr] implies [MovesIdentity (ams ++ amsr)],
    but the other direction many not be true 
     This extra strength is useful because
    in the sideways move below, Wriggle-inverse does not immediately
    follow the Wriggle-move. *)
    
    
(*         TODO : quantify over [acs]. *)
  Definition MovesInverse (ams amsr : AtomicMoves) :=
    ∀ 
      (tstart tend : Time)  (p: tstart ≤ tend)
      (tstartr tendr : Time)  (pr: tstartr ≤ tendr),
      CarExecutesAtomicMovesDuring ams tstart tend p
      -> CarExecutesAtomicMovesDuring amsr tstartr tendr pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> (posAtTime acs tend - posAtTime acs tstart
          = posAtTime acs tstartr - posAtTime acs tendr
          /\ {theta acs} tstart = {theta acs} tendr).

  Definition CarExecutesAtomicMovesDuringAux  
      (tstart tend : Time)  (p: tstart ≤ tend) m
       := CarExecutesAtomicMovesDuring m tstart tend p .
  
   Lemma foldForProperAM : ∀ m 
      (tstart tend : Time)  (p: tstart ≤ tend),
      CarExecutesAtomicMovesDuring m tstart tend p ≡
      CarExecutesAtomicMovesDuringAux tstart tend p m.
   Proof. reflexivity. Qed.

  Global Instance CarExecutesAtomicMovesDuringAux_Proper (tstart tend : Time)  (p :tstart ≤ tend) :
    Proper (equiv ==> iff) (CarExecutesAtomicMovesDuringAux tstart tend p).
  Proof.
    apply CarExecutesAtomicMovesDuring_ProperM.
  Qed.

  Global Instance MovesInverseProper : Proper 
    (equiv ==> equiv ==> iff)  MovesInverse.
  Proof.
    intros ? ? ? ? ? ?. unfold MovesInverse.
    setoid_rewrite (foldForProperAM x).
    setoid_rewrite (foldForProperAM x0).
    setoid_rewrite  H.
    setoid_rewrite  H0.
    tauto.
  Qed.
      

        
  Definition AtomicMoveInv (m : AtomicMove) : AtomicMove
      := {|am_tc := am_tc m; am_distance := -(am_distance m) |}.

  Definition AtomicMovesInv (ms : AtomicMoves) : AtomicMoves
      := rev (List.map AtomicMoveInv ms).

  Lemma atomicMoveInvertibleθ :
    ∀ m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring m  p
      -> CarExecutesAtomicMoveDuring (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> ({theta acs} tstart = {theta acs} tendr).
  Proof.
    intros m ? ? ? ? ? ? amscl amscrl Ht.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl.
    rewrite amscrl, Ht, amscl.
    autorewrite with CRtoIR. unfold cast,Cart_CR_IR.
    IRring.
  Qed.

    
  (** The equations for X coordinate are different, based on whether the steering wheel is perfectly
      straight or not. The double negation trick works while proving equality *)
  Lemma atomicMoveInvertibleX :
    ∀ m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring m  p
      -> CarExecutesAtomicMoveDuring (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> ({X (position acs)} tend - {X (position acs)} tstart 
              = {X (position acs)} tstartr - {X (position acs)} tendr).
  Proof.
    intros m ? ? ? ? ? ? amscl amscrl Hte.
    pose proof amscl as Htt.
    eapply atomicMoveInvertibleθ in Htt; eauto.
    apply not_ap_imp_eq.
    pose proof (decideEdDN ('am_tc m) [0]) as Hd.
    intro Hc.
    apply Hd.
    clear Hd. intro Hd.
    apply ap_tight in Hc;[contradiction|]. clear H Hc.
    pose proof amscl as Ht.
    apply AtomicMoveθ in Ht.
    destruct Hd as [Hd | Hd].
    - apply AtomicMoveZX with (pr := p) in amscl;
        [| exact Hd].
      apply AtomicMoveZX with (pr := pr) in amscrl;
        [| exact Hd].
      simpl in amscl, amscrl, Ht.
      rewrite Hd in Ht.
      autounfold with IRMC in Ht. ring_simplify in Ht.
      rewrite amscrl, Hte, amscl, Ht.
      autorewrite with CRtoIR. unfold cast,Cart_CR_IR.
      IRring.
    - apply AtomicMoveXT with (tcNZ:= Hd) in amscl.
      eapply AtomicMoveXT  in amscrl.
      Unshelve. Focus 2. apply Hd.
      simpl in amscl, amscrl.
      unfold cf_div in amscl.
      unfold cf_div in amscrl.
      rewrite amscrl, Hte, amscl, Htt. IRring.
    Qed.
  (** just replace X by Y in the proof above *)
  Lemma atomicMoveInvertibleY :
    ∀ m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring m  p
      -> CarExecutesAtomicMoveDuring (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> ({Y (position acs)} tend - {Y (position acs)} tstart 
              = {Y (position acs)} tstartr - {Y (position acs)} tendr).
  Proof.
    intros m ? ? ? ? ? ? amscl amscrl Hte.
    pose proof amscl as Htt.
    eapply atomicMoveInvertibleθ in Htt; eauto.
    apply not_ap_imp_eq.
    pose proof (decideEdDN ('am_tc m) [0]) as Hd.
    intro Hc.
    apply Hd.
    clear Hd. intro Hd.
    apply ap_tight in Hc;[contradiction|]. clear H Hc.
    pose proof amscl as Ht.
    apply AtomicMoveθ in Ht.
    destruct Hd as [Hd | Hd].
    - apply AtomicMoveZY with (pr := p) in amscl;
        [| exact Hd].
      apply AtomicMoveZY with (pr := pr) in amscrl;
        [| exact Hd].
      simpl in amscl, amscrl, Ht.
      rewrite Hd in Ht.
      autounfold with IRMC in Ht. ring_simplify in Ht.
      rewrite amscrl, Hte, amscl, Ht.
      autorewrite with CRtoIR. unfold cast,Cart_CR_IR.
      IRring.
    - apply AtomicMoveYT with (tcNZ:= Hd) in amscl.
      eapply AtomicMoveYT  in amscrl.
      Unshelve. Focus 2. apply Hd.
      simpl in amscl, amscrl.
      unfold cf_div in amscl.
      unfold cf_div in amscrl.
      rewrite amscrl, Hte, amscl, Htt. IRring.
    Qed.

  Lemma atomicMoveInvertible :
    ∀ (m : AtomicMove), MovesInverse [m] [AtomicMoveInv m].
  Proof.
    intros m ? ? ? ? ? ? ?.
    invertAtomicMoves.
    intros ? ?.    
    invertAtomicMoves.
    split; [split |].
    - eapply atomicMoveInvertibleX; eauto.
    - eapply atomicMoveInvertibleY; eauto.
    - eapply atomicMoveInvertibleθ in Hf0; eauto.
  Qed.

  Lemma MoveInvInvolutive : ∀ (m : AtomicMove), 
    AtomicMoveInv (AtomicMoveInv m) = m.
  Proof.
    intros m.
    destruct m. unfold AtomicMoveInv, equiv, Equiv_AtomicMove. simpl.
    split; [| reflexivity]. apply negate_involutive.
  Qed.

  Lemma movesControlsApp : ∀ (l r : AtomicMoves) (tstart tend: Time)
    (pr : tstart ≤ tend),
    CarExecutesAtomicMovesDuring (l++r) _ _ pr
    -> exists (tmid : Time), exists (p : tstart ≤ tmid ≤ tend),
         CarExecutesAtomicMovesDuring l tstart tmid (proj1 p)
        /\ CarExecutesAtomicMovesDuring r tmid tend (proj2 p).
  Proof.
    induction l; intros.
    - exists tstart. eexists. split; auto;[constructor; reflexivity| ].
      simpl in H.
      Unshelve. Focus 2. split;[apply leEq_reflexive | exact pr].
      eapply CarExecutesAtomicMovesDuring_wd; eauto; reflexivity.
    - simpl in H.
      invertAtomicMoves.
      eapply IHl in Hr; eauto.
      destruct Hr as [tmmid  Hr]. 
      destruct Hr as [pm Hr].
      repnd.
      exists tmmid. eexists.
      split; eauto.
      Focus 2.
        eapply CarExecutesAtomicMovesDuring_wd; eauto; reflexivity.
      econstructor; eauto.
      Unshelve.
      split; eauto 2 with CoRN.
      autounfold with IRMC. unfold Le_instance_Time.
       clear Hl.
      apply timeLtWeaken in pl.
      eauto 3 with CoRN.
  Qed.
  
  Lemma atomicMoveInvertibleRev :
    ∀ (m : AtomicMove), MovesInverse  [AtomicMoveInv m] [m].
  Proof.
    intros m. remember [AtomicMoveInv m].
    setoid_rewrite <- MoveInvInvolutive.
    subst.
    apply atomicMoveInvertible.
  Qed.
    
    
  
  Lemma MovesControlsSingle : ∀ (m : AtomicMove) (tstart tend: Time)
    (pr : tstart < tend),
    @CarExecutesAtomicMoveDuring m tstart tend pr
    -> CarExecutesAtomicMovesDuring [m] tstart tend (timeLtWeaken pr).
  Proof.
    intros. econstructor; eauto. econstructor. reflexivity.
    Unshelve. apply leEq_reflexive.
  Qed.

   
   

  Lemma atomicMovesInvertibleAux :
    ∀ (m : AtomicMoves), MovesInverse (AtomicMovesInv m) m.
  Proof.
    induction m as [| h tl Hind]; intros ? ? ? ? ? ? Hm Hrm Ht;
      unfold AtomicMovesInv in Hrm; simpl in Hrm.
    - invertAtomicMoves. unfold posAtTime. rewrite <- Hml in Ht. 
      rewrite Hrml in Ht.
      rewrite Ht, Hml, Hrml. split;[split; simpl | reflexivity];
      repeat rewrite plus_negate_r; reflexivity.
    - invertAtomicMoves. rename tmid into tmidr.
      unfold AtomicMovesInv in Hm.
      rename Hm into Hl.
      simpl in Hl.
      apply movesControlsApp in Hl.
      destruct Hl as [tmid Hl].
      destruct Hl as [prr Hl].
      repnd.
      apply MovesControlsSingle in Hrml.
      eapply atomicMoveInvertibleRev in Hrml; eauto.
      specialize (Hrml Ht). repnd.
      eapply Hind in Hrmr; eauto.
      symmetry in Hrmlr.
      specialize (Hrmr Hrmlr). repnd. clear Hrmlr.
      split; [clear Hrmrr | exact Hrmrr].
      pose proof (@sg_op_proper _ _ plus  _ _ _ Hrmll _ _ Hrmrl) as Hadd.
      clear Hrmll  Hrmrl.
      unfold sg_op in Hadd.
      ring_simplify in Hadd.
      exact Hadd.
  Qed.
  
  Lemma MovesInvInvolutive : ∀ (m : AtomicMoves), 
    AtomicMovesInv (AtomicMovesInv m) = m.
  Proof.
    induction m;[reflexivity |].
    unfold AtomicMovesInv. simpl.
    rewrite map_app.
    rewrite map_cons.
    rewrite rev_app_distr.
    simpl.
    rewrite MoveInvInvolutive.
    constructor; auto.
  Qed.


  Lemma atomicMovesInvertible :
  ∀ (m : AtomicMoves), MovesInverse m (AtomicMovesInv m).
  Proof.
    intros m. remember (AtomicMovesInv m).
    setoid_rewrite <- (MovesInvInvolutive m).
    subst.
    apply atomicMovesInvertibleAux.
  Qed.
  
End Invertability.

(* TODO: Move *)
Lemma CRasIR1 : CRasIR 1 = [1].
Proof.
  pose proof IR_One_as_CR as HH.
  apply CRasIR_wd in HH.
  rewrite IRasCRasIR_id in HH.
  symmetry. exact HH.
Qed.


Section Sideways.

(** * The sideways move

Adding just one atomic move to the [SidewaysAux] move defined below
will get us to the sideways move. After [SidewaysAux],
as we will prove,
the car's orientation is same as that in the original state, but
it's position has shifted a bit, both along the car's orientaition and orthogonal to it.
[SidewaysAux] is just a straight-drive move inserted between
a wriggle and its inverse.
Note that without this insertion, we would have been back
to where we started.
*)
  Variable tc : CR.
  Hypothesis tcNZ : 'tc[#](0:IR).
  Variable wdistance : CR.
  Variable ddistance : CR.
  
  Local Notation SWriggle := (Wriggle tc wdistance).
  Local Notation SWriggleInv := (AtomicMovesInv SWriggle).
  
  (** Drive a distance of [ddistance]
    with front wheels perfectly straight.*)  
  Local Notation DriveStraight := {| am_distance := ddistance ; am_tc := 0|}.

  Definition SidewaysAux : AtomicMoves 
    := SWriggle ++ [DriveStraight] ++ SWriggleInv.

  
  (** The car's orientation at the end is same as that at the start.
     [θAtW] denotes the car's orientation at the completion of the [SWriggle] move. 
     For any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
     *)
  Lemma SidewaysAuxState : forall  (tstart tend : Time) (timeInc : tstart ≤ tend),
  (CarExecutesAtomicMovesDuring SidewaysAux tstart tend timeInc)
  ->
  let θs := ({theta acs} tstart) in 
  let θAtW := θs + 2 * 'tc * 'wdistance  in
  {theta acs} tend =  θs /\
    posAtTime acs tend = (posAtTime acs tstart)
      + ('ddistance) * (unitVec θAtW).
  Proof.
    intros ? ? ? amsc.    
    unfold SidewaysAux in amsc.
    apply movesControlsApp in amsc.
    destruct amsc as [tds Hams]. (* ds for drive straight *)
    destruct Hams as [pds Hams].
    repnd. rename Hamsl into Hw. (* w for wiggle *)
    apply movesControlsApp in Hamsr.
    destruct Hamsr as [twr Hamsr]. (* ds for drive straight *)
    destruct Hamsr as [pwr Hams]. repnd.
    rename Hamsl into Hds.
    rename Hamsr into Hwr.
    pose proof Hw as Hwb. (* needed for θAtW *)
    eapply atomicMovesInvertible in Hw; eauto.
    specialize (Hw Hwr). clear Hwr.
    apply Wriggleθ in Hwb.
    invertAtomicMoves.
    apply AtomicMoveFinal in Hf;[|unfold amNoTurn;  simpl; 
        autorewrite with CRtoIR; reflexivity].
    simpl in Hf. repnd.
    specialize (Hw Hfl).
    repnd. symmetry in Hwr.
    split;[assumption|]. rewrite Hwb in Hfr.
    clear Hwb Hwr Hfl pll. rewrite Hfr in Hwl. clear Hfr.
    rewrite  <- (@plus_assoc (Cart2D IR)) in Hwl; [|eauto with typeclass_instances].
    apply (@left_cancellation ) in Hwl; [|apply groups.LeftCancellation_instance_0].
    apply (RingNegateProper ) in Hwl.
    rewrite negate_involutive in Hwl.
    rewrite Hwl.
    autorewrite with CRtoIR.
    simpl. ring.
  Qed.

  (** After [SidewaysAux], the car is in the same orientation as before, but it has position
    has changed. For a sideways move, we just have drive straight to cancel
    the component of that position change along the car's orientation.
    We get this component by taking the dot product of the position change with the unit vector
    along the car's orientation.
    Formally, a sideways move is one where the car's position shifts in a direction
    orthogonal to its orientation.
    *)
  Local Notation DriveStraightRev 
    := {| am_distance := - ddistance * cos (2 * tc * wdistance) ; am_tc := 0|}.

  Definition SidewaysMove : AtomicMoves 
    := SidewaysAux ++ [DriveStraightRev].
    
  (** The car's final orientation is same as before, and 
  its position changes in the direction that is at a right angle [(½ * π)]
  to its orientation, i.e., it is a sideways move. 
  The distance moved is [ddistance * Sin  θw].

  As mentioned before, for any [v], [sameXY v] denotes [{|X:=v; Y:=v|}].
  *)
  
  Lemma SidewaysState : forall  (tstart tend : Time) (timeInc : tstart ≤ tend),
  (CarExecutesAtomicMovesDuring SidewaysMove tstart tend timeInc)
  ->
  let θs := ({theta acs} tstart) in 
  let θw := 2 * tc * wdistance  in
    {theta acs} tend =  θs /\
    posAtTime acs tend = (posAtTime acs tstart) 
      + ('(ddistance * sin  θw)) * unitVec (θs + (½ * π)).
  Proof.
    intros ? ? ? amsc.
    unfold SidewaysMove in amsc. simpl.
    apply movesControlsApp in amsc.
    destruct amsc as [tds Hams]. (* ds for drive straight *)
    destruct Hams as [pds Hams]. repnd.
    apply SidewaysAuxState in Hamsl.
    invertAtomicMoves.
    apply AtomicMoveFinal in Hf;[|unfold amNoTurn;   simpl; 
        autorewrite with CRtoIR; reflexivity].
    simpl in Hf. repnd.
    rewrite Hamsll in Hfl.
    rewrite Hamsll in Hfr.
    split;[assumption|]. clear Hamsll Hfl.
    rewrite Hamslr in Hfr. clear Hamslr pll pdsl pdsr.
    remember (2 * tc * wdistance) as θw.
    clear Heqθw. unfold cast, castCRCart2DIR, Cart_CR_IR  in Hfr.
    rewrite CR_mult_asIR in Hfr.
    setoid_rewrite <- sameXYMult in Hfr.
    rewrite CRasIR_inv in Hfr.
    setoid_rewrite sameXYNegate in Hfr.
    Typeclasses eauto := 100. simpl in Hfr.
    rewrite  <- (@mult_assoc (Cart2D IR) _ _ _ _ _ _) in Hfr. 
    rewrite <- negate_mult_distr_l in Hfr.
    rewrite negate_mult_distr_r in Hfr.
    rewrite  <- (@plus_assoc (Cart2D IR) _ _ _ _ _ _) in Hfr. 
    rewrite  <- (@plus_mult_distr_l (Cart2D IR) _ _ _ _ _ _ _ _) in Hfr.
    autorewrite with CRtoIR in Hfr.
    rewrite CRasIR1 in Hfr.
    rewrite unitVecLemma1 in Hfr. unfold cast, castCRCart2DIR.
    autorewrite with CRtoIR.
    rewrite CRasIR1.
    setoid_rewrite <- sameXYMult.
    rewrite  <- (@mult_assoc (Cart2D IR)); [|eauto with typeclass_instances].
    rewrite PiBy2DesugarIR.
    exact Hfr.
  Qed.

End Sideways.

End Props.