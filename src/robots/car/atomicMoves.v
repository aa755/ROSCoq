Set Suggest Proof Using.
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

    Ltac dimp H :=
    lapply H;[clear H; intro H|].

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
  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Local Notation minxy := (lstart).
Local Notation maxxy := (lend).
Local Notation  "∫" := Cintegral.

Require Import MathClasses.interfaces.orders.

(*Move to MCInstances*)
Global Instance LeTimePreorder  : PreOrder Le_instance_Time .
Proof.
  split; intros ?; unfold le, Le_instance_Time; eauto 2 with CoRN.
Qed.

Global Instance LeTimePartialOrder  : PartialOrder Le_instance_Time.
Proof.
  split; eauto with typeclass_instances.
  intros ? ?; unfold le, Le_instance_Time, equiv; eauto 2 with CoRN.
  intros. destruct x, y. eapply leEq_imp_eq; eauto.
Qed.

(** * Atomic Move

We will build complex manueuvers out of the following basic move :
turn the steering wheel so that the turnCurvature has a particular value ([tc]),
and then drive for a particular distance ([distance]).
Note that both [tc] and [distance] are signed -- the turn center can be on the either side,
and one can drive both forward and backward *)
  Record AtomicMove := mkAtomicMove
  {
     am_distance : IR;
     am_tc : IR
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
 Proof using .
  unfold equiv, Equiv_AtomicMove. split.
  - intros x. destruct x. simpl. split; auto with *.
  - intros x y. destruct x,y. simpl. intros Hd; destruct Hd;
      split; auto with relations.

  - intros x y z. destruct x,y,z. simpl. intros H0 H1.
    repnd.
    split; eauto 10
    with relations.
  Qed.

Global Instance ProperAMTC : 
Proper (equiv ==> equiv) am_tc.
Proof using.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Global Instance ProperAMDistance : 
Proper (equiv ==> equiv) am_distance.
Proof using.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Section AtomicMove.

  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).
  Variable am : AtomicMove.
  Definition amTurn := (am_tc am) [#] 0.
  Definition amNoTurn := (am_tc am) = 0.
  
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
 
    am_steeringControls : ({turnCurvature acs} am_tdrive) = (am_tc am) 
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
          (am_distance am) = ∫ driveIb (linVel acs)
  }.

  Definition CarMonotonicallyExecsAtomicMoveDuring (p: tstart < tend) : Type :=
    CarExecutesAtomicMoveDuring p
    and (noSignChangeDuring (linVel acs) tstart tend). 
  
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

   Lemma am_driveDistanceFull : 
      let driveIb := (@mkIntBnd _ tstart tend am_timeStartEnd) in 
          (am_distance am) = ∫ driveIb (linVel acs).
   Proof using Type.
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


  Lemma AtomicMoveθ : {theta acs} tend =  θs + tc * distance.
  Proof using All.
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
    rewrite (fun p => LV0Theta acs tstart tdrive p tdrive) in driveControls;[| apply (proj2 steeringControls) 
        | timeReasoning ].
    rewrite <- (am_driveDistance amc) in driveControls.
    rewrite <- driveControls. simpl.
    autounfold with IRMC. simpl. ring. 
  Qed.

  Lemma rigidStateNoChange : forall t:Time, 
    tstart ≤ t ≤ tdrive
    -> (rigidStateAtTime acs t) = (rigidStateAtTime acs tstart).
  Proof using Type.
    apply LV0. destruct amc.
    simpl in *.
    tauto.
  Qed.

  (** 2 cases, based on whether the steering wheel is perfectly straight before driving.
    To avoid a  divide-by-0, the integration has to be done differently in these cases. *)
  Section TCNZ.
  Hypothesis (tcNZ : amTurn).
  
    Lemma AtomicMoveXT : {X (position acs)} tend =  Xs +
          ((Sin ({theta acs} tend) - Sin θs) [/] tc [//] tcNZ).
    Proof using All.
      pose proof (am_driveControls amc) as driveControlsb.
      pose proof (am_steeringControls amc) as steeringControls.
      setoid_rewrite (proj1 steeringControls) in driveControlsb.
      eapply  fixedSteeeringX with (t:= tend) (tcNZ0:=tcNZ) in driveControlsb.
      Unshelve. Focus 2. timeReasoning.
      unfold cf_div in driveControlsb.
      rewrite (fun p => LV0X acs tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      rewrite (fun p => LV0Theta acs tstart tdrive p tdrive) in driveControlsb;[| apply (proj2 steeringControls) 
          | timeReasoning ].
      setoid_rewrite <- driveControlsb. simpl. autounfold with IRMC. simpl. ring.
    Qed.

    Lemma AtomicMoveX : {X (position acs)} tend =  Xs +
          ((Sin (θs + tc * distance) - Sin θs) [/] tc [//] tcNZ).
    Proof using All.
      unfold cf_div. rewrite <- AtomicMoveθ.
      exact AtomicMoveXT.
    Qed.

    Lemma AtomicMoveYT : {Y (position acs)} tend =  Ys +
          ((Cos θs - Cos ({theta acs} tend)) [/] tc [//] tcNZ).
    Proof using All.
      pose proof (am_driveControls amc) as driveControlsb.
      pose proof (am_steeringControls amc) as steeringControls.
      setoid_rewrite (proj1 steeringControls) in driveControlsb.
      eapply  fixedSteeeringY with (t:= tend) (tcNZ0:=tcNZ) in driveControlsb.
      Unshelve. Focus 2. timeReasoning.
      unfold cf_div in driveControlsb.
      rewrite (fun p => LV0Y acs tstart tdrive p tdrive) 
          in driveControlsb;[| apply (proj2 steeringControls) 
                             | timeReasoning ].
      rewrite (fun p => LV0Theta acs tstart tdrive p tdrive) 
        in driveControlsb;[| apply (proj2 steeringControls) 
                           | timeReasoning ].
      setoid_rewrite <- driveControlsb. simpl. autounfold with IRMC. simpl. ring.
    Qed.


    Lemma AtomicMoveY : {Y (position acs)} tend =  Ys +
          ((Cos θs - Cos (θs + tc * distance)) [/] tc [//] tcNZ).
    Proof using All.
      unfold cf_div. rewrite <- AtomicMoveθ.
      exact AtomicMoveYT.
    Qed.

    Lemma AtomicMoveXYT : posAtTime acs tend =  Ps +
         {|X:=(Sin ({theta acs} tend) - Sin θs);
             Y:=(Cos θs - Cos ({theta acs} tend))|} 
      * '(f_rcpcl tc  tcNZ).
    Proof using All.
      split; simpl;[apply AtomicMoveXT | apply AtomicMoveYT].
    Qed.

    Lemma AtomicMoveXY : posAtTime acs tend =  Ps +
         {|X:=(Sin (θs + tc * distance) - Sin θs);
             Y:=(Cos θs - Cos (θs + tc * distance))|} 
      * '(f_rcpcl tc  tcNZ).
    Proof using All.
      split; simpl;[apply AtomicMoveX | apply AtomicMoveY].
    Qed.
  
  Require Import CoRN.logic.Stability.

    Section XYBounds.
    Variable cd :CarDimensions IR.

    Local Notation turnRadius  (* :IR *) := (f_rcpcl tc tcNZ).

  Lemma noSignChangeDuringWeaken: forall F a1 b1 a2 b2,
    noSignChangeDuring F a1 b1
    -> a1 ≤ a2
    -> b2 ≤ b1
    -> noSignChangeDuring F a2 b2.
  Proof using .
    intros ? ? ? ? ? Hn ? ?. destruct Hn as [Hn | Hn];[left|right];
      intros t Hb; apply Hn; destruct Hb; split; eauto 2 with CoRN.
  Qed.

  Lemma AMTurnCurvature : ∀ t : Time,
      tdrive ≤ t ≤ tend → {turnCurvature acs} t = tc.
  Proof using Type.
    destruct amc. simpl in *.
    apply proj1 in am_steeringControls0.
    setoid_rewrite am_steeringControls0 
        in am_driveControls0.
    assumption.
  Qed.

   Hypothesis nosign : noSignChangeDuring (linVel acs) tstart tend.
    
    (*Local*) Lemma confinedDuringTurningAMIfAux : forall (confineRect : Line2D IR),
    (∀ (θ : IR), inBetweenR θ ({theta acs} tstart) ({theta acs} tend)
     -> carMinMaxXY cd
          (turnRigidStateAtθ (rigidStateAtTime acs tstart) turnRadius θ ) 
           ⊆ confineRect)
     ->  confinedDuring acs tdrive tend cd confineRect.
    Proof using All.
      intros ? Hb.
      eapply noSignChangeDuringWeaken in nosign;
        [ |  exact (proj1 am_timeIncWeaken)
        | apply leEq_reflexive].
      destruct am_timeIncWeaken.
      pose proof (rigidStateNoChange tdrive) as XX.
      dimp XX;[|split;auto].
      eapply auxConfinedDuringAMIf; auto.
      - apply AMTurnCurvature.
      - intros ? Hj. rewrite XX.
        apply Hb. clear Hb.
        unfold inBetweenR in Hj. apply proj2 in XX.
        simpl in XX.
        rewrite  XX in Hj. exact Hj.
    Qed.

  Definition confinedTurningAM  (init : Rigid2DState IR) 
        (confineRect : Line2D IR) :=
    let θi := (θ2D init) in
    let θf := θi + tc * distance in
    ∀ (θ : IR), 
      inBetweenR θ θi θf
       -> carMinMaxXY cd
          (turnRigidStateAtθ init
           turnRadius θ)  ⊆ confineRect.

Lemma confinedDuringSplit : forall (confineRect : Line2D IR)
  (ts tm te :Time),
  ts ≤ tm
  -> tm ≤ te
  ->confinedDuring acs ts tm cd confineRect
  ->confinedDuring acs tm te cd confineRect
  ->confinedDuring acs ts te cd confineRect.
Proof using.
  intros ? ? ? ? hl hr cl cr t Hb.
  eapply stable. 
      Unshelve. Focus 2. apply StableSubsetLine2D.
           apply StableLeIR;fail.
  pose proof (leEq_or_leEq _ t tm) as Hd.
  eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
  destruct Hd;[apply cl|apply cr];
  repnd; split; auto.
Qed.
           
  Lemma confinedTurningAMCorrect : forall (confineRect : Line2D IR),
    confinedTurningAM (rigidStateAtTime acs tstart) confineRect
     ->  confinedDuring acs tstart tend cd confineRect.
  Proof using All.
    intros ?  hh.
    unfold confinedTurningAM in hh. simpl in hh.
    unfold inBetweenR in hh.
    setoid_rewrite <- AtomicMoveθ in hh.
    pose proof am_timeIncWeaken. repnd.
    apply confinedDuringSplit with (tm:=tdrive);
    auto; [|]; intros t Hb.
    - apply confinedDuringTurningAMIfAux in hh.
      rewrite rigidStateNoChange;[| repnd; split; auto].
      rewrite <- (rigidStateNoChange tdrive); [| split; auto;apply am_timeIncWeaken].
      apply hh. split; auto;apply am_timeIncWeaken.
    - apply confinedDuringTurningAMIfAux; auto.
  Qed.

  End XYBounds.
  End TCNZ.
              
  Section TCZ.
  Hypothesis (tcZ : amNoTurn).
  
    Lemma AtomicMoveZθ : forall t:Time, tstart ≤ t ≤ tend
    -> {theta acs} t =  θs.
    Proof using All.
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
         [rewrite (proj1 steeringControls), tcZ; IRring | ]. 
         repnd. split; timeReasoning.
    Qed.

    Lemma AtomicMoveZX : forall (t:Time) (pl : tstart ≤ t) (pr : t ≤ tend), 
    {X (position acs)} t =  Xs
     +  (∫ (mkIntBnd pl) (linVel acs)) * (Cos θs).
    Proof using All. 
      intros ? ? ?.
      apply leftShiftEqIR.
      rewrite mult_comm.
      eapply TBarrowScale with (ib := (mkIntBnd pl));
        [apply derivX | ].
      intros tt Hb. unfold mkIntBnd, intgBndL, intgBndR in Hb. simpl in Hb.
      rewrite mult_comm at 1.
      autounfold with TContRMC.
      rewrite IContRMultAp.
      rewrite CFCosAp.
      apply mult_wd;[| reflexivity].
      apply Cos_wd.
      apply AtomicMoveZθ.
      autounfold with IRMC. repnd;
      split; eauto 3 with CoRN.
   Qed.

    Lemma AtomicMoveZY : forall (t:Time) (pl : tstart ≤ t) (pr : t ≤ tend),
    {Y (position acs)} t =  Ys
     +  (∫ (mkIntBnd pl) (linVel acs)) * (Sin θs).
    Proof using All.
      intros ? ? ?.
      apply leftShiftEqIR.
      rewrite mult_comm.
      eapply TBarrowScale with (ib := (mkIntBnd pl));
        [apply derivY | ].
      intros tt Hb. unfold mkIntBnd, intgBndL, intgBndR in Hb. simpl in Hb.
      rewrite mult_comm at 1.
      autounfold with TContRMC.
      rewrite IContRMultAp.
      rewrite CFSineAp.
      apply mult_wd;[| reflexivity].
      apply Sin_wd.
      apply AtomicMoveZθ. 
      autounfold with IRMC. repnd;
      split; eauto 3 with CoRN.
    Qed.

    Lemma AtomicMoveZ : ∀ (t:Time) 
        (pl : tstart ≤ t) (pr : t ≤ tend), 
    posAtTime acs t =
    Ps + ' ∫ ((mkIntBnd pl)) (linVel acs) * (unitVec θs).
    Proof using All.
     split; simpl; [apply AtomicMoveZX | apply AtomicMoveZY];
     auto.
    Qed.

   Lemma AtomicMoveZFinal : rigidStateAtTime acs tend = 
     {| pos2D := Ps + ('distance) * (unitVec θs); θ2D := θs |}.
   Proof using All.
     split;[|apply AtomicMoveZθ;split; timeReasoning].
      rewrite  (am_driveDistanceFull).
     apply AtomicMoveZ. auto.
   Qed.

   Section XYBounds.
   Variable cd :CarDimensions IR.

(* RHS was automatically obtained *)
Lemma carMinMaxAtTEq : forall r, 
carMinMaxXY cd r = 
'(pos2D r) +
({|
lstart := minCart
            (minCart
               (minCart
                  (-
                   frontUnitVec r *
                   ' lengthBack cd +
                   rightSideUnitVec
                     r *
                   ' width cd)
                  (-
                   frontUnitVec r *
                   ' lengthBack cd -
                   rightSideUnitVec
                     r *
                   ' width cd))
               (frontUnitVec r *
                ' lengthFront cd -
                rightSideUnitVec
                  r * 
                ' width cd))
            (frontUnitVec r *
             ' lengthFront cd +
             rightSideUnitVec r *
             ' width cd);
lend := maxCart
          (maxCart
             (maxCart
                (- frontUnitVec r *
                 ' lengthBack cd +
                 rightSideUnitVec
                   r * 
                 ' width cd)
                (- frontUnitVec r *
                 ' lengthBack cd -
                 rightSideUnitVec
                   r * 
                 ' width cd))
             (frontUnitVec r *
              ' lengthFront cd -
              rightSideUnitVec r *
              ' width cd))
          (frontUnitVec r *
           ' lengthFront cd +
           rightSideUnitVec r *
           ' width cd) |}).
Proof using Type.
    intros ?.
    hideRight.
    unfold  carMinMaxXY. simpl.
    unfold boundingUnion. simpl.
    unfold backRight, backLeft.
    rewrite maxCartSum, minCartSum.
    unfold frontLeft.
    rewrite maxCartSum, minCartSum.
    unfold frontRight.
    rewrite maxCartSum, minCartSum.
    subst l.
    reflexivity.
Qed.

Lemma straightAMMinMaxXY : ∀ r d, 
   carMinMaxXY cd 
      {|pos2D := pos2D r + d ; θ2D := θ2D r |} 
    = carMinMaxXY cd r + 'd.
Proof using.
  intros.
  rewrite carMinMaxAtTEq.
  rewrite carMinMaxAtTEq.
  unfold frontUnitVec, rightSideUnitVec.
  simpl.
  match goal with
  [ |- _ + ?bb = _] => remember bb as l
  end.
  clear Heql.
  split; simpl; ring.
Qed.



Lemma straightAMMinMaxXYT : ∀ (t:Time) 
 (pl : tstart ≤ t) (pr : t ≤ tend), 
 carMinMaxAtT acs cd t =
 carMinMaxAtT acs cd tstart 
 + '(' ∫ ((mkIntBnd pl)) (linVel acs) * (unitVec θs)).
Proof using All.
  intros ? ? ?.
  unfold carMinMaxAtT.
  unfold rigidStateAtTime.
  rewrite AtomicMoveZθ; [|auto].
  rewrite AtomicMoveZ with (pl:=pl); [|auto].
  rewrite <- straightAMMinMaxXY.
  reflexivity.
Qed.


  Require Import MathClasses.orders.rings.
  Require Import MathClasses.interfaces.orders.

  (*Move: not intuitive at all, but turns out to be true,
      and exactly what is needed in the next lemma*)
  Lemma MinMax0Mult: forall (a b k:ℝ),
      Min 0 a ≤ b ≤ Max 0 a
      -> Min 0 (a*k) ≤ b*k ≤ Max 0 (a*k).
  Proof using .
    intros ? ? ? Hm.
    eapply stable.
    Unshelve. Focus 2. apply stable_conjunction; 
        apply StableLeIR; fail. 
    pose proof (leEq_or_leEq _ k 0) as Hd.
    eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
    destruct Hd as [Hd | Hd].
    - rewrite (@commutativity _ _ _ mult _).
      rewrite (@commutativity _ _ _ mult _ b). 
      rewrite <- negate_mult_negate.
      rewrite <- (negate_mult_negate k).
      apply flip_le_negate in Hd. rewrite negate_0 in Hd.
      assert (0 = (-k) * 0) as Xr by IRring.
      rewrite Xr. clear Xr.
      setoid_rewrite MinMultLeft;[| assumption].
      setoid_rewrite MaxMultLeft;[| assumption].
      split;
      apply mult_resp_leEq_lft; auto; clear dependent k;
      apply flip_le_negate;
      setoid_rewrite negate_involutive.
      + setoid_rewrite negate_0. tauto.
      + apply proj1 in Hm. rewrite <- negate_0.
        exact Hm.

    - rewrite (@commutativity _ _ _ mult _). 
      assert (0 = k * 0) as Xr by IRring.
      rewrite Xr. clear Xr.
      setoid_rewrite MinMultLeft;[| assumption].
      setoid_rewrite MaxMultLeft;[| assumption].
      rewrite (@commutativity _ _ _ mult _).
      repnd.
      split; apply mult_resp_leEq_lft; auto.
  Qed.
   
  (** When the car is moving straight (not turning), the 
      space needed (as a  rectangle) is the union
      of the initial bouding rectangle and the final
      bounding rectangle. Unlike while turning, the whole
      trajectory need not be considered
  *)
   Definition straightAMSpaceRequirement 
      (init : Rigid2DState IR) : Line2D IR :=
      let bi := carMinMaxXY cd init  in
      let bf := bi + '(('distance) * (unitVec (θ2D init))) in
          (boundingUnion bi bf).
          
   Lemma straightAMSpaceRequirementCorrect :
      noSignChangeDuring (linVel acs) tstart tend
      -> confinedDuring acs tstart tend cd 
          (straightAMSpaceRequirement 
                (rigidStateAtTime acs tstart)).
   Proof using All.
     unfold straightAMSpaceRequirement. 
     intros Hn t Hb.
     fold (carMinMaxAtT acs cd t).
     fold (carMinMaxAtT acs cd tstart).
     destruct Hb as [pl prr].
     rewrite straightAMMinMaxXYT with (pl:=pl);[| tauto].
     unfold boundingUnion.
     assert ((minxy (carMinMaxAtT acs cd tstart)) 
        = (minxy (carMinMaxAtT acs cd tstart)) + 0) as H0 by ring.
     rewrite H0. clear H0.
     assert ((maxxy (carMinMaxAtT acs cd tstart)) 
        = (maxxy (carMinMaxAtT acs cd tstart)) + 0) as H0 by ring.
     rewrite H0. clear H0.
     setoid_rewrite  minCartSum.
     setoid_rewrite  maxCartSum.
     rewrite foldPlusLine.
     replace {|
        lstart := minxy (carMinMaxAtT acs cd tstart);
        lend := maxxy (carMinMaxAtT acs cd tstart) |}
        with  (carMinMaxAtT acs cd tstart);[| reflexivity].
     simpl.
     apply order_preserving; eauto with
      typeclass_instances.
     remember (∫ (mkIntBnd pl) (linVel acs)) as dist.
     eapply nosignChangeInBwInt with (pl:=pl)
        (Hab := am_timeStartEnd) in Hn;[| assumption].
     unfold inBetweenR in Hn.
     rewrite <- am_driveDistanceFull in Hn.
     rewrite <- Heqdist in Hn. clear Heqdist.
     pose proof Hn as Hns.
     eapply MinMax0Mult with (k:= cos θs)in Hn.
     eapply MinMax0Mult with (k:= sin θs)in Hns.
     repnd.     
     split; split; simpl; tauto.
    Qed.
  End XYBounds.
  End TCZ.

End AtomicMove.

Section AtomicMoveSummary.
Context `(acs : AckermannCar maxTurnCurvature).

Definition AtomicMoveSign (am : AtomicMove) : Type :=
  (am_tc am =0) or (am_tc am[#]0).

Definition DAtomicMove := {am : AtomicMove 
    | AtomicMoveSign am }.

Global Instance EquivDAtomicMove : Equiv DAtomicMove.
Proof using.
  apply sigT_equiv.
Defined.

Global Instance EquivalenceCarDim 
   : Equivalence EquivDAtomicMove.
Proof using .
  unfold EquivDAtomicMove.
  eauto with typeclass_instances.
  unfold equiv, EquivDAtomicMove, sigT_equiv. split.
  - intros x. destruct x. simpl. split; auto with *.
  - intros x y. destruct x,y. simpl. intros Hd; repnd;
      rewrite Hd; reflexivity.

  - intros x y z. destruct x,y,z. simpl. intros H0 H1.
    repnd; rewrite H0; rewrite H1. reflexivity. 
Qed.


(** combine the final positions for,
    both for the cases of turning and driving straignt*)
Definition stateAfterAtomicMove 
  (cs : Rigid2DState IR) (dm : DAtomicMove): Rigid2DState IR:=
  
  let tc : IR := (am_tc (projT1 dm)) in
  let dist : IR := (am_distance (projT1 dm)) in
  let θInit :IR := (θ2D cs) in
  let θf :IR := θInit + tc*dist in
  let posInit : Cart2D IR := (pos2D cs) in
  let posDelta := 
    match (projT2 dm) with
    | inl _ =>  ('dist) * (unitVec θInit)
    | inr p => {|X:= (sin θf - sin θInit) * (f_rcpcl tc p) ; 
                Y:= (cos θInit - cos θf) * (f_rcpcl tc p)|}
    end in  
  {|pos2D := posInit + posDelta; θ2D := θf|}.

Global Instance ProperstateAfterAtomicMove:
Proper (equiv ==> equiv ==> equiv) 
  stateAfterAtomicMove.
Proof using.
  intros ? ? H1 aml amr H2.
  unfold stateAfterAtomicMove.
  destruct aml as [ml sl].
  destruct amr as [mr sr]. simpl. 
  unfold equiv, EquivDAtomicMove, sigT_equiv in H2.
  simpl in H2. unfold AtomicMoveSign in sl, sr.
  destruct sl as [sl | sl].
  - rewrite H2 in sl.
    destruct sr;[| eapply eq_imp_not_ap in sl; eauto; contradiction].
    rewrite  H1, H2. reflexivity.
  - destruct sr as [sr|];[rewrite <- H2 in sr;eapply eq_imp_not_ap in sr; eauto; contradiction|].
   rewrite H1.
   assert ((f_rcpcl (am_tc ml) sl) = (f_rcpcl (am_tc mr) c))
    as Heq by
    (apply f_rcpcl_wd; apply ProperAMTC; assumption).
   setoid_rewrite Heq.
   setoid_rewrite H2.
   reflexivity.
Qed.

Lemma stateAfterAtomicMoveCorrect : forall 
 (dm : DAtomicMove) 
  (tstart tend :Time)
  (p: tstart < tend),
  @CarExecutesAtomicMoveDuring _ acs (projT1 dm) tstart tend p
  -> rigidStateAtTime acs tend = 
      stateAfterAtomicMove (rigidStateAtTime acs tstart) dm.
Proof using.
  intros  ? ? ? ? Ham.
  destruct dm as [am s]. unfold stateAfterAtomicMove.
  destruct s as [s | s]; simpl.
  - rewrite s. rewrite mult_0_l, plus_0_r. eapply AtomicMoveZFinal; eauto. 
  - split; simpl; [eapply  AtomicMoveXY | eapply AtomicMoveθ]; eauto.
Qed. 

(** combine the sufficient conditions on space required,
    both for the cases of turning and driving straignt*)
Definition carConfinedDuringAM 
  (cd : CarDimensions IR) (rect : Line2D IR)
  (ams : DAtomicMove)
  (init : Rigid2DState IR)
   := 
let (am,s) :=ams in
match s with
| inl _ => (straightAMSpaceRequirement am cd init) ⊆ rect
| inr turn => (confinedTurningAM am turn cd init rect)
end.

Lemma carConfinedDuringAMCorrect:  forall 
  (cd : CarDimensions IR)
  (ams : DAtomicMove)
  (rect : Line2D IR)
  (tstart tend :Time)
  (p: tstart < tend),
  @CarMonotonicallyExecsAtomicMoveDuring _ acs (projT1 ams) tstart tend  p
  -> @carConfinedDuringAM cd rect ams (rigidStateAtTime acs tstart)
  -> confinedDuring acs tstart tend cd rect.
Proof using Type.
  intros  ? ? ? ? ? ? Ham Hcc.
  destruct Ham as [Ham Hnosign].
  destruct ams as [am s].
  destruct s as [s | s]; simpl in Hcc.
  - eapply (@straightAMSpaceRequirementCorrect _ acs) with (cd:=cd) in Ham;      eauto.
    intros t Hb. specialize (Ham t Hb).
    eauto 2 with relations.
  - eapply confinedTurningAMCorrect in Hcc; eauto.
Qed.

 
Global Instance ProperstraightAMSpaceRequirement:
 Proper (equiv ==> equiv ==> equiv ==> equiv) 
    straightAMSpaceRequirement.
Proof using.
  intros aml amr H1 ? ?  H2 ? ? H3.
  unfold straightAMSpaceRequirement.
  unfold BoundingRectangle.
  rewrite H3.
  rewrite H2.
  rewrite H1.
  reflexivity.
Qed.

(* overall case structure of the proof is similar to 
[ProperstateAfterAtomicMove] above*)
Global Instance ProperCarConfinedDuringAM:
Proper (equiv ==> equiv ==> equiv ==> equiv ==> iff) 
  (carConfinedDuringAM).
Proof using.
  intros ? ? H0 ? ? H1 aml amr H2 ? ? H3.
  unfold carConfinedDuringAM.
  destruct aml as [ml sl].
  destruct amr as [mr sr]. simpl. 
  unfold equiv, EquivDAtomicMove, sigT_equiv in H2.
  simpl in H2. unfold AtomicMoveSign in sl, sr.
  destruct sl as [sl | sl].
  - rewrite H2 in sl.
    destruct sr;[| eapply eq_imp_not_ap in sl; eauto; contradiction].
    rewrite H0, H1, H2, H3. tauto.
  - destruct sr as [sr|];[rewrite <- H2 in sr;eapply eq_imp_not_ap in sr; eauto; contradiction|].
   unfold confinedTurningAM. unfold inBetweenR.
   setoid_rewrite H1.
   setoid_rewrite H3.
   assert ((f_rcpcl (am_tc ml) sl) = (f_rcpcl (am_tc mr) c))
    as Heq by
    (apply f_rcpcl_wd; apply ProperAMTC; assumption).
   setoid_rewrite Heq.
   setoid_rewrite H2.
   setoid_rewrite H0.
   tauto.
Qed.


End AtomicMoveSummary.

Section Wdd.
  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).

  Lemma CarExecutesAtomicMoveDuring_wd :
  forall  ml mr tstartl tstartr tendl tendr 
      (pl :tstartl < tendl) (pr :tstartr < tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarExecutesAtomicMoveDuring acs ml pl
    -> ml = mr
    -> CarExecutesAtomicMoveDuring acs mr pr.
  Proof using Type.
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

     
  Lemma CarMonotonicallyExecsAtomicMoveDuring_wd:
  forall ml mr tstartl tstartr tendl tendr 
      (pl :tstartl < tendl) (pr :tstartr < tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarMonotonicallyExecsAtomicMoveDuring acs ml pl
    -> ml = mr
    -> CarMonotonicallyExecsAtomicMoveDuring acs mr pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?  tl tr Hl Heq.
    destruct Hl as [c Hl].
    split;[eapply CarExecutesAtomicMoveDuring_wd;eauto |].
    clear c. rewrite <- tl, <- tr. exact Hl.
  Qed.
  
  
  Lemma CarExecutesAtomicMoveDuring_wdtl :
  forall m tstartl tstartr tend 
      (pl :tstartl < tend) (pr :tstartr < tend),
    tstartl = tstartr
    -> CarExecutesAtomicMoveDuring acs m pl
    -> CarExecutesAtomicMoveDuring acs m pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?. eapply CarExecutesAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.

  Lemma CarExecutesAtomicMoveDuring_wdtr :
  forall m tstart tendl tendr 
      (pl :tstart < tendl) (pr :tstart < tendr),
    tendl = tendr
    -> CarExecutesAtomicMoveDuring acs m pl
    -> CarExecutesAtomicMoveDuring acs m pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?. eapply CarExecutesAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.

  Lemma CarMonotonicallyExecsAtomicMoveDuring_wdtr :
  forall m tstart tendl tendr 
      (pl :tstart < tendl) (pr :tstart < tendr),
    tendl = tendr
    -> CarMonotonicallyExecsAtomicMoveDuring acs m pl
    -> CarMonotonicallyExecsAtomicMoveDuring acs m pr.
  Proof using Type.
    intros ? ? ? ? ? ? ? ?. eapply CarMonotonicallyExecsAtomicMoveDuring_wd; eauto; reflexivity.
  Qed.


(** * Executing a sequence of atomic moves *)
  Definition AtomicMoves := list AtomicMove.
  


  Inductive executesMultipleMovesDuring 
    (execSingleMoveDuring : AtomicMove → ∀ tstart tend : Time, tstart < tend → Type)
    : AtomicMoves -> forall (tstart tend : Time),  (tstart ≤ tend) -> Prop :=
  | amscNil : forall (tl tr:Time) (pe : tl = tr)(p: tl≤tr), 
        executesMultipleMovesDuring execSingleMoveDuring [] tl tr p
  | amscCons : forall (tstart tmid tend:Time) (pl : tstart < tmid) (pr : tmid ≤ tend) (p : tstart ≤ tend)
      (h: AtomicMove) (tl : AtomicMoves), 
      @execSingleMoveDuring h tstart tmid pl
      -> executesMultipleMovesDuring execSingleMoveDuring tl tmid tend pr
      -> executesMultipleMovesDuring execSingleMoveDuring(h::tl) tstart tend p.

  
  (** This predicate defines what it means for a car to follow 
    a list of atomic moves from time [tstart] to [tend].*)
  Definition CarExecutesAtomicMovesDuring :=
    executesMultipleMovesDuring (CarExecutesAtomicMoveDuring acs).

  Definition CarMonotonicallyExecsAtomicMovesDuring :=
    executesMultipleMovesDuring (CarMonotonicallyExecsAtomicMoveDuring acs).

End Wdd.


Ltac substAtomicMoves amscrrl :=
    let pll := fresh "pll" in 
    let Hf := fresh "Hf" in 
    match type of amscrrl with
    ?l = _ => match goal with
        [  amscrl: @CarExecutesAtomicMoveDuring _ _ _ _ l ?pl0 |- _]
        =>
    pose proof pl0 as pll;
    rewrite amscrrl in pll;
    pose proof (@CarExecutesAtomicMoveDuring_wdtr _ _ _ _ _ _ 
      pl0 pll amscrrl amscrl) as Hf; clear dependent l
      end
      end.

Ltac substAtomicMovesMon amscrrl :=
    let pll := fresh "pll" in 
    let Hf := fresh "Hf" in 
    match type of amscrrl with
    ?l = _ => match goal with
        [  amscrl: @CarMonotonicallyExecsAtomicMoveDuring _ _ _ _ l ?pl0 |- _]
        =>
    pose proof pl0 as pll;
    rewrite amscrrl in pll;
    pose proof (@CarMonotonicallyExecsAtomicMoveDuring_wdtr _ _ _ _  _ _ 
      pl0 pll amscrrl amscrl) as Hf; clear dependent l
      end
      end.

Ltac invertAtomicMoves :=
  (repeat match goal with
    [ H: CarExecutesAtomicMovesDuring _ _ _ _ _ |- _] =>
      unfold CarExecutesAtomicMovesDuring in H
   | [ H: CarMonotonicallyExecsAtomicMovesDuring _ _ _ _ _ |- _] =>
      unfold CarMonotonicallyExecsAtomicMovesDuring in H
   | [ H: executesMultipleMovesDuring _ _ _ _ _ |- _] =>
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      let pl := fresh H "pl" in
      let pr := fresh H "pr" in
      (inverts H as Hl Hr pl pr;[]);
      try  substAtomicMoves Hl;
      try  substAtomicMovesMon Hl
  (* invert only if only 1 case results. o/w inf. loop will result if there are fvars*)
  end);
  repeat match goal with
    [ H: eq ?x ?x |- _] => clear H
    | [ H: le ?x ?x |- _] => clear H
  end.
  
Hint Resolve timeLtWeaken : timeReasoning.
Section Wddd.
  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).

    Lemma CarExecutesAtomicMovesDuring_wd :
    forall ml mr,
         ml = mr
 -> forall tstartl tstartr tendl tendr 
      (pl :tstartl ≤ tendl) (pr :tstartr ≤ tendr),
    tstartl = tstartr
    -> tendl = tendr
    -> CarExecutesAtomicMovesDuring acs ml _ _ pl
    -> CarExecutesAtomicMovesDuring acs mr _ _ pr.
  Proof using Type.
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
    Proper (equiv ==> iff) (fun m => CarExecutesAtomicMovesDuring acs m tstart tend p).
  Proof using Type.
    intros ? ? ?. split; apply CarExecutesAtomicMovesDuring_wd; 
    eauto 1 with relations.
  Qed.


Fixpoint carConfinedDuringAMs (cd : CarDimensions IR)
  (rect : Line2D IR) 
  (lam : list DAtomicMove)
  (init : Rigid2DState IR) : Prop  :=
match lam with
| [] => carMinMaxXY cd init ⊆ rect
| m::tl => (carConfinedDuringAM cd rect m init) /\ 
            carConfinedDuringAMs cd rect tl (stateAfterAtomicMove init m)
end.



Global Instance ProperCarConfinedDuringAMs:
  Proper (equiv ==> equiv ==> equiv ==> equiv ==> iff) 
    (carConfinedDuringAMs).
Proof using.
  intros ? ? H1 ? ? H2 ? ? meq.
  induction meq as [| h1 h2 t1 t2 meq]; intros ? ? H3.
  - simpl. rewrite H1, H2, H3. tauto.
  - simpl.
    pose proof H3 as Hb.
    apply ProperstateAfterAtomicMove in H3.
    specialize (H3 _ _ meq).
    apply IHmeq in H3.
    rewrite H3. clear H3 IHmeq.
    rewrite meq.
    rewrite H1.
    rewrite Hb.
    rewrite H2.
    tauto.
Qed.

(*Move to geometry2DProps*)
Lemma minCart_leEq_lft: ∀ x y : Cart2D ℝ, 
  minCart x y ≤ x.
Proof using .
  intros ? ?.
  split; apply Min_leEq_lft.
Qed.

Lemma minCart_leEq_rht: ∀ x y : Cart2D ℝ, 
  minCart x y ≤ y.
Proof using .
  intros ? ?. rewrite commutativity.
  apply minCart_leEq_lft.
Qed.

Lemma lft_leEq_maxCart: ∀ x y : Cart2D ℝ, 
  x ≤ maxCart x y.
Proof using .
  intros ? ?.
  split; apply lft_leEq_Max.
Qed.

Lemma rht_leEq_maxCart: ∀ x y : Cart2D ℝ, 
  y ≤ maxCart x y.
Proof using .
  intros ? ?. rewrite commutativity.
  apply lft_leEq_maxCart.
Qed.

Lemma leEq_minCart : ∀ x y z : Cart2D ℝ, 
  z ≤ x → z ≤ y → z ≤ minCart x y.
Proof using .
  intros ? ? ? Hab Hbc.
  destruct Hab, Hbc.
  split; apply leEq_Min; assumption.
Qed.

Lemma maxCart_leEq : ∀ x y z : Cart2D ℝ, 
  x ≤ z → y ≤ z → maxCart x y ≤ z.
Proof using .
  intros ? ? ? Hab Hbc.
  destruct Hab, Hbc.
  split; apply Max_leEq; assumption.
Qed.

  
Hint Resolve minCart_leEq_lft
minCart_leEq_rht
lft_leEq_maxCart
rht_leEq_maxCart
leEq_minCart
maxCart_leEq
 : MinMaxCart.

Lemma boundingUnionIff: forall (a b c : Line2D IR),
  boundingUnion a b ⊆ c
  <-> (a ⊆ c /\ b ⊆ c).
Proof using .
  intros. unfold boundingUnion, le, LeAsSubset.
  simpl. split; intro hh.
  - repnd. split; split;
    eapply (@transitivity (Cart2D ℝ) le _);
    try apply hhl;
    try apply hhr;
    eauto using
      minCart_leEq_lft,
      minCart_leEq_rht,
      lft_leEq_maxCart,
      rht_leEq_maxCart.
  - repnd. split; eauto using 
      leEq_minCart, maxCart_leEq.
Qed.
  
(*a more convenient characterization 
of the single case*)
Lemma carConfinedDuringAMsSingle: forall
  (cd : CarDimensions IR)
  (rect : Line2D IR) 
  (m : DAtomicMove)
  (init : Rigid2DState IR),
carConfinedDuringAMs cd rect [m] init
<-> carConfinedDuringAM cd rect m init.
Proof using.
  intros ? ? ? ?. simpl.
  split;[tauto|].
  intros Hc. split;[assumption|].
  destruct m as [m s]. simpl in Hc.
  destruct s as [s|s];
  unfold stateAfterAtomicMove; simpl.
  - simpl. unfold straightAMSpaceRequirement in Hc.
    apply boundingUnionIff in Hc.
    apply proj2 in Hc.
    simpl in Hc.
    eapply (@transitivity (Line2D ℝ) le _);
      [|apply Hc].
    apply eq_le.
    rewrite <- straightAMMinMaxXY.
    rewrite s, mult_0_l, plus_0_r.
    reflexivity.
  - unfold confinedTurningAM in Hc.
    specialize (Hc (θ2D init + am_tc m * am_distance m)).
    apply Hc. clear Hc.
    unfold inBetweenR.
    split; eauto with CoRN.
Qed.


Lemma carConfinedDuringAMsCorrect : forall
  (cd : CarDimensions IR)
  (rect : Line2D IR)
  (tstart tend :Time)
  p
  (dams : list DAtomicMove),
  let ams := List.map (@projT1 _ _) dams in
  CarMonotonicallyExecsAtomicMovesDuring acs ams tstart tend  p
  -> @carConfinedDuringAMs cd rect dams (rigidStateAtTime acs tstart)
  -> confinedDuring acs tstart tend cd rect.
Proof using Type.
  intros  ? ? ? ? ? ? ? Ham. remember ams as l. subst ams.
  revert Heql. revert dams. 
  induction Ham; intros ? ? Hcc.
  - destruct dams; inverts Heql. simpl in Hcc.
    intros ? Hb. rewrite <- pe in Hb.
    destruct Hb as [Hbl Hbr]. 
    eapply po_antisym in Hbl. specialize (Hbl Hbr).
    clear Hbr. rewrite <- Hbl. assumption.
  - destruct dams as [| m tm];inverts Heql as Heql Haa Hbb.
    pose proof (timeLtWeaken  pl).
    specialize (IHHam _ eq_refl).
    simpl in Hcc. repnd.
    eapply carConfinedDuringAMCorrect with (p0:=pl) in Hccl;
      eauto.
    rewrite <- stateAfterAtomicMoveCorrect 
      with (p0:=pl) in Hccr; destruct X; eauto.
    apply IHHam in Hccr.
    clear IHHam c Ham. revert pl pr Hccl Hccr. clear.
    intros. eapply confinedDuringSplit with (tm:=tmid); eauto.
    apply timeLtWeaken. assumption.
Qed.

End Wddd.



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
    ∀ mt (acs : AckermannCar mt)
   (tstart tend : Time)  (p: tstart ≤ tend),
      CarExecutesAtomicMovesDuring acs ams tstart tend p
      -> (posAtTime acs tstart = posAtTime acs tend 
          /\ {theta acs} tstart = {theta acs} tend).

  (** [MovesIsInverse ams amsr] implies [MovesIdentity (ams ++ amsr)],
    but the other direction many not be true 
     This extra strength is useful because
    in the sideways move below, Wriggle-inverse does not immediately
    follow the Wriggle-move. *)
    
    
(*         TODO : quantify over [acs]. *)
  Definition MovesInverse (ams amsr : AtomicMoves) :=
    ∀ mt (acs : AckermannCar mt)
      (tstart tend : Time)  (p: tstart ≤ tend)
      (tstartr tendr : Time)  (pr: tstartr ≤ tendr),
      CarExecutesAtomicMovesDuring acs ams tstart tend p
      -> CarExecutesAtomicMovesDuring acs amsr tstartr tendr pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> (posAtTime acs tend - posAtTime acs tstart
          = posAtTime acs tstartr - posAtTime acs tendr
          /\ {theta acs} tstart = {theta acs} tendr).



(** if each atomic move is executed monotonically, we can aslo
    relate the confinements of the car in axis aligned rectangles.*)
Definition MonotonicMovesInverse (dams damsr : list DAtomicMove)  :=
  let ams  := List.map (@projT1 _ _) dams in
  let amsr  := List.map (@projT1 _ _) damsr in
  ∀ mt (acs : AckermannCar mt) (cd : CarDimensions ℝ) (confineRect: Line2D IR)
    (tstart tend : Time)  (p: tstart ≤ tend)
    (tstartr tendr : Time)  (pr: tstartr ≤ tendr),
    CarMonotonicallyExecsAtomicMovesDuring acs ams tstart tend p
    -> CarMonotonicallyExecsAtomicMovesDuring acs amsr tstartr tendr pr
    -> carConfinedDuringAMs cd confineRect dams (rigidStateAtTime acs tstart)
    -> carConfinedDuringAMs cd
          (confineRect + '(posAtTime acs tendr - posAtTime acs tstart))
          damsr (rigidStateAtTime acs tstartr).


  Definition CarExecutesAtomicMovesDuringAux  
  mt (acs : AckermannCar mt)
      (tstart tend : Time)  (p: tstart ≤ tend) m
       := CarExecutesAtomicMovesDuring acs m tstart tend p .
  
   Lemma foldForProperAM : ∀ mt (acs : AckermannCar mt) m 
      (tstart tend : Time)  (p: tstart ≤ tend),
      CarExecutesAtomicMovesDuring acs m tstart tend p ≡
      CarExecutesAtomicMovesDuringAux acs tstart tend p m.
   Proof using Type. reflexivity. Qed.

  Global Instance CarExecutesAtomicMovesDuringAux_Proper mt (acs : AckermannCar mt)
  (tstart tend : Time)  (p :tstart ≤ tend) :
    Proper (equiv ==> iff) (CarExecutesAtomicMovesDuringAux acs tstart tend p).
  Proof using Type.
    apply CarExecutesAtomicMovesDuring_ProperM.
  Qed.

  Global Instance MovesInverseProper : Proper 
    (equiv ==> equiv ==> iff)  MovesInverse.
  Proof using Type.
    intros ? ? ? ? ? ?. unfold MovesInverse.
    setoid_rewrite (foldForProperAM acs x).
    setoid_rewrite (foldForProperAM acs x0).
    setoid_rewrite  H.
    setoid_rewrite  H0.
    tauto.
  Qed.
      

        
  Definition AtomicMoveInv (m : AtomicMove) : AtomicMove
      := {|am_tc := am_tc m; am_distance := -(am_distance m) |}.

  Definition AtomicMovesInv (ms : AtomicMoves) : AtomicMoves
      := rev (List.map AtomicMoveInv ms).


  Lemma atomicMoveInvertibleθ :
    ∀ mt (acs : AckermannCar mt) m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring acs m  p
      -> CarExecutesAtomicMoveDuring acs (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> ({theta acs} tstart = {theta acs} tendr).
  Proof using Type.
    intros ? ? m ? ? ? ? ? ? amscl amscrl Ht.
    apply AtomicMoveθ in amscl.
    apply AtomicMoveθ in amscrl.
    simpl in amscl, amscrl.
    rewrite amscrl, Ht, amscl.
    IRring.
  Qed.

  (** The equations for X coordinate are different, based on whether the steering wheel is perfectly
      straight or not. The double negation trick works while proving equality *)
  Lemma atomicMoveInvertibleXY :
    ∀ mt (acs : AckermannCar mt) m
      (tstart tend : Time)  (p: tstart < tend)
      (tstartr tendr : Time)  (pr: tstartr < tendr),
      CarExecutesAtomicMoveDuring acs m  p
      -> CarExecutesAtomicMoveDuring acs (AtomicMoveInv m)  pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> (posAtTime acs tend - posAtTime acs tstart 
              = posAtTime acs tstartr - posAtTime acs tendr).
  Proof using Type.
    intros ? ? m ? ? ? ? ? ? amscl amscrl Hte.
    pose proof amscl as Htt.
    eapply atomicMoveInvertibleθ in Htt; eauto.
    eapply stable. 
      Unshelve. Focus 2. apply StableEqCart2D.
           apply StableEqIR;fail.
    pose proof (decideEdDN (am_tc m) [0]) as Hd.
    eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
    destruct Hd as [Hd | Hd].
    - apply AtomicMoveZFinal with (pr0 := p) in amscl;
        [| exact Hd].
      apply AtomicMoveZFinal with (pr0 := pr) in amscrl;
        [| exact Hd]. simpl in amscl.
      destruct amscl as [amsclr amscll].
      destruct amscrl as [amscrlr amscrll].
      simpl in amsclr, amscrlr.
      rewrite amscrlr,  amsclr, Hte, amscll.
      unfold cast, castCRCart2DCR. rewrite sameXYNegate. simpl.
      ring.
    - apply AtomicMoveXYT with (tcNZ:= Hd) in amscl.
      eapply AtomicMoveXYT  in amscrl.
      Unshelve. Focus 2. apply Hd;fail.
      simpl in amscl, amscrl.
      rewrite amscrl, Hte, amscl, Htt.
       split; simpl; IRring.
    Qed.

  Lemma atomicMoveInvertible :
    ∀ (m : AtomicMove), MovesInverse [m] [AtomicMoveInv m].
  Proof using Type.
    intros ? ? m ? ? ? ? ? ? ?.
    invertAtomicMoves.
    intros ? ?.    
    invertAtomicMoves.
    split.
    - eapply atomicMoveInvertibleXY; eauto.
    - eapply atomicMoveInvertibleθ in Hf0; eauto.
  Qed.

  Definition DAtomicMoveInv (m : DAtomicMove) : DAtomicMove:=
    existT _ (AtomicMoveInv (projT1 m)) (projT2 m).

  Definition DAtomicMovesInv (ms : list DAtomicMove) : list DAtomicMove
      := rev (List.map DAtomicMoveInv ms).


Lemma atomicMonoMoveInvertible :
    ∀ (m : DAtomicMove), 
    MonotonicMovesInverse [m] [DAtomicMoveInv m].
Proof.
  intros m.
  intros ? ? ? ? ? ? ? ? ? ? Hcm Hcmi Hcon.
  rename confineRect into rect.
  simpl in Hcm.
  simpl in Hcmi.
  invertAtomicMoves.
  apply carConfinedDuringAMsSingle.
  unfold DAtomicMoveInv, AtomicMoveInv in *.
  destruct m as [m s].
  simpl in *.
  destruct s as [s | s].
  - simpl in *.
  Abort.

  Lemma MoveInvInvolutive : ∀ (m : AtomicMove), 
    AtomicMoveInv (AtomicMoveInv m) = m.
  Proof using .
    intros m.
    destruct m. unfold AtomicMoveInv, equiv, Equiv_AtomicMove. simpl.
    split; [| reflexivity]. apply negate_involutive.
  Qed.

  Lemma movesControlsApp : ∀ mt (acs : AckermannCar mt) 
  (l r : AtomicMoves) (tstart tend: Time)
    (pr : tstart ≤ tend),
    CarExecutesAtomicMovesDuring acs (l++r) _ _ pr
    -> exists (tmid : Time), exists (p : tstart ≤ tmid ≤ tend),
         CarExecutesAtomicMovesDuring acs l tstart tmid (proj1 p)
        /\ CarExecutesAtomicMovesDuring acs r tmid tend (proj2 p).
  Proof using Type.
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
  Proof using Type.
    intros m. remember [AtomicMoveInv m].
    setoid_rewrite <- MoveInvInvolutive.
    subst.
    apply atomicMoveInvertible.
  Qed.
    
    
  
  Lemma MovesControlsSingle : ∀ mt (acs : AckermannCar mt) 
  (m : AtomicMove) (tstart tend: Time)
    (pr : tstart < tend),
    @CarExecutesAtomicMoveDuring _ acs m tstart tend pr
    -> CarExecutesAtomicMovesDuring acs [m] tstart tend (timeLtWeaken pr).
  Proof using Type.
    intros. econstructor; eauto. econstructor. reflexivity.
    Unshelve. apply leEq_reflexive.
  Qed.

   
   

  Lemma atomicMovesInvertibleAux :
    ∀ (m : AtomicMoves), MovesInverse (AtomicMovesInv m) m.
  Proof using Type.
    induction m as [| h tl Hind]; intros ? ? ? ? ? ? ? ? Hm Hrm Ht;
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
  Proof using .
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
  Proof using Type.
    intros m. remember (AtomicMovesInv m).
    setoid_rewrite <- (MovesInvInvolutive m).
    subst.
    apply atomicMovesInvertibleAux.
  Qed.
  
End Invertability.
