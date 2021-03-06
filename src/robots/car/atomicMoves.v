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
Require Import car.errorBounds.
Require Import ackermannSteeringProp.
Require Import IRMisc.LegacyIRRing.


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
Require Import MathClasses.theory.setoids.
Unset Implicit Arguments.
(* Move to MCMisc. Does MC have such a construct? *)
Definition Setoid_Mor (A B :Type) `{Equiv A} `{Equiv B} : Type:=
  sig (@Setoid_Morphism A B _ _).
Set Implicit Arguments.


Infix "-->" := (Setoid_Mor).

Typeclasses Transparent Setoid_Mor.
Global Instance EquivSetoisMor (A B :Type) `{Equiv A} `{Equiv B} :
  Equiv  (A --> B).
Proof.
  apply sig_equiv.
Defined.  

Global Instance EquivalenceSetoisMor (A B :Type) `{Equiv A} `{Equiv B} :
  Equivalence (@equiv (A --> B) _).
Proof.
  constructor.
- intros ? ?. apply ext_equiv_refl.
- intros ? ?. eapply ext_equiv_sym.
- intros ? ? ? . eapply ext_equiv_trans.
Unshelve.
destruct x. destruct s. 
eauto with relations typeclass_instances.
destruct x. destruct s. 
eauto with relations typeclass_instances.
destruct x. destruct s. 
eauto with typeclass_instances.
destruct x. destruct s. 
eauto with typeclass_instances.
Qed.
Set Implicit Arguments.

(** * Atomic Move

We will build complex manueuvers out of the following basic move :
turn the steering wheel so that the turnCurvature has a particular value ([tc]),
and then drive for a particular distance ([distance]).
Note that both [tc] and [distance] are signed -- the turn center can be on the either side,
and one can drive both forward and backward *)
  Record AtomicMove (R:Type) := mkAtomicMove
  {
     am_distance : R;
     am_tc : R
  }.

  (** Needed because equality on reals (IR) is different 
      from syntactic equality 
      ([≡]). *)
      
  Global Instance Equiv_AtomicMove `{Equiv R} : Equiv (AtomicMove R) :=
    fun (ml mr : AtomicMove R) => (am_distance ml = am_distance mr) 
          /\ (am_tc ml = am_tc mr).

  (** To make tactics like [reflexivity] work, we needs to show
  that the above defined custom defined equality on [AtomicMove] 
  is an equivalence relation.*)
  Global Instance Equivalence_instance_AtomicMove `{Setoid R} 
    : @Equivalence (AtomicMove R) equiv.
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

Global Instance ProperAMTC `{Equiv R} : 
Proper (equiv ==> equiv) (@am_tc R).
Proof using.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Global Instance ProperAMDistance `{Equiv R} : 
Proper (equiv ==> equiv) (@am_distance R).
Proof using.
  intros ? ? Heq. destruct Heq. tauto.
Qed.

Section AtomicMove.

  Context  {maxTurnCurvature : Qpos}
   (acs : AckermannCar maxTurnCurvature).
  Variable am : AtomicMove IR.
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

  Definition confinedInRect (cd :CarDimensions IR) (rect : Line2D IR) 
  : (Rigid2DState IR) --> Prop.
  Proof using.
  exists (fun s => carMinMaxXY cd s ⊆ rect).
  constructor; unfold Setoid; eauto 2 with typeclass_instances.
  intros ? ? Heq.
  rewrite Heq. reflexivity.
  Defined. 

  Global Instance ProperConfinedInRect :
    Proper (equiv ==> equiv ==> equiv) confinedInRect.
  Proof.
    intros ? ? H1 ? ? H2 ? ? H3. unfold confinedInRect. simpl.
    rewrite H1, H2, H3.
    reflexivity.
  Qed.



    Section XYBounds.
    Variable cd :CarDimensions IR.

    Local Notation turnRadius  (* :IR *) := (f_rcpcl tc tcNZ).


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



  Definition holdsDuringTurningAM  (init : Rigid2DState IR) 
        (P : (Rigid2DState IR) --> Prop) :=
    let θi := (θ2D init) in
    let θf := θi + tc * distance in
    ∀ (θ : IR), 
      inBetweenR θ θi θf
       -> (`P) (turnRigidStateAtθ init turnRadius θ).



  





  Definition confinedTurningAM  (init : Rigid2DState IR) 
        (confineRect : Line2D IR) :=
    holdsDuringTurningAM init (confinedInRect cd confineRect).

Lemma holdsDuringSplit : forall (P:Rigid2DState ℝ --> Prop)
  (ts tm te :Time) (stabl : forall s, util.Stable ((`P) s)) ,
  ts ≤ tm
  -> tm ≤ te
  -> (∀ t : Time, ts ≤ t ≤ tm → (`P) (rigidStateAtTime acs t))
  -> (∀ t : Time, tm ≤ t ≤ te → (`P) (rigidStateAtTime acs t))
  -> (∀ t : Time, ts ≤ t ≤ te → (`P) (rigidStateAtTime acs t)).
Proof using.
  intros ? ? ? ? ? hl hr cl cr t Hb.
  apply stable. 
  pose proof (leEq_or_leEq _ t tm) as Hd.
  eapply DN_fmap;[exact Hd|]. clear Hd. intro Hd.
  destruct Hd;[apply cl|apply cr];
  repnd; split; auto.
Qed.

Global Instance confineInRectStable :
∀ s : Rigid2DState ℝ, util.Stable ((` (confinedInRect cd confineRect)) s).
Proof using.
  intros ? ?. simpl.
  apply StableSubsetLine2D.
  apply StableLeIR.  
Qed.

Lemma confinedDuringSplit : forall (confineRect : Line2D IR)
  (ts tm te :Time),
  ts ≤ tm
  -> tm ≤ te
  ->confinedDuring acs ts tm cd confineRect
  ->confinedDuring acs tm te cd confineRect
  ->confinedDuring acs ts te cd confineRect.
Proof using.
  intros ? ? ? ? ? ?.
  unfold confinedDuring.
  eapply holdsDuringSplit with (P:= confinedInRect cd confineRect); auto.
  (* eauto with typeclass_instances. *)
  apply confineInRectStable.
Qed.

  Local Opaque Min.
  Local Opaque Max.

  Lemma holdsDuringTurningAMCorrect : forall (P:Rigid2DState ℝ --> Prop)
    (stabl : forall s, util.Stable ((`P) s)),
    holdsDuringTurningAM (rigidStateAtTime acs tstart) P
    ->  ∀ t : Time, tstart ≤ t ≤ tend → (`P) (rigidStateAtTime acs t).
  Proof using pr nosign amc.
    intros ?  hs hh.
    unfold confinedTurningAM, holdsDuringTurningAM in hh. simpl in hh.
    unfold inBetweenR in hh.
    setoid_rewrite <- AtomicMoveθ in hh.
    pose proof am_timeIncWeaken. repnd.
    destruct P as [P pp].
    apply holdsDuringSplit with (tm:=tdrive);
    trivial; [|]; intros t Hb; simpl in *.
    - rewrite rigidStateNoChange;[| repnd; split; auto].
      specialize (hh θs).
      unfold turnRigidStateAtθ in hh. simpl in hh.
      do 2 rewrite plus_negate_r in hh.
      setoid_rewrite mult_0_l in hh.
      rewrite plus_0_r in hh.
      apply hh. split; eauto with *.
    - 
      eapply noSignChangeDuringWeaken in nosign;
        [ |  exact (proj1 am_timeIncWeaken)
        | apply leEq_reflexive].
      destruct am_timeIncWeaken.
      pose proof (rigidStateNoChange tdrive) as XX.
      dimp XX;[|split;auto].
      eapply holdsDuringAMIf; eauto.
      + apply AMTurnCurvature.
      + intros ? Hj. rewrite XX.
        apply hh. clear hh.
        unfold inBetweenR in Hj. apply proj2 in XX.
        simpl in XX.
        rewrite  XX in Hj. exact Hj.
  Qed.

    (* TODO: reuse the second bullet of holdsDuringTurningAMCorrect above *)
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

  Lemma confinedTurningAMCorrect : forall (confineRect : Line2D IR),
    confinedTurningAM (rigidStateAtTime acs tstart) confineRect
     ->  confinedDuring acs tstart tend cd confineRect.
  Proof using pr nosign amc.
    intros ?  hh ?.
      eapply holdsDuringTurningAMCorrect 
        with (P:=confinedInRect cd confineRect); eauto with typeclass_instances.
  Qed.

  End XYBounds.

  End TCNZ.


  Section TCZ.
  Hypothesis (tcZ : amNoTurn).
  
    Lemma AtomicMoveZθ : forall t:Time, tstart ≤ t ≤ tend
    -> {theta acs} t =  θs.
    Proof using tcZ pr amc am.
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

(*
Lemma displacedCarMinMaxXY2 : ∀ r d, 
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
*)
Lemma displacedCarMinMaxXY : ∀ r d, 
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
  rewrite <- displacedCarMinMaxXY.
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

  (* unlike in the turn case, P does not need to be a setoid morphism *)
   Definition holdsDuringStAM  (init : Rigid2DState IR) 
        (P : (Rigid2DState IR) -> Prop) :=
     ∀ (d : IR), 
       inBetweenR d [0] distance
       -> P {|pos2D := pos2D init + ( 'd * (unitVec (θ2D init))); θ2D := θ2D init|}.

   Lemma straightAMSpaceRequirementCorrectAux : forall init,
    holdsDuringStAM init (fun s => carMinMaxXY cd s ⊆ straightAMSpaceRequirement init).
   Proof using.
     clear.
     unfold straightAMSpaceRequirement. unfold holdsDuringStAM.
     intros init d Hb. simpl.
     unfold boundingUnion.
     assert ((minxy (carMinMaxXY cd init)) 
        = (minxy (carMinMaxXY cd init)) + 0) as H0 by ring.
     rewrite H0. clear H0.
     assert ((maxxy (carMinMaxXY cd init)) 
        = (maxxy (carMinMaxXY cd init)) + 0) as H0 by ring.
     rewrite H0. clear H0.
     setoid_rewrite  minCartSum.
     setoid_rewrite  maxCartSum.
     rewrite foldPlusLine.
     simpl.
     pose proof (displacedCarMinMaxXY init (' d * unitVec (θ2D init)))
      as Hd.
     simpl in *.
     rewrite Hd.
     apply order_preserving; eauto with
      typeclass_instances.
      rename Hb into Hn.
     unfold inBetweenR in Hn.
     pose proof Hn as Hns.
     eapply MinMax0Mult with (k:= cos (θ2D init))in Hn.
     eapply MinMax0Mult with (k:= sin (θ2D init))in Hns.
     repnd.     
     split; split; simpl; try tauto.
   Qed.
 
   Lemma holdsDuringStAMIff : forall rect init,
    holdsDuringStAM init (fun s => carMinMaxXY cd s ⊆ rect)
    <-> straightAMSpaceRequirement init ⊆ rect.
   Proof using.
    clear.
    intros. split; intro H.
  - pose proof (H 0) as Hl.
    unfold inBetweenR in Hl.
      dimp Hl;[| eauto with *].
    pose proof (H distance) as Hr.
    unfold inBetweenR in Hr.
      dimp Hr;[| eauto with *].
    unfold straightAMSpaceRequirement.
    simpl.
    apply boundingUnionIff.
    simpl in *.
    rewrite <- displacedCarMinMaxXY.
    simpl in *.
    split; auto. clear Hr.
    rewrite preserves_0 in Hl.
    rewrite mult_0_l, plus_0_r  in Hl.
    assumption.
  - intros t Hb. apply straightAMSpaceRequirementCorrectAux with (init:=init )in Hb.
    simpl in *. eauto with relations.
  Qed.


   Lemma holdsDuringStAMCorrect : forall (P: (Rigid2DState IR) -> Prop)
    `{@Setoid_Morphism  _ _ _ _ P},
    noSignChangeDuring (linVel acs) tstart tend
    -> holdsDuringStAM (rigidStateAtTime acs tstart) P
    ->  ∀ t : Time, tstart ≤ t ≤ tend → P (rigidStateAtTime acs t).
   Proof using tcZ amc pr.
     intros ? ? Hn Hh t Hb.
     destruct Hb as [pl prr].
     eapply nosignChangeInBwInt with (pl:=pl)
        (Hab := am_timeStartEnd) in Hn;[| assumption].
     unfold inBetweenR in Hn.
     rewrite <- am_driveDistanceFull in Hn.
     unfold rigidStateAtTime.
     rewrite AtomicMoveZθ; [|auto].
     rewrite AtomicMoveZ with (pl:=pl); [|auto].
     specialize (Hh (∫ (mkIntBnd pl) (linVel acs)) Hn).
     clear Hn.
     simpl in *.
     assumption.
    Qed.

  (* TODO : reuse [holdsDuringStAMCorrect] above *)
   Lemma straightAMSpaceRequirementCorrect :
      noSignChangeDuring (linVel acs) tstart tend
      -> confinedDuring acs tstart tend cd 
          (straightAMSpaceRequirement 
                (rigidStateAtTime acs tstart)).
   Proof using tcZ amc pr.
     intros Hn t Hb.
     fold (carMinMaxAtT acs cd t).
     fold (carMinMaxAtT acs cd tstart).
     destruct Hb as [pl prr].
     eapply nosignChangeInBwInt with (pl:=pl)
        (Hab := am_timeStartEnd) in Hn;[| assumption].
     unfold inBetweenR in Hn.
     rewrite <- am_driveDistanceFull in Hn.
     pose proof (@straightAMSpaceRequirementCorrectAux 
        (rigidStateAtTime acs tstart) _ Hn) as H.
     rewrite straightAMMinMaxXYT with (pl:=pl) by assumption.
     eapply transitivity;[| apply H].
     simpl in *.
     unfold carMinMaxAtT.
     rewrite <- displacedCarMinMaxXY. simpl.
     reflexivity.
    Qed.

    
  End XYBounds.
  End TCZ.

End AtomicMove.

Section AtomicMoveSummary.
Context `(acs : AckermannCar maxTurnCurvature).

Definition AtomicMoveSign `{Zero R} `{ApartT R} `{Equiv R} 
  (am : AtomicMove R) : Type :=
  (am_tc am =0) or (am_tc am ≭ 0).

Definition DAtomicMove (R:Type) `{Zero R} `{ApartT R} `{Equiv R}
  := {am : AtomicMove R 
    | AtomicMoveSign am }.
    
Global Arguments DAtomicMove R {_} {_} {_}.

Global Instance EquivDAtomicMove `{Zero R} `{ApartT R} `{Equiv R}  : Equiv (DAtomicMove R).
Proof using.
  apply sigT_equiv.
Defined.

Global Instance EquivalenceDAtomicMove  `{Setoid R} `{Zero R} `{ApartT R}
   : Equivalence EquivDAtomicMove.
Proof using .
  fold (@equiv (DAtomicMove R) _).
  eapply setoids.sigT_setoid.
  Unshelve.
  unfold Setoid.
  eauto with typeclass_instances.
Qed.

(** combine the final positions for,
    both for the cases of turning and driving straignt*)
Definition stateAfterAtomicMove `{Ring R} `{ApartT R} `{ReciprocalT R}
  `{SinClass R} `{CosClass R}
  (cs : Rigid2DState R) (dm : @DAtomicMove R _ _ _): Rigid2DState R:=
  
  let tc : R := (am_tc (projT1 dm)) in
  let dist : R := (am_distance (projT1 dm)) in
  let θInit :R := (θ2D cs) in
  let θf :R := θInit + tc*dist in
  let posInit : Cart2D R := (pos2D cs) in
  let posDelta := 
    match (projT2 dm) with
    | inl _ =>  ('dist) * (unitVec θInit)
    | inr p => {|X:= (sin θf - sin θInit) * (recipT tc p) ; 
                Y:= (cos θInit - cos θf) * (recipT tc p)|}
    end in  
  {|pos2D := posInit + posDelta; θ2D := θf|}.

Global Instance ProperstateAfterAtomicMove:
Proper (equiv ==> equiv ==> equiv) 
  (@stateAfterAtomicMove IR _ _ _ _ _ _ _ _ _ _ _ _ _).
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
   assert ((f_rcpcl (am_tc ml) sl) = (f_rcpcl (am_tc mr) a))
    as Heq by
    (apply f_rcpcl_wd; apply ProperAMTC; assumption).
   setoid_rewrite Heq.
   setoid_rewrite H2.
   reflexivity.
Qed.

Lemma stateAfterAtomicMoveCorrect : forall 
 (dm : DAtomicMove  IR) 
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

Definition holdsDuringAM 
  (ams : DAtomicMove IR)
  (init : Rigid2DState IR) (P : (Rigid2DState IR) --> Prop)
   := 
let (am,s) :=ams in
match s with
| inl _ => holdsDuringStAM am init (`P)
| inr turn => holdsDuringTurningAM am turn init P
end.

(** combine the sufficient conditions on space required,
    both for the cases of turning and driving straignt*)
Definition carConfinedDuringAM 
  (cd : CarDimensions IR) (rect : Line2D IR)
  (ams : DAtomicMove IR)
  (init : Rigid2DState IR)
   := holdsDuringAM ams init (confinedInRect cd rect).

Lemma holdsDuringAMCorrect:  forall (P : Rigid2DState ℝ --> Prop)
  (stable : ∀ s0 : Rigid2DState ℝ, util.Stable ((` P) s0))
  (ams : DAtomicMove IR)
  (tstart tend :Time)
  (p: tstart < tend),
  @CarMonotonicallyExecsAtomicMoveDuring _ acs (projT1 ams) tstart tend  p
  -> holdsDuringAM ams (rigidStateAtTime acs tstart) P
  -> ∀ t : Time, tstart ≤ t ≤ tend → (`P) (rigidStateAtTime acs t).
Proof using Type.
  intros  ? ? ? ? ? ? Ham Hcc.
  destruct Ham as [Ham Hnosign].
  destruct ams as [am s].
  destruct s as [s | s]; simpl in Hcc.
  - intros t Hb.
    eapply holdsDuringStAMCorrect; eauto.
  - intros t Hb.
    eapply holdsDuringTurningAMCorrect; eauto.
Qed.

Lemma carConfinedDuringAMCorrect:  forall 
  (cd : CarDimensions IR)
  (ams : DAtomicMove IR)
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
  - rewrite holdsDuringStAMIff in Hcc; auto.
    intros t Hb.
    eapply (@straightAMSpaceRequirementCorrect _ acs) with (cd:=cd) in Ham; eauto.
    specialize (Ham t Hb). simpl in *.
    eauto with relations.
  -  eapply confinedTurningAMCorrect; eauto.
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

(*
Global Instance EquivRigid2DProp : Equiv (Rigid2DState ℝ --> Prop).
  apply sig_equiv .
Defined.
*)

(*
Global Instance EquivalenceRigid2DProp : Equivalence  EquivRigid2DProp.
  apply setoids.sig_setoid.
Defined.
*)
(*
Global Instance EquivalenceDAtomicMove  `{Setoid R} `{Zero R} `{ApartT R}
   : Equivalence EquivDAtomicMove.
Proof using .
  unfold EquivDAtomicMove.
  eauto with typeclass_instances.
  unfold equiv, EquivDAtomicMove, sigT_equiv. split.
  - intros x. destruct x. simpl. split; auto with *.
  - intros x y. destruct x,y. simpl. intros Hd; repnd;
      rewrite Hd; reflexivity.

  - intros x y z. destruct x,y,z. simpl. intros h0 h1.
    repnd; rewrite h0; rewrite h1. reflexivity. 
Qed.
*)

(* Move to the definition of holdsDuringStAM*)
Global Instance ProperHoldsDuringStAM:
Proper (equiv ==> equiv ==> equiv ==> iff) 
  (holdsDuringStAM).
Proof using.
  intros aml amr H2 ? ? H3 ? ? Hp.
  unfold holdsDuringStAM, inBetweenR.
  setoid_rewrite H2.
  apply iff_under_forall.
  intro. apply iff_under_imp. intro H.
  apply Hp.
  rewrite H3. reflexivity.
Qed.

Global Instance ProperHoldsDuringAM:
Proper (equiv ==> equiv ==> equiv ==> iff) 
  (holdsDuringAM).
Proof using.
  intros aml amr H2 ? ? H3 ? ? Hp.
  unfold carConfinedDuringAM, holdsDuringAM,
    inBetweenR.
  destruct aml as [ml sl].
  destruct amr as [mr sr].
  Local Opaque Min.
  Local Opaque Max.
  unfold equiv, EquivDAtomicMove, sigT_equiv in H2.
  simpl in H2. unfold AtomicMoveSign in sl, sr.
  destruct sl as [sl | sl].
  - rewrite H2 in sl.
    destruct sr;[| eapply eq_imp_not_ap in sl; eauto; contradiction].
    apply ProperHoldsDuringStAM; auto.
  - destruct sr as [sr|];[rewrite <- H2 in sr;eapply eq_imp_not_ap in sr; eauto; 
      contradiction|].
    apply iff_under_forall.
    intro.
    assert ((f_rcpcl (am_tc ml) sl) =  (f_rcpcl (am_tc mr) a))  as Hh by
      (apply f_rcpcl_wd; rewrite H2; reflexivity).
    destruct x0.
    destruct y0. simpl.
    rewrite Hh. clear Hh.
    unfold inBetweenR.
    rewrite H2.
    rewrite H3.
    apply iff_under_imp. intro H.
    apply Hp.
    reflexivity.
  Qed.

(* overall case structure of the proof is similar to 
[ProperstateAfterAtomicMove] above*)
Global Instance ProperCarConfinedDuringAM:
Proper (equiv ==> equiv ==> equiv ==> equiv ==> iff) 
  (carConfinedDuringAM).
Proof using.
  
  intros ? ? H0 ? ? H1 aml amr H2 ? ? H3.
  apply ProperHoldsDuringAM; try assumption.
  intros a b Hab. simpl.
  rewrite H0.
  rewrite H1.
  rewrite Hab.
  reflexivity.  
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
  Definition AtomicMoves (R:Type ):= list (AtomicMove R).
  


  Inductive executesMultipleMovesDuring 
    (execSingleMoveDuring : AtomicMove IR → ∀ tstart tend : Time, tstart < tend → Type)
    : AtomicMoves IR -> forall (tstart tend : Time),  (tstart ≤ tend) -> Prop :=
  | amscNil : forall (tl tr:Time) (pe : tl = tr)(p: tl≤tr), 
        executesMultipleMovesDuring execSingleMoveDuring [] tl tr p
  | amscCons : forall (tstart tmid tend:Time) (pl : tstart < tmid) (pr : tmid ≤ tend) (p : tstart ≤ tend)
      (h: AtomicMove IR) (tl : AtomicMoves IR), 
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

Fixpoint holdsDuringAMs 
  (lam : list (DAtomicMove IR))
  (init : Rigid2DState IR) P : Prop  :=
match lam with
| [] => (`P) init
| m::tl => (holdsDuringAM m init P) /\ 
            holdsDuringAMs tl (stateAfterAtomicMove init m) P
end.


Definition carConfinedDuringAMs (cd : CarDimensions IR)
  (rect : Line2D IR) 
  (lam : list (DAtomicMove IR))
  (init : Rigid2DState IR) : Prop  :=
  holdsDuringAMs lam init (confinedInRect cd rect).

Definition stateAfterAtomicMoves :
(list (DAtomicMove IR))->Rigid2DState IR ->Rigid2DState IR :=
fold_left stateAfterAtomicMove.

Global Instance ProperHoldsDuringAMs:
  Proper (equiv ==>  equiv ==> equiv ==> iff) 
    (holdsDuringAMs).
Proof using.
  intros ? ? meq. unfold carConfinedDuringAMs.
  induction meq as [| h1 h2 t1 t2 meq]; intros ? ? H3 ? ? H4.
  - simpl. apply H4. assumption.
  - simpl.
    assert (forall A B C D, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D ) ) as H by tauto.
    apply H;clear H;[apply ProperHoldsDuringAM; auto|].
    apply IHmeq; auto.
    apply ProperstateAfterAtomicMove in H3. auto.
Qed.


Global Instance ProperCarConfinedDuringAMs:
  Proper (equiv ==> equiv ==> equiv ==> equiv ==> iff) 
    (carConfinedDuringAMs).
Proof using.
  intros ? ? H1 ? ? H2 ? ? meq ? ? H3.
  apply ProperHoldsDuringAMs; auto.
  intros ? ? Hab.
  simpl.
  rewrite H1, H2, Hab.
  reflexivity.
Qed.

Lemma holdsDuringAMsCorrect : forall (P : Rigid2DState ℝ --> Prop)
  (stable : ∀ s0 : Rigid2DState ℝ, util.Stable ((` P) s0))
  (tstart tend :Time)
  p
  (dams : list (DAtomicMove IR)),
  let ams := List.map (@projT1 _ _) dams in
  CarMonotonicallyExecsAtomicMovesDuring acs ams tstart tend  p
  ->  holdsDuringAMs dams (rigidStateAtTime acs tstart) P
  ->  ∀ t : Time, tstart ≤ t ≤ tend → (`P) (rigidStateAtTime acs t).
Proof using Type.
  intros  ? ? ? ? ? ? ? Ham. remember ams as l. subst ams.
  revert Heql. revert dams. 
  induction Ham; intros ? ? Hcc.
  - destruct dams; inverts Heql. simpl in Hcc.
    intros ? Hb. rewrite <- pe in Hb.
    destruct Hb as [Hbl Hbr]. 
    eapply po_antisym in Hbl. specialize (Hbl Hbr).
    clear Hbr.
    destruct P as [P pp]. simpl in *.
    rewrite <- Hbl. assumption.
  - destruct dams as [| m tm];inverts Heql as Heql Haa Hbb.
    pose proof (timeLtWeaken  pl).
    specialize (IHHam _ eq_refl).
    unfold carConfinedDuringAMs in Hcc.
    simpl in Hcc. repnd.
    rewrite <- stateAfterAtomicMoveCorrect 
      with (p0:=pl) in Hccr; destruct X; eauto.
    eapply holdsDuringSplit with (tm0:=tmid); eauto.
    clear IHHam.
    intros.
    eapply holdsDuringAMCorrect with (p0:=pl) in Hccl; eauto.
    split; auto.
  Qed.

Lemma carConfinedDuringAMsCorrect : forall
  (cd : CarDimensions IR)
  (rect : Line2D IR)
  (tstart tend :Time)
  p
  (dams : list (DAtomicMove IR)),
  let ams := List.map (@projT1 _ _) dams in
  CarMonotonicallyExecsAtomicMovesDuring acs ams tstart tend  p
  -> @carConfinedDuringAMs cd rect dams (rigidStateAtTime acs tstart)
  -> confinedDuring acs tstart tend cd rect.
Proof using Type.
  intros  ? ? ? ? ? ? ? ? ? ?.
   eapply holdsDuringAMsCorrect 
       with (P:=confinedInRect cd rect); eauto with typeclass_instances.
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

  Definition MovesIdentity (ams : AtomicMoves IR) :=
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
    
    
  Definition MovesInverse (ams amsr : AtomicMoves IR) :=
    ∀ mt (acs : AckermannCar mt)
      (tstart tend : Time)  (p: tstart ≤ tend)
      (tstartr tendr : Time)  (pr: tstartr ≤ tendr),
      CarExecutesAtomicMovesDuring acs ams tstart tend p
      -> CarExecutesAtomicMovesDuring acs amsr tstartr tendr pr
      -> {theta acs} tstartr = {theta acs} tend 
      -> (posAtTime acs tend - posAtTime acs tstart
          = posAtTime acs tstartr - posAtTime acs tendr
          /\ {theta acs} tstart = {theta acs} tendr).





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
      

        
  Definition AtomicMoveInv `{Negate R} (m : AtomicMove R) : AtomicMove R
      := {|am_tc := am_tc m; am_distance := -(am_distance m) |}.

  Definition AtomicMovesInv `{Negate R} (ms : AtomicMoves R) : AtomicMoves R
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
    ∀ (m : AtomicMove IR), MovesInverse [m] [AtomicMoveInv m].
  Proof using Type.
    intros ? ? m ? ? ? ? ? ? ?.
    invertAtomicMoves.
    intros ? ?.    
    invertAtomicMoves.
    split.
    - eapply atomicMoveInvertibleXY; eauto.
    - eapply atomicMoveInvertibleθ in Hf0; eauto.
  Qed.

  Lemma MoveInvInvolutive : ∀ (m : AtomicMove IR), 
    AtomicMoveInv (AtomicMoveInv m) = m.
  Proof using .
    intros m.
    destruct m. unfold AtomicMoveInv, equiv, Equiv_AtomicMove. simpl.
    split; [| reflexivity]. apply negate_involutive.
  Qed.

  Lemma movesControlsApp : ∀ mt (acs : AckermannCar mt) 
  (l r : AtomicMoves IR) (tstart tend: Time)
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
    ∀ (m : AtomicMove IR), MovesInverse  [AtomicMoveInv m] [m].
  Proof using Type.
    intros m. remember [AtomicMoveInv m].
    setoid_rewrite <- MoveInvInvolutive.
    subst.
    apply atomicMoveInvertible.
  Qed.
    
    
  
  Lemma MovesControlsSingle : ∀ mt (acs : AckermannCar mt) 
  (m : AtomicMove IR) (tstart tend: Time)
    (pr : tstart < tend),
    @CarExecutesAtomicMoveDuring _ acs m tstart tend pr
    -> CarExecutesAtomicMovesDuring acs [m] tstart tend (timeLtWeaken pr).
  Proof using Type.
    intros. econstructor; eauto. econstructor. reflexivity.
    Unshelve. apply leEq_reflexive.
  Qed.

   
   

  Lemma atomicMovesInvertibleAux :
    ∀ (m : AtomicMoves IR), MovesInverse (AtomicMovesInv m) m.
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
  
  Lemma MovesInvInvolutive : ∀ (m : AtomicMoves IR), 
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
  ∀ (m : AtomicMoves IR), MovesInverse m (AtomicMovesInv m).
  Proof using Type.
    intros m. remember (AtomicMovesInv m).
    setoid_rewrite <- (MovesInvInvolutive m).
    subst.
    apply atomicMovesInvertibleAux.
  Qed.
  
  
End Invertability.

Section  SpaceInvertability.

Add Ring tempRingIR : (stdlib_ring_theory IR).

Require Import MathClasses.interfaces.canonical_names.

Lemma holdsDuringAMEndpoints: forall P
  (m : (DAtomicMove IR))
  (init : Rigid2DState IR),
holdsDuringAM m init P
→ (`P) (stateAfterAtomicMove init m)
   /\ (`P) init.
Proof.
  intros ? ? ? Hc.
  destruct P as [P Pp]. simpl.
  destruct m as [m s]. simpl in Hc.
  destruct s as [s|s].
- simpl.
  pose proof (Hc 0) as Hl.
  unfold inBetweenR in Hl.
  dimp Hl;[| eauto with *].
  pose proof (Hc (am_distance m)) as Hr.
  unfold inBetweenR in Hr.
  dimp Hr;[| eauto with *].
  unfold stateAfterAtomicMove. simpl.
  rewrite s, mult_0_l, plus_0_r.
  rewrite preserves_0 in Hl.
  rewrite  mult_0_l, plus_0_r in Hl.
  destruct init; simpl in *.
  dands; tauto.
- unfold stateAfterAtomicMove; simpl.
  unfold confinedTurningAM in Hc.
  pose proof (Hc (θ2D init)) as Hcc.
  unfold turnRigidStateAtθ in Hcc.
  specialize (Hc (θ2D init + am_tc m * am_distance m)).
  unfold turnRigidStateAtθ in Hc.
  simpl in Hcc.
  rewrite plus_negate_r in Hcc.
  rewrite plus_negate_r in Hcc.
  fold (@Zero_instance_Cart2D IR _) in Hcc.
  fold (@zero (Cart2D IR) _) in Hcc.
  rewrite mult_0_l, plus_0_r in Hcc.
  destruct init; simpl in *.
  split;[ apply Hc | apply Hcc]; clear Hc Hcc;
  unfold inBetweenR;
  split; eauto with CoRN.
Qed.

Lemma carConfinedDuringAMEndpoints: forall
  (cd : CarDimensions IR)
  (rect : Line2D IR) 
  (m : (DAtomicMove IR))
  (init : Rigid2DState IR),
carConfinedDuringAM cd rect m init
→ (carMinMaxXY cd (stateAfterAtomicMove init m) ⊆ rect
   /\ carMinMaxXY cd init ⊆ rect).
Proof.
  intros ? ? ? ?.
  apply holdsDuringAMEndpoints.
Qed.

(*a more convenient characterization 
of the single case*)
Lemma holdsDuringAMsSingle: forall P
  (m : (DAtomicMove IR))
  (init : Rigid2DState IR),
holdsDuringAMs [m] init P
<-> holdsDuringAM m init P.
Proof using.
  intros ? ? ?. simpl.
  split;[tauto|].
  intros Hc. split;[assumption|].
  apply holdsDuringAMEndpoints in Hc.
  tauto.
Qed.

(*a more convenient characterization 
of the single case*)
Lemma carConfinedDuringAMsSingle: forall
  (cd : CarDimensions IR)
  (rect : Line2D IR) 
  (m : (DAtomicMove IR))
  (init : Rigid2DState IR),
carConfinedDuringAMs cd rect [m] init
<-> carConfinedDuringAM cd rect m init.
Proof using.
  intros ? ? ?. apply holdsDuringAMsSingle.
Qed.

Definition DAtomicMoveInv `{Zero R}
`{ApartT R} `{Equiv R} `{Negate R}
 (m : (DAtomicMove R)) : (DAtomicMove R):=
  existT _ (AtomicMoveInv (projT1 m)) (projT2 m).

Definition DAtomicMovesInv `{Zero R}
`{ApartT R} `{Equiv R} `{Negate R}
(ms : list (DAtomicMove R)) : list (DAtomicMove R)
  := rev (List.map DAtomicMoveInv ms).

(** if each atomic move is executed monotonically, we can aslo
    relate the confinements of the car in axis aligned rectangles.*)
Definition MovesSpaceInverse (dams damsr : list (DAtomicMove IR)) := 
  ∀ (init initr : Rigid2DState ℝ)
 (cd : CarDimensions ℝ) (confineRect: Line2D IR),
 let disp := pos2D (stateAfterAtomicMoves damsr initr) - pos2D init in
 θ2D initr = θ2D (stateAfterAtomicMoves dams init)
 -> carConfinedDuringAMs cd confineRect dams init
 -> carConfinedDuringAMs cd
     (confineRect + 'disp)
          damsr initr.

(* analogous to [MovesInverse], but more convenient as there is no car*)
Definition MovesStateInverse (damsl damsr : list (DAtomicMove IR)) := 
  ∀ (initl initr : Rigid2DState ℝ) ,
 let endl := (stateAfterAtomicMoves damsl initl) in
 let endr := (stateAfterAtomicMoves damsr initr) in
 θ2D initr = θ2D endl
 -> (pos2D endl - pos2D initl
    = pos2D initr - pos2D endr
    /\ θ2D initl = θ2D endr).

Lemma holdsDuringAMsAppend : forall P la lb init,
holdsDuringAMs (la++lb) init P
<-> (holdsDuringAMs la init P
    /\ holdsDuringAMs lb (stateAfterAtomicMoves la init) P).
Proof.
  induction la; intros lb init.
- simpl. split; [|tauto].
  intros Hc.
  destruct lb;[simpl in *; tauto|].
  simpl in *. repnd. split;[| tauto].
  clear Hcr.
  apply holdsDuringAMEndpoints in Hcl; tauto.
- simpl. rewrite IHla. tauto.
Qed. 

Lemma carConfinedDuringAMsAppend : forall cd rect la lb init,
carConfinedDuringAMs cd rect (la++lb) init
<-> (carConfinedDuringAMs cd rect la init 
    /\ carConfinedDuringAMs cd rect lb (stateAfterAtomicMoves la init)).
Proof.
  intros ? ?. apply holdsDuringAMsAppend.
Qed. 


Require Import MCMisc.rings.
Local Opaque Max.
Local Opaque Min.

(*reuse this to prove atomicMoveInvertible*)
Lemma atomicMoveStateInvertible :
    ∀ (m : (DAtomicMove IR)), 
    MovesStateInverse [m] [DAtomicMoveInv m].
Proof using.
  intros m.
  intros  ? ? ? ? Ht. subst endl endr.
  unfold stateAfterAtomicMoves.
  simpl fold_left.
  unfold DAtomicMoveInv, AtomicMoveInv in *.
  destruct m as [m s].
  destruct s as [s | s].
  - simpl in *. rewrite s in *.
    rewrite mult_0_l, plus_0_r in Ht.
    rewrite Ht. split;[| ring].
    rewrite preserves_negate.
    ring.
  - simpl. rewrite Ht. simpl.
    split;[| ring].
    rewrite <- negate_mult_distr_r.
    rewrite RingProp2.
    split; simpl; ring.
Qed.

Lemma DMoveInvInvolutive : ∀ (m : (DAtomicMove IR)), 
    DAtomicMoveInv (DAtomicMoveInv m) = m.
Proof using .
  intros m.
  apply MoveInvInvolutive.
Qed.

Lemma DMovesInvInvolutive : ∀ (m : list (DAtomicMove IR)), 
  DAtomicMovesInv (DAtomicMovesInv m) = m.
Proof using .
  induction m;[reflexivity |].
  unfold DAtomicMovesInv. simpl.
  rewrite map_app.
  rewrite map_cons.
  rewrite rev_app_distr.
  simpl.
  rewrite DMoveInvInvolutive.
  constructor; auto.
Qed.

Lemma atomicMovesStateInvertibleAux :
  ∀ (m : list (DAtomicMove IR)), MovesStateInverse (DAtomicMovesInv m) m.
Proof using.
  induction m as [| h tl Hind];
  intros ? ? ?  ? Ht; subst endl endr;
    [simpl in *; split;[ ring| auto]|].
  simpl in *.
  unfold DAtomicMovesInv in *.
  simpl in *.
  revert Ht.
  setoid_rewrite fold_left_app.
  simpl fold_left.
  fold stateAfterAtomicMoves.
  pose proof (atomicMoveStateInvertible (DAtomicMoveInv h)) as X.
  unfold MovesStateInverse in X.
  unfold stateAfterAtomicMoves in X.
  simpl fold_left in X.
  intro Ht.
  specialize (X _ _  Ht).
  rewrite DMoveInvInvolutive in X.
  unfold DAtomicMoveInv in Ht. simpl in Ht.
  rewrite <- negate_mult_distr_r in Ht.
  symmetry in Ht.
  rewrite RingShiftMinus in Ht.
  symmetry in Ht.
  rewrite (@commutativity _ _ _ plus _) in Ht.
  unfold MovesStateInverse in Hind.
  specialize (Hind _ (stateAfterAtomicMove initr h) Ht).
  clear Ht.
  repnd. clear Xr.
  split;[| exact Hindr].
  clear Hindr.
  pose proof (@sg_op_proper _ _ plus  _ _ _ Hindl _ _ Xl) as Hadd.
  clear Hindl  Xl.
  unfold sg_op in Hadd.
  ring_simplify in Hadd.
  rewrite (@commutativity _ _ _ plus _).
  symmetry.
  rewrite (@commutativity _ _ _ plus _).
  symmetry.
  exact Hadd.
Qed.  

Lemma atomicMoveSpaceInvertible :
    ∀ (m : (DAtomicMove IR)), 
    MovesSpaceInverse [m] [DAtomicMoveInv m].
Proof using.
  intros m.
  intros ? ? ? ? ? Ht.
  rewrite carConfinedDuringAMsSingle.
  rewrite carConfinedDuringAMsSingle.
  intro Hcon.
  rename confineRect into rect.
  remember disp as d.
  assert (d=disp) as Heq by (rewrite Heqd; reflexivity).
  clear Heqd. subst disp.
  unfold DAtomicMoveInv, AtomicMoveInv in *.
  destruct m as [m s].
  simpl in *.
  destruct s as [s | s].
  - rewrite holdsDuringStAMIff. unfold straightAMSpaceRequirement,
    stateAfterAtomicMove in *.
    simpl in *. rewrite s in Ht.
    rewrite mult_0_l, plus_0_r in Ht.
    rewrite Ht in Heq. rewrite Ht.
    rewrite <- (@simple_associativity _ _  plus _ _) in Heq.
    rewrite (@commutativity _ _ _ plus _) in Heq.
    apply RingShiftMinus in Heq.
    rewrite preserves_negate in Heq.
    ring_simplify in Heq.
    replace initr with {| pos2D := pos2D initr; 
      θ2D := θ2D initr |}; 
      [| destruct initr; reflexivity].
    rewrite <- Heq. clear Heq.
    rewrite  (@commutativity _ _ _ plus _).
    rewrite Ht.
    rewrite displacedCarMinMaxXY.
    rewrite preserves_negate.
    rewrite <- negate_mult_distr_l.
    rewrite <- (@simple_associativity _ _  plus _ _).
    rewrite <- preserves_plus.
    rewrite RingProp2.
    rewrite (@commutativity _ _ _ plus _ d).
    rewrite  preserves_plus.
    rewrite  (@simple_associativity _ _  plus _ _).
    rewrite  (@commutativity _ _ _ plus _ _ ('d)).
    rewrite  (@commutativity _ _ _ plus _ _ ('d)).
    rewrite boundingUnionPlus.
    rewrite  (@commutativity _ _ _ plus _ _ ('d)).
    apply order_preserving; 
      [eauto 2 with typeclass_instances|].
    rewrite  (@commutativity _ _ _ boundingUnion _ _ ).
    rewrite holdsDuringStAMIff in Hcon.
    exact Hcon.
  - unfold holdsDuringTurningAM, confinedTurningAM, inBetweenR in *. 
    simpl in *.
    intro.
    rewrite Ht.
    rewrite <- negate_mult_distr_r.
    rewrite <- (@simple_associativity _ _  plus _ _).
    rewrite plus_negate_r.
    rewrite plus_0_r.
    rewrite <- (@commutativity _ _ _ Min _ _).
    rewrite <- (@commutativity _ _ _ Max _ _).
    intro Hb.
    specialize (Hcon _ Hb). clear Hb.
    rewrite <- (@simple_associativity _ _  plus _ _) in Heq.
    rewrite (@commutativity _ _ _ plus _) in Heq.
    apply RingShiftMinus in Heq.
    ring_simplify in Heq.
    rewrite (@commutativity _ _ _ plus _) in Heq.
    replace initr with {| pos2D := pos2D initr; 
      θ2D := θ2D initr |}; 
      [| destruct initr; reflexivity].
    rewrite <- Heq. clear Heq.
    unfold turnRigidStateAtθ in *.
    simpl in *. rewrite Ht.
    rewrite <- negate_mult_distr_r.
    rewrite RingProp2.
    rewrite <- (@simple_associativity (Cart2D IR) 
          _  plus _ _).
    rewrite <- (@simple_associativity (Cart2D IR) 
          _  plus _ _).
    unfold plus at 3. unfold Plus_instance_Cart2D at 3.
    simpl.
    unfold sin, cos, SinClassIR, CosClassIR.
    match goal with
    [|- context [{|
            X :=?x ; Y :=?y|} ]] 
         => ring_simplify x; ring_simplify y
    end.
    match type of Hcon with
    carMinMaxXY _ ?r ⊆ _ =>
       match goal with
       [|- carMinMaxXY _ ?rr ⊆ _]
          => assert 
           (rr= {| pos2D := pos2D r + d; θ2D := θ2D r |})
           as Heq by
         (split;[split;simpl; unfold recipT, RecipTIR; try ring|reflexivity])
       end
    end.
    rewrite Heq. clear Heq.
    rewrite displacedCarMinMaxXY.
    rewrite  (@commutativity _ _ _ plus _ _ ('d)).
    rewrite  (@commutativity _ _ _ plus _ _ ('d)).
    apply order_preserving; 
      [eauto 2 with typeclass_instances|].
    exact Hcon.
  Qed.





Lemma atomicMovesSpaceInvertibleAux :
  ∀ (m : list (DAtomicMove IR)), MovesSpaceInverse (DAtomicMovesInv m) m.
Proof using Type.
  induction m as [| h tl Hind];
  intros ? ? ? ? ? Ht Hcon;
  remember disp as d;
  assert (d=disp) as Heq by (rewrite Heqd; reflexivity);
  clear Heqd; subst disp; unfold carConfinedDuringAMs.
- simpl in *.
  rewrite (@commutativity _ _ _ plus _) in Heq.
  apply RingShiftMinus in Heq.
  ring_simplify in Heq.
  replace initr with {| pos2D := pos2D initr; 
      θ2D := θ2D initr |}; 
      [| destruct initr; reflexivity].
  rewrite <- Heq. clear Heq.
  rewrite Ht.
  rewrite (@commutativity _ _ _ plus _).
  rewrite displacedCarMinMaxXY.
  rewrite (@commutativity _ _ _ plus _).
  rewrite (@commutativity _ _ _ plus _ _ ('d)).
  apply order_preserving; 
      [eauto 2 with typeclass_instances|].
  exact Hcon.
- unfold DAtomicMovesInv in *.
  simpl in *.
  setoid_rewrite fold_left_app in Ht.
  simpl in Ht.
  fold stateAfterAtomicMoves in Ht.
  apply carConfinedDuringAMsAppend in Hcon.
  repnd.
  pose proof (@atomicMoveSpaceInvertible (DAtomicMoveInv h)) as X.
  specialize (@X _ initr cd confineRect Ht).
  apply X in Hconr. clear X.
  rewrite <- negate_mult_distr_r in Ht.
  symmetry in Ht.
  rewrite RingShiftMinus in Ht.
  symmetry in Ht.
  rewrite (@commutativity _ _ _ plus _) in Ht.
  split;[|rewrite Heq; apply Hind; auto].
  clear Hconl.
  simpl stateAfterAtomicMoves in Hconr. 
  rewrite DMoveInvInvolutive in Hconr.
  apply carConfinedDuringAMsSingle in Hconr.
  pose proof (atomicMovesStateInvertibleAux tl 
      _ (stateAfterAtomicMove initr h) Ht) as X.
  apply proj1 in X. clear Ht.
  pose proof (@sg_op_proper _ _ plus  _ _ _ Heq _ _ X) as Hadd.
  clear Heq X.
  unfold sg_op in Hadd.
  ring_simplify in Hadd.
  rewrite RingShiftMinus in Hadd.
  ring_simplify in Hadd.
  symmetry in Hadd.
  rewrite (@commutativity _ _ _ plus _) in Hadd.
  rewrite <- RingShiftMinus in Hadd.
  rewrite Hadd in Hconr.
  clear Hadd.
  exact Hconr.
Qed. 

Global Instance NegateDAtomicMove
`{Zero R}
`{ApartT R} `{Equiv R} `{Negate R} : Negate (DAtomicMove R) :=
  DAtomicMoveInv.

Global Instance NegateDAtomicMoves `{Zero R}
`{ApartT R} `{Equiv R} `{Negate R} : Negate (list (DAtomicMove R)) :=
  DAtomicMovesInv.

Lemma atomicMovesSpaceInvertible :
  ∀ (m : list (DAtomicMove IR)), MovesSpaceInverse m (-m).
Proof.
  intros. unfold MovesSpaceInverse.
  intros ? ? ? ?.
  pose proof (DMovesInvInvolutive m) as H.
  rewrite <- H at 1.
  rewrite <- H at 2.
  apply atomicMovesSpaceInvertibleAux.
Qed.

Lemma atomicMovesStateInvertible :
  ∀ (m : list (DAtomicMove IR)), MovesStateInverse m (-m).
Proof.
  intros. unfold MovesStateInverse.
  intros ? ?.
  pose proof (DMovesInvInvolutive m) as H.
  rewrite <- H at 1.
  rewrite <- H at 2.
  apply atomicMovesStateInvertibleAux.
Qed.

End SpaceInvertability.

Definition mkStraightMove `{ApartT R} `{Setoid R} `{Zero R}
 (d:R): DAtomicMove R.
 exists {|am_distance :=d; am_tc :=0|}.
 simpl. left. reflexivity.
Defined.

Lemma carConfinedDuringAMsEndpoints: forall
  (cd : CarDimensions IR)
  (rect : Line2D IR) 
  (m : list (DAtomicMove IR))
  (init : Rigid2DState IR),
carConfinedDuringAMs cd rect m init
→ (carMinMaxXY cd (stateAfterAtomicMoves m init) ⊆ rect
   /\ carMinMaxXY cd init ⊆ rect).
Proof.
  unfold carConfinedDuringAMs.
  induction m; intros ? Hc;simpl in *;
    [tauto|].
  repnd.
  apply carConfinedDuringAMEndpoints in Hcl.
  split;[| tauto].
  repnd.
  apply IHm in Hcr. tauto.
Qed.

(**because the extremas w.r.t space occupation occur
at endpoints during a straight move, one can forget about it
while computing space requirements. 
This is not true for turning moves.*)
Lemma strMoveSandwichedConfined : ∀
  (damsl damsr : list (DAtomicMove IR))
  (cd : CarDimensions ℝ) (init : Rigid2DState ℝ) (d:ℝ)
  (confineRect: Line2D IR),
  let sandwich : list (DAtomicMove IR) 
    := damsl ++ [mkStraightMove d] ++ damsr in
  let stMid : Rigid2DState ℝ  
    := stateAfterAtomicMoves (damsl ++ [mkStraightMove d]) init in
 carConfinedDuringAMs cd confineRect damsl init
 -> carConfinedDuringAMs cd confineRect damsr stMid
 -> carConfinedDuringAMs cd confineRect sandwich init.
Proof.
  intros ? ? ? ? ? ?.
  simpl. intros H1c H2c.
  apply carConfinedDuringAMsAppend.
  split;[exact H1c|].
  fold ([mkStraightMove d] ++ damsr).
  rewrite carConfinedDuringAMsAppend.
  setoid_rewrite fold_left_app in H2c.
  fold stateAfterAtomicMoves in H2c.
  fold stateAfterAtomicMoves in H2c.
  split;[|exact H2c].
  apply carConfinedDuringAMsSingle.
  simpl.
  rewrite holdsDuringStAMIff.
  unfold straightAMSpaceRequirement.
  simpl.
  apply boundingUnionIff.
  apply carConfinedDuringAMsEndpoints in H1c.
  apply carConfinedDuringAMsEndpoints in H2c.
  repnd.
  split;[tauto |].
  simpl in H2cr.
  unfold stateAfterAtomicMove in H2cr.
  simpl in H2cr.
  rewrite mult_0_l, plus_0_r in H2cr. 
  rewrite displacedCarMinMaxXY in H2cr.
  exact H2cr.
Qed.  
