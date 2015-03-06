Add LoadPath "../../../nuprl/coq".
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
(** printing ω $w$ #ω# *)
(** printing eeev $\epsilon_v$ #∊ᵥ# *)
(** printing eeew $\epsilon_w$ #∊w# *)
(** printing tm $t_m$ #tm# *)
(** printing IR $\mathbb{R}$ #IR# *)
(** printing CR $\mathbb{R}$ #CR# *)
(** printing tr $t_r$ #tr# *)
(** printing θErrTurn $\theta ErrTurn$ #θErrTurn# *)
(** remove printing * *)
(** printing θErrTrans $\theta ErrTrans$ #θErrTrans# *)
Require Export Vector.
Require Export ROSCyberPhysicalSystem.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import CartCR.

Definition initialVel : (Polar2D Q) := {|rad:=0; θ:=0|}.

Require Export CartIR.

Notation FConst := ConstTContR.
Notation FSin:= CFSine.
Notation FCos:= CFCos.


Record iCreate : Type := {
  position :> Cart2D TContR;          (* x, y co-ordinates*)
  theta : TContR;                       (* orientation *)
  transVel : TContR;             (* translation vel (along [theta]) *)
  omega : TContR;

  (** derivatives *)
  derivRot : isDerivativeOf omega theta;
  derivX : isDerivativeOf (transVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (transVel * (FSin theta)) (Y position);

  (** Initial (at time:=0) Conditions *)  

  initPos:  ({X position} 0) ≡ 0 ∧ ({Y position} 0) ≡ 0;
  initTheta:  ({theta} 0) ≡ 0;
  initTransVel : ({transVel} 0) ≡ (rad initialVel);
  initOmega : ({omega} 0) ≡ (θ initialVel)
}.



(** Robot is asked to go to the  [target] relative to current position.
    This function defines the list of messages that the robot will send to
    the motor so that it will go to the target position.
    [X] axis of target points towards the direction that robot will move
    and [Y] points to its left side. it might be better to make Y
    point in robot's direction. Then add 90 in cartesian <-> polar conversion. *)

Section RobotProgam.
Variables   rotspeed speed anglePrec distPrec delay : Qpos.


Definition robotPureProgam (target : Cart2D Q) : list (Q × Polar2D Q) :=
  let polarTarget : Polar2D CR := Cart2Polar target in
  let approxTheta : Q := approximate (θ polarTarget) anglePrec in
  let rotDirection : Q := QSign approxTheta 1 in (* +1 or -1*)
  let approxDist : Q := approximate (rad polarTarget) distPrec in
  let rotDuration : Q :=  (|approxTheta|) / (QposAsQ rotspeed) in
  let translDuration : Q :=  approxDist / (QposAsQ speed) in
  [ (0,{|rad:= 0 ; θ := rotDirection*rotspeed |}) 
      ; (rotDuration, {|rad:= 0 ; θ := 0 |}) 
      ; (QposAsQ delay , {|rad:= QposAsQ speed ; θ := 0 |}) 
      ; (translDuration , {|rad:= 0 ; θ := 0 |}) 
  ].


Inductive Topic :=  VELOCITY | TARGETPOS. (* similar to CMD_VEL *)

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


(** When adding a nrew topic, add cases of this function *)
Definition topic2Type (t : Topic) : Type :=
match t with
| VELOCITY => Polar2D Q
| TARGETPOS => Cart2D Q 
end.


Instance  ttttt : @RosTopicType Topic _.
  constructor. exact topic2Type.
Defined.

Inductive RosLoc :=  MOVABLEBASE | EXTERNALCMD | SWNODE.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
  constructor. exact RosLoc_eq_dec.
Defined.

Close Scope Q_scope.


Definition getVelM  : Message -> option (Polar2D Q) :=
  getPayload VELOCITY.


Section iCREATECPS.

(** To define IO devices, we already need
    an Event type *)
Context  
  (minGap : Q)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


(** In some cases, the equations might invove transcendental 
  functions like sine, cos which can output 
  irrationals even on rational *)



Definition getVelEv (e : Event) : option (Polar2D Q)  :=
  getRecdPayload VELOCITY e.

Definition getVelOEv : (option Event) ->  option (Polar2D Q)  :=
getRecdPayloadOp VELOCITY.


Definition getVelAndTime (oev : option Event) 
    : option ((Polar2D Q) * Event)  :=
  getPayloadAndEv VELOCITY oev.


Definition inIntervalDuring
  (interval: interval) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  Squash (forall t : QTime, ( tStart <= t <= tEnd   -> (interval) (f t)))%Q.
  
Definition isEqualDuring
  (vel: Q) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  (forall t : QTime, ( tStart <= t <= tEnd   -> (f t) [=] vel))%Q.

Variable reacTime : QTime.
(** It is more sensible to change the type o [QNonNeg]
    as the value certainly does not represent time.
    However, the coercion QT2Q does not work then *)
Variable motorPrec : Polar2D Q → Polar2D QTime.

Variable motorPrec0 : motorPrec {| rad :=0 ; θ :=0 |} ≡ {| rad :=0 ; θ :=0 |}.
  
Close Scope Q_scope.


(** all velocity messages whose index  < numPrevEvts .
    the second item is the time that messsage was dequed.
    last message, if any  is the outermost (head)
    Even though just the last message is needed,
    this list is handy for reasoning; it is a convenient
    thing to do induction over
 *)

Definition velocityMessages (t : QTime) :=
  (filterPayloadsUptoTime VELOCITY (localEvts MOVABLEBASE) t).


Definition lastVelAndTime
  (evs : nat -> option Event) (t : QTime) : ((Polar2D Q) × QTime) :=
  lastPayloadAndTime VELOCITY evs t initialVel.


Instance ProjectionFst_instance_sig 
   (A : Type) (P: A → Prop):  
    ProjectionFst (sig P) A := (@projT1 A P) .

Instance ProjectionFst_instance_sigT 
   (A : Type) (P: A → Type):  
    ProjectionFst (sigT P) A := (@projT1 A P) .


Definition correctVelDuring
  (lastVelCmd : (Polar2D Q)) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (robot: iCreate) :=

  changesTo 
    (transVel robot) 
    lastTime uptoTime 
    (rad lastVelCmd) 
    reacTime 
    (rad  (motorPrec lastVelCmd))
  ∧ 
  changesTo 
    (omega robot) 
    lastTime uptoTime 
    (θ lastVelCmd) 
    reacTime 
    (θ (motorPrec lastVelCmd)).

(** TODO : second bit of conjunction is incorrect it will force the
   orientation in [iCreate] to jump from [2π] to [0] while turning.
   changes_to is based on a notion of distance or norm. we need to generalize 
    it to use the norm typeclass and then define appropriate notion for distance
    for angles*)

Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime)
  (robot: iCreate) :=
let (lastVel, lastTime) := lastVelAndTime evs uptoTime in
correctVelDuring lastVel lastTime uptoTime robot.


Definition BaseMotors  : Device iCreate :=
λ (robot: iCreate) (evs : nat -> option Event) ,
  (∀ t: QTime, corrSinceLastVel evs t robot)
  ∧ ∀ n:nat, isDeqEvtOp (evs n).

Definition onlyRecvEvts (evs : nat -> option Event) : Prop :=
∀ n:nat, isDeqEvtOp (evs n).

Definition eeev  a b : Q  :=
 (rad (motorPrec {|rad:= a; θ:= b|})).

Definition eeew  a b : Q :=
 (θ (motorPrec {|rad:= a; θ:= b|})).

Definition BaseMotorsP (ic: iCreate) (evs : nat -> option Event): Prop :=
onlyRecvEvts evs ∧ ∀ t: QTime,
  let (lastCmd, tm ) := lastVelAndTime evs t in 
  let a : Q := rad (lastCmd) in
  let b : Q := θ (lastCmd) in
  ∃ tr : QTime, (tm ≤ tr ≤ tm + reacTime)
    ∧ (∀ t' : QTime, (tm ≤ t' ≤ tr) 
        → (Min ({transVel ic} tm) (a - eeev a b) 
            ≤ {transVel ic} t' ≤ Max ({transVel ic} tm) (a+ eeev a b)))
    ∧ (∀ t' : QTime, (tr ≤ t' ≤ t) → |{transVel ic} t' - a | ≤ Q2R (eeev a b)).

Lemma BaseMotorsPCorr1 :
  ∀ icr evs,
  BaseMotors icr evs ->  BaseMotorsP icr evs.
Proof.
  intros ? ? H.
  destruct H as [Hr H].
  split; [assumption|]. clear H.
  intros t.
  specialize (Hr t).
  unfold corrSinceLastVel in Hr.
  destruct (lastVelAndTime evs t) as [lc lt].
  apply proj1 in Hr.
  destruct Hr as [qtrans Hr].
  exists qtrans.
  unfold le, Le_instance_QTime.
  autounfold with IRMC. unfold Plus_instance_QTime.
  unfoldMC. repnd.
  split; auto.
  unfold eeev.
  destruct lc.
  simpl Vector.rad.
  simpl Vector.rad in Hrrl, Hrrr.
  unfold Q2R. setoid_rewrite inj_Q_inv.
  split; auto.
  unfold between, Q2R in Hrrr.
  intros ? H.
  apply Hrrr in H.
  autorewrite with QSimpl in H.
  exact H.
Qed.

Definition PureSwProgram:
  PureProcWDelay TARGETPOS VELOCITY:=
  robotPureProgam.

Definition SwProcess 
      : Process Message (list Message):= 
  mkPureProcess (delayedLift2Mesg (PureSwProgram)).

Variable procTime : QTime.
Variable sendTimeAcc : Qpos.
Require Import CoRN.model.metric2.Qmetric.


Definition ControllerNode : RosSwNode :=
  Build_RosSwNode (SwProcess) (procTime, sendTimeAcc).


(** The software could reply back to the the external agent saying "done".
    Then the s/w will output messages to two different topics
    In that case, change the [SWNODE] claue *)
Definition locTopics (rl : RosLoc) : TopicInfo :=
match rl with
| MOVABLEBASE => ((VELOCITY::nil), nil)
| SWNODE => ((TARGETPOS::nil), (VELOCITY::nil))
| EXTERNALCMD => (nil, (TARGETPOS::nil))
end.


Variable targetPos : Cart2D Q.
Variable eCmdEv0 : Event.


(** 10 should be replaced by something which is a function of 
    velocity accuracy, angle accuracy, max velocity etc *)
Definition externalCmdSemantics {Phys : Type} 
 : @NodeSemantics Phys Event :=
  λ _ evs , ((evs 0) ≡ Some eCmdEv0) 
              ∧  isSendEvt eCmdEv0 
              ∧ (getPayload TARGETPOS (eMesg eCmdEv0) ≡ Some targetPos)
              ∧ ∀ n : nat, (evs (S n)) ≡ None.





Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| MOVABLEBASE => DeviceSemantics (λ ts,  ts) BaseMotors
| SWNODE => RSwSemantics ControllerNode
| EXTERNALCMD  => externalCmdSemantics
end.

Variable expectedDelivDelay : Qpos.
Variable delivDelayVar : Qpos.

Instance rllllfjkfhsdakfsdakh : @RosLocType iCreate Topic Event  RosLoc _.
  apply Build_RosLocType.
  - exact locNode.
  - exact locTopics.
  - exact (λ _ _ t , ball delivDelayVar t (QposAsQ expectedDelivDelay)).
Defined.

Variable acceptableDist : Q.
Variable ic : iCreate.
Variable eo : (@PossibleEventOrder _  ic minGap _ _ _ _ _ _ _ _ _).


Lemma derivXNoMC : ∀ icr, isDerivativeOf (transVel icr[*] (CFCos (theta icr))) (X (position icr)).
  exact derivX.
Qed.

Lemma derivYNoMC : ∀ icr, isDerivativeOf (transVel icr[*] (CFSine (theta icr))) (Y (position icr)).
  exact derivY.
Qed.

Definition posAtTime (t: Time) : Cart2D IR :=
  {| X:= {X (position ic)} t ; Y := {Y (position ic)} t |}.

Definition targetPosR : Cart2D IR := ' targetPos.


Require Import Coq.Lists.List.
Hint Resolve (fun a b x => proj1 (locEvtIndex a b x)) : ROSCOQ.

Ltac contra :=
  match goal with
  | [H: ~(assert true) |- _ ] => provefalse; apply H; reflexivity
  end.

(** No Change at All from the train proof.
    However, it was changed later when ROSCPS was simplified*)
Lemma SwOnlyReceivesFromExt :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Er ≡ SWNODE
  -> eLoc Es ≡ EXTERNALCMD.
Proof.
  intros ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd.
  repnd. clear Hsendlrrr.
  unfold validRecvMesg  in Hsendlrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  simpl in  XXl.
  apply (f_equal (fst)) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  rewrite Hl in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  unfold mtopic in Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  simpl in Hsendlrrl. 
  unfold mtopic in  Hsendlrl. 
  simpl in Hsendlrl, Hsendlrrl.
  rewrite <- Hsendlrl in Hsendlrrl.
  destruct (eLoc Es); simpl in Hsendlrrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

(** No Change at All from the train proof.
    However, it was changed later when ROSCPS was simplified*)
Lemma MotorOnlyReceivesFromSw :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Er ≡ MOVABLEBASE
  -> eLoc Es ≡ SWNODE.
Proof.
  intros ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd.
  repnd. clear Hsendlrrr.
  unfold validRecvMesg  in Hsendlrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  simpl in  XXl.
  apply (f_equal (fst)) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  rewrite Hl in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  unfold mtopic in Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  simpl in Hsendlrrl. 
  unfold mtopic in  Hsendlrl. 
  simpl in Hsendlrl, Hsendlrrl.
  rewrite <- Hsendlrl in Hsendlrrl.
  destruct (eLoc Es); simpl in Hsendlrrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

(** No Change at All from the train proof *)

Lemma ExCMDOnlySendsToSw :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Es ≡ EXTERNALCMD
  -> eLoc Er ≡ SWNODE.
Proof.
  intros ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrr.
  unfold validSendMesg in Hsendlrrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  apply (f_equal fst) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  simpl in Hsendlrrl, XXl. 
  unfold mtopic in Hsendlrrl. simpl in XXl, Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  rewrite Hl in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite RemoveOrFalse in Hsendlrrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl.
  simpl in Hsendlrl.
  unfold validRecvMesg, mtopic in Hsendlrl.
  simpl in Hsendlrrl, Hsendlrl.
  rewrite <- Hsendlrrl in Hsendlrl.
  destruct (eLoc Er); simpl in Hsendlrl;
    try rewrite RemoveOrFalse in Hsendlrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

Lemma SWOnlySendsToMotor :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Es ≡ SWNODE
  -> eLoc Er ≡ MOVABLEBASE.
Proof.
  intros ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrr.
  unfold validSendMesg in Hsendlrrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  apply (f_equal fst) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  simpl in Hsendlrrl, XXl. 
  unfold mtopic in Hsendlrrl. simpl in XXl, Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  rewrite Hl in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite RemoveOrFalse in Hsendlrrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl.
  simpl in Hsendlrl.
  unfold validRecvMesg, mtopic in Hsendlrl.
  simpl in Hsendlrrl, Hsendlrl.
  rewrite <- Hsendlrrl in Hsendlrl.
  destruct (eLoc Er); simpl in Hsendlrl;
    try rewrite RemoveOrFalse in Hsendlrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

Lemma SwRecv : ∀ ev:Event,
  eLoc ev ≡ SWNODE
  -> isDeqEvt ev
  -> (getPayload TARGETPOS (eMesg ev) ≡ Some targetPos
            ∧ causedBy eo eCmdEv0 ev).
Proof.
  intros ev Hl Heqevk.
  pose proof (recvSend eo ev Heqevk) as Hsend.
  destruct Hsend as [Es Hsend].
  repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
  pose proof (SwOnlyReceivesFromExt _ _  Hsendrr Heqevk Hsendl Hl) as Hex.
  pose proof (corrNodes eo EXTERNALCMD) as Hc.
  simpl in Hc. unfold externalCmdSemantics in Hc.
  repnd. remember (eLocIndex Es) as esn.
  destruct esn;
    [|specialize (Hcrrr esn);
      rewrite (locEvtIndexRW Es) in Hcrrr; eauto; inversion Hcrrr].
  clear Hcrrr.
  rewrite (locEvtIndexRW Es) in Hcl; eauto.
  inverts Hcl.
  apply proj1 in Hsendl.
  unfold getPayload.
  rewrite <- Hsendl.
  dands; assumption.
Qed.



Lemma SwLiveness : notNone (localEvts SWNODE 0).
Proof.
  pose proof (corrNodes eo EXTERNALCMD) as Hc.
  simpl in Hc. unfold externalCmdSemantics in Hc.
  repnd. 
  pose proof (eventualDelivery eo _ Hcrl) as Hsend.
  destruct Hsend as [Er  Hsend]. repnd.
  apply locEvtIndex in Hcl.
  repnd.
  apply ExCMDOnlySendsToSw in Hsendl; auto.
  remember (eLocIndex Er) as ern.
  destruct ern.
  - unfold notNone. rewrite (locEvtIndexRW Er); auto.
  - pose proof (localIndexDense _ _ _ 0 (conj Hsendl eq_refl)) as Hx.
    rewrite <- Heqern in Hx.
    clear Heqern.
    lapply Hx; [clear Hx; intro Hx |omega].
    destruct Hx as [Err ]. repnd.
    rewrite (locEvtIndexRW Err); auto.
Qed.


Open Scope nat_scope.

Lemma SwEvents0 :
  {ev | eLocIndex ev ≡ 0 ∧ eLoc ev ≡ SWNODE ∧
       (getRecdPayload TARGETPOS ev ≡ Some targetPos) 
             ∧ causedBy eo eCmdEv0 ev}.
Proof.
  unfold getRecdPayload, deqMesg. 
  pose proof SwLiveness as Hlive.
  remember (localEvts SWNODE 0) as oev.
  destruct oev as [ev |]; inversion Hlive.
  clear Hlive. exists ev.
  symmetry in Heqoev. 
  pose proof (corrNodes eo SWNODE) as Hex.
  simpl in Hex.
  apply SwFirstMessageIsNotASend with (ev0:=ev) in Hex;[|eauto 4 with ROSCOQ].
  unfold isSendEvt in Hex.
  remember (eKind ev) as evk.
  destruct evk; simpl in Hex; try contra; try tauto.
  clear Hex.
  symmetry in Heqevk. apply isDeqEvtIf in Heqevk.
  apply locEvtIndex in Heqoev. repnd.
  apply  SwRecv in Heqevk  ; auto.
Qed.
Local  Notation π₂ := snd.

(** Nice warm up proof.
    Got many mistakes in definitions corrected *)
Lemma SwEventsSn :
  let resp := PureSwProgram targetPos in
  ∀ n: nat, 
      n < 4
      → {ev : Event | eLocIndex ev ≡ S n ∧ eLoc ev ≡ SWNODE
            ∧ (isSendEvt ev) 
            ∧ Some (eMesg ev) 
               ≡ nth_error
                    (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) n
            ∧ ball sendTimeAcc
                (eTime (projT1 SwEvents0)
                     + minDelayForIndex
                         (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) 
                         n 
                     + procTime)%Q 
                (QT2Q (eTime ev))}.
Proof.
  simpl.
  destruct (SwEvents0) as [ev0 Hind]. simpl.
  repnd.
  pose proof (corrNodes eo SWNODE) as Hex.
  simpl in Hex. intros n Hlt.
  apply DelayedPureProcDeqSendPair with (nd:=0) (pl:=targetPos) (n:=n)
      in Hex; eauto;
  [|rewrite (locEvtIndexRW ev0); auto; fail].
  simpl in Hex. destruct Hex as [evs Hex]. repnd.
  exists evs.
  apply locEvtIndex in Hexl. repnd.
  rewrite (locEvtIndexRW ev0) in Hexrrr; auto.
Qed.

Lemma eCmdEv0Loc :  eLoc eCmdEv0 ≡ EXTERNALCMD.
Proof.
  pose proof (corrNodes eo EXTERNALCMD) as Hc.
  simpl in Hc. unfold externalCmdSemantics in Hc.
  repnd. apply locEvtIndex in Hcl. repnd.
  assumption.
Qed.

Lemma SwRecvDeqOnly0 : ∀ ev:Event,
  eLoc ev ≡ SWNODE
  -> isDeqEvt ev
  -> eLocIndex ev ≡ 0.
Proof.
  intros ev Hl Hd.
  apply SwRecv in Hd;[| assumption].
  repnd.
  destruct SwEvents0 as [ev0 Hev0].
  repnd. pose proof eCmdEv0Loc.
  pose proof (noDuplicateDelivery eo) as Hh.
  unfold NoDuplicateDelivery in Hh.
  eapply Hh with (evr2:=ev0) in Hdr; eauto;
    try congruence.
Qed.



Lemma SwEventsOnly5 :
  ∀ n : nat, 4 < n -> (localEvts SWNODE n) ≡ None.
Proof.
  intros n Hlt.
  remember (localEvts SWNODE n) as oevn.
  destruct oevn as [evn|]; [| reflexivity].
  provefalse.
  remember (eKind evn) as evnk.
  destruct evnk.
- pose proof (corrNodes eo SWNODE n) as Hex.
  apply fst in Hex.
  unfold isSendEvt in Hex.
  symmetry in Heqoevn. apply locEvtIndex in Heqoevn.
  rewrite  (locEvtIndexRW evn) in Hex; [| assumption].
  simpl in Hex. unfold isSendEvt in Hex.
  rewrite <- Heqevnk in Hex; auto.
  specialize (Hex eq_refl).
  destruct Hex as [nd Hex].
  destruct Hex as [si Hex].
  (* pose proof Hex as Hltt.
   apply possibleDeqSendOncePair2_index in Hltt. *)
  unfold possibleDeqSendOncePair2 in Hex.
  remember (localEvts SWNODE nd) as oed.
  destruct oed as [ed |];[| contradiction].
  apply locEvtIndex in Heqoevn.
  rewrite Heqoevn in Hex.
  remember (eKind ed) as edk.
  destruct edk;[contradiction|].
  rewrite <- Heqevnk in Hex.
  symmetry in Heqedk. apply isDeqEvtIf in Heqedk.
  symmetry in Heqoed. apply locEvtIndex in Heqoed.
  apply SwRecvDeqOnly0 in Heqedk; [|tauto].
  repnd. rewrite Heqoedr in Heqedk. subst.
  rewrite Heqedk in Heqoevn.
  rewrite Heqedk in Hlt.
  remember (startIndex inf) as si.
  assert (si≡4+(si-4))%nat as H3s by omega.
  rewrite H3s in Hexrrl.
  simpl in Hexrrl.
  unfold procOutMsgs, ControllerNode, SwProcess  in Hexrrl.
  simpl in Hexrrl.
  rewrite getNewProcLPure in Hexrrl.
  unfold delayedLift2Mesg, PureSwProgram in Hexrrl.
  simpl in Hexrrl. rewrite (locEvtIndexRW ed) in Hexrrl; auto.
  destruct (getPayload TARGETPOS (eMesg ed)); simpl in Hexrrl;
    try discriminate.
  rewrite  nth_error_nil in Hexrrl; discriminate.
  
- symmetry in Heqevnk. apply isDeqEvtIf in Heqevnk.
  symmetry in  Heqoevn. apply locEvtIndex in Heqoevn.
  repnd.  apply SwRecvDeqOnly0 in Heqevnk; auto.
  omega.
Qed.

Definition SwRecvEventsNth (n:nat) (p :  n < 4) : Event.
  apply SwEventsSn in p.
  exact (projT1 p).
Defined.


Notation "{ a , b : T | P }" :=
  {a : T | {b : T | P} }
    (at level 0, a at level 99, b at level 99).

Lemma SwMotorPrevSend : ∀ Es Er ern,
  ern < eLocIndex Er
  → causedBy eo Es Er
  → eLoc Er ≡ MOVABLEBASE
  → eLoc Es ≡ SWNODE 
  → isSendEvt Es 
  → isRecvEvt Er 
  → {Erp, Esp: Event |  eLoc Erp ≡ MOVABLEBASE 
                          ∧ eLoc Esp ≡ SWNODE 
                          ∧ isSendEvt Esp 
                          ∧ isRecvEvt Erp
                          ∧ eLocIndex Esp < eLocIndex Es
                          ∧ eLocIndex Erp ≡ ern
                          ∧ causedBy eo Esp Erp}.
Proof.
  intros ? ? ? Hlt Hsendrl Hmot Hswsrl Hswsrrl Hsendrr.
  pose proof Hlt as Hltb.
  eapply localIndexDense in Hlt; eauto.
  destruct Hlt as [Erp  Hevp]. exists Erp.
  pose proof (corrNodes eo MOVABLEBASE) as Hb.
  simpl in Hb. apply proj2 in Hb.
  specialize (Hb ern).
  rewrite (locEvtIndexRW Erp) in Hb; [| assumption].
  simpl in Hb.
  pose proof (recvSend eo Erp Hb) as Hsend.
  destruct Hsend as [Esp Hsend]. exists Esp.
  repnd. apply MotorOnlyReceivesFromSw in Hsendl; eauto.
  assert (eLocIndex Erp < eLocIndex Er) as Hlt by omega.
  eapply orderRespectingDeliveryRS with (evs1:=Esp) (evs2:=Es) in Hlt; eauto;
  try congruence. dands; auto.
Qed.

Lemma SwEv0IsNotASend: ∀ Esp,
    eLocIndex Esp ≡ 0 
    → (eLoc Esp ≡ SWNODE)
    → ~ (isSendEvt Esp).
Proof.
  intros ? Hs0 Hltrl.
  destruct SwEvents0 as [Esp' H0s]. repnd.
  assert (Esp ≡ Esp') by
    (eapply indexDistinct; eauto; try congruence).
  subst. pose proof (getRecdPayloadSpecDeq TARGETPOS) as Hpp.
  simpl in Hpp. apply Hpp in H0srrl.
  apply DeqNotSend in H0srrl. assumption.
Qed.


Lemma MotorEventsCausal:
  ∀ (n: nat) (p:n < 4),
      {Er : Event | let Es := (SwRecvEventsNth n p) in
              PossibleSendRecvPair Es Er 
              ∧ causedBy eo Es Er 
              ∧ isRecvEvt Er
              ∧ eLoc Er ≡ MOVABLEBASE
              ∧  eLocIndex Er ≡ n }.
Proof.
  induction n  as [n Hind] using comp_ind_type. intros p.
  destruct n as [| n'].
- unfold SwRecvEventsNth.
  destruct (SwEventsSn 0 p) as [Es Hsws]. simpl. 
  repnd. clear Hswsrrrr Hswsrrrl.
  pose proof (eventualDelivery eo _ Hswsrrl) as Hsend.
  destruct Hsend as [Er  Hsend]. repnd. exists Er.
  pose proof  Hsendl as Hmot.
  eapply SWOnlySendsToMotor in Hmot; eauto.
  repeat(split;[assumption|]).
  remember (eLocIndex Er) as ern.
  destruct ern; [reflexivity| provefalse].
  assert (ern < eLocIndex Er) as Hlt by omega.
  apply SwMotorPrevSend with (Es:=Es) in Hlt; try assumption.
  destruct Hlt as [Erp Hlt].
  destruct Hlt as [Esp Hlt]. repnd.
  rewrite Hswsl in Hltrrrrl.
  assert (eLocIndex Esp ≡ 0) as Hs0 by omega.
  apply SwEv0IsNotASend in Hs0; auto.

- unfold SwRecvEventsNth.
  destruct (SwEventsSn _ p) as [Es Hsws]. simpl. 
  repnd. clear Hswsrrrr Hswsrrrl.
  pose proof (eventualDelivery eo _ Hswsrrl) as Hsend.
  destruct Hsend as [Er  Hsend]. repnd. exists Er.
  pose proof  Hsendl as Hmot.
  eapply SWOnlySendsToMotor in Hmot; eauto.
  repeat(split;[assumption|]).
  pose proof (lt_eq_lt_dec (eLocIndex Er) (S n')) as Htric.
  destruct Htric as[Htric| Htric];
    [ destruct Htric as[Htric| Htric]|]; [|assumption|]; provefalse.
  + assert (eLocIndex Er  < 4) as Hpp by omega.
    (** we show that a message of index [eLocIndex Er] was already
        received due to a previous send *)
    specialize (Hind _ Htric  Hpp). unfold SwRecvEventsNth in Hind.
    destruct (SwEventsSn _ Hpp) as [Esp Hsws].
    simpl in Hind.
    repnd. clear Hswsrrrr Hswsrrrl.
    destruct Hind as [Erp Hind].
    repnd. apply indexDistinct in Hindrrrr; try congruence.
    subst. 
    assert (eLocIndex Esp <eLocIndex Es) as Hlt by omega.
    eapply orderRespectingDeliverySR with (evr1:=Er) (evr2:=Er) in Hlt; eauto;
    try congruence. omega.
  + apply SwMotorPrevSend with (Es:=Es) in Htric; try assumption.
    destruct Htric as [Erp Hlt].
    destruct Hlt as [Esp Hlt]. repnd.
    rewrite Hswsl in Hltrrrrl.
    remember (eLocIndex Esp) as esn.
    symmetry in Heqesn.
    destruct esn; 
      [apply SwEv0IsNotASend in Heqesn; tauto |].
    apply NPeano.Nat.succ_lt_mono in Hltrrrrl.
    assert (esn  < 4) as Hpp by omega.
    specialize (Hind _ Hltrrrrl  Hpp). unfold SwRecvEventsNth in Hind.
    destruct (SwEventsSn _ Hpp) as [Esp' Hsws].
    simpl in Hind.
    repnd. clear Hswsrrrr Hswsrrrl.
    assert (Esp' ≡ Esp) by
      (eapply indexDistinct; eauto; try congruence).
    subst.
    destruct Hind as [Erpp Hind].
    repnd.
    pose proof (noDuplicateDelivery eo) as Hh.
    unfold NoDuplicateDelivery in Hh.
    eapply Hh with (evr2:=Erp) in Hindrl; eauto;
    try congruence. clear dependent Esp.
    subst. omega.
Qed.


Require Import Psatz.


(** change message semantics so that message receipt 
    is at a ball near ed + deliveryTime.
    make the balls size be a parameter *)
Lemma MotorEvents:
  let resp := PureSwProgram targetPos in
  ∀ n: nat, 
      n < 4
      → {ev : Event | (isRecvEvt ev)  ∧ eLoc ev ≡ MOVABLEBASE
            ∧ eLocIndex ev ≡ n
            ∧ Some (π₁ (eMesg ev))
               ≡ nth_error
                    (map (λ p, existT topicType VELOCITY (π₂ p)) resp) n
            ∧ ball (sendTimeAcc+delivDelayVar)
                ( eTime (projT1 SwEvents0) + expectedDelivDelay
                     + minDelayForIndex
                         (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) 
                         n 
                     + procTime)%Q 
                (QT2Q (eTime ev)) }.
Proof.
  intros ? n Hlt.
  pose proof (MotorEventsCausal n Hlt) as Hsws.
  destruct Hsws as [Er Hsws]. repnd. exists Er.
  simpl in Hsws. repnd.
  repeat(split;[trivial|];[]).
  clear Hswsrrrr Hswsrrrl Hswsrrl Hswsrl.
  unfold PossibleSendRecvPair in Hswsl.
  rename Hswsl into H.
  repnd. clear Hrrl Hrl. simpl in Hrrr.
  unfold SwRecvEventsNth in Hrrr, Hl.
  destruct (SwEventsSn _ Hlt) as [Es Hes].
  simpl in Hrrr, Hl. repnd. clear Hesrrl Hesrl Hesl.
  subst resp. simpl. unfold π₁, ProjectionFst_instance_prod.
  simpl.
  rewrite <- Hl.
  rename Hesrrrl into Hm.
  simpl in Hm.
  apply (f_equal (option_map π₁)) in Hm.
  simpl in Hm.
  rewrite nth_error_map in Hm.
  simpl in Hm.
  dands; [assumption|].
  clear Hm. rename Hesrrrr into Ht.
  unfold π₁, ProjectionFst_instance_prod in Ht.
  simpl in Ht. simpl.
  match type of Ht with
  context [Qball _ (?l + ?sd + _) _] => 
    remember l as est;
    remember sd as sdt
  end.
  clear Heqsdt Heqest.
  revert Ht Hrrr. clear.
  repeat (rewrite Qball_Qabs).
  intros H1q H2q.
  remember (QT2Q (eTime Er)) as Ert.
  remember (QT2Q (eTime Es)) as Est.
  clear HeqErt HeqEst.
  apply Q.Qabs_diff_Qle in H1q.
  apply Q.Qabs_diff_Qle in H2q.
  apply Q.Qabs_diff_Qle.
  destruct sendTimeAcc as [tAcc ?].
  destruct expectedDelivDelay  as [expD ?].
  destruct delivDelayVar   as [maxVar ?].
  simpl.
  simpl in H2q, H1q.
  split; lra.
Qed.
  
Lemma MotorEventsOnly4 :
  ∀ n : nat, 3 < n -> (localEvts MOVABLEBASE n) ≡ None.
Abort.

Close Scope nat_scope.


Hint Resolve derivRot  derivX derivY initPos initTheta initTransVel initOmega
    derivXNoMC derivYNoMC : ICR.
Hint Resolve qtimePos : ROSCOQ.


Open Scope nat_scope.


Lemma MotorEvents2:
  let resp := PureSwProgram targetPos in
  ∀ n: nat, 
      (n < 4)
      → {ev : Event |  
           (isRecvEvt ev)  ∧ eLoc ev ≡ MOVABLEBASE
            ∧ eLocIndex ev ≡ n
            ∧  getPayloadAndEv VELOCITY (Some ev)  
                ≡ opBind (λ pl, Some (π₂ pl, ev))
                       (nth_error resp n)
            ∧ ball (sendTimeAcc+delivDelayVar)
                ( eTime (projT1 SwEvents0) + expectedDelivDelay
                     + minDelayForIndex
                         (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) 
                         n 
                     + procTime)%Q 
                (QT2Q (eTime ev)) }.
Proof.
  simpl. intros n Hp.
  apply MotorEvents in Hp.
  destruct Hp as [ev Hp].
  exists ev.
  repnd.
  dands; auto;[].
  revert Hprrrl Hpl.
  clear.
  intros Hc Hpl.
  unfold getRecdPayload.
  rewrite deqSingleMessage3;[| assumption].
  rewrite <- nth_error_map in Hc.
  simpl in Hc.
  match goal with
  [|- context[@nth_error ?T ?l ?n]] => destruct (@nth_error T l n); inverts Hc as Hc
  end.
  autounfold with π₁ in Hc.
  rewrite moveMapInsideSome.
  simpl. rewrite Hc.
  reflexivity.
Qed.

Definition MotorEventsNth (n:nat) (p :  n < 4) : Event.
  apply MotorEvents2 in p.
  exact (projT1 p).
Defined.


Definition MotorEventsNthTime (n:nat) (p :  n < 4) : QTime :=
  (eTime (MotorEventsNth n p)).

(** only the fly proof construction for closed (transparently) 
     decidable propositions.
   For example, (decAuto (2<4) I) is a of type (2<4) *)


Definition  mt0 : QTime 
  := MotorEventsNthTime 0 (decAuto (0<4)%nat I).

Definition  mt1 : QTime 
  := MotorEventsNthTime 1 (decAuto (1<4)%nat I).

Definition  mt2 : QTime 
  := MotorEventsNthTime 2 (decAuto (2<4)%nat I).

Definition  mt3 : QTime 
  := MotorEventsNthTime 3 (decAuto (3<4)%nat I).

Lemma MotorEventsNthTimeInc:
  ∀ (n1 n2 : nat) p1 p2,
  (n1 < n2)%nat
   -> MotorEventsNthTime n1 p1 
      ≤ MotorEventsNthTime n2 p2.
Proof.
  unfold MotorEventsNthTime, MotorEventsNth.
  intros.
  destruct (MotorEvents2 n1 p1) as [ev1  H1e].
  destruct (MotorEvents2 n2 p2)  as [ev2  H2e].
  simpl. repnd.
  apply Qlt_le_weak.
  apply timeIndexConsistent.
  congruence.
Qed.

Lemma MotorEventsNthTimeIncSn:
  ∀ (n : nat) p1 p2,
   (MotorEventsNthTime n p1 
      <= MotorEventsNthTime (S n) p2)%Q.
Proof.
  intros.
  apply MotorEventsNthTimeInc.
  auto.
Qed.

Lemma EautoTimeICR0 :  (mt0 <= mt1)%Q.
  apply MotorEventsNthTimeIncSn.
Qed.

Lemma EautoTimeICR1 :  (mt1 <= mt2)%Q.
  apply MotorEventsNthTimeIncSn.
Qed.

Lemma EautoTimeICR2 :  (mt2 <= mt3)%Q.
  apply MotorEventsNthTimeIncSn.
Qed.

Close Scope nat_scope.

(** Also, this is the way 0 is defined for CR *)

Instance Zero_Instace_IR_better : Zero IR := inj_Q IR 0.
Hint Unfold Zero_Instace_IR_better : IRMC.

Lemma correctVelTill0:
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
    correctVelDuring initialVel (mkQTime 0 I) t0 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, BaseMotors in Hc.
  apply proj1 in Hc.
  (** lets go one by one starting from the first message *)

  unfold MotorEventsNthTime, MotorEventsNth in t0.
  destruct (MotorEvents2 0 (decAuto (0<4)%nat I)) as [evStartTurn  H0m].
  simpl in t0.
  unfold minDelayForIndex, roscore.delay, Basics.compose in H0m.
  Local Opaque getPayloadAndEv.
  simpl in H0m.
  unfold corrSinceLastVel in Hc.
  unfold lastVelAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
  specialize (Hc (eTime evStartTurn)).
  repnd.
  rewrite numPrevEvtsEtime in Hc;[|assumption].
  rewrite H0mrrl in Hc.
  simpl in Hc. auto.
Qed.
  
Lemma OmegaThetaAtEV0 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  ∀ (t : QTime),  t ≤ t0
      → ({omega ic} t = 0 ∧ {theta ic} t = {theta ic} 0).
Proof.
  intros ? ? Hle.
  unfold zero, Zero_instance_IR, Zero_instance_Time.
  unfold equiv, Zero_Instace_IR_better.
  unfold le, Le_instance_QTime in Hle.
  pose proof (qtimePos t) as Hq.
  apply changesToDeriv0Comb with 
    (uptoTime := t0)
    (reactionTime:=reacTime); eauto with ICR; try (simpl;lra);
    [|rewrite initOmega; reflexivity].
    
  pose proof correctVelTill0 as Hc.
  simpl in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc.
  unfold initialVel in Hc.
  rewrite motorPrec0 in Hc.
  exact Hc.
Qed.

  
Lemma IR_mult_zero_left : ∀ (x : IR), 0[*]x[=]0.
  intros x.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  apply cring_mult_zero_op.
Qed.

  
Lemma TransVelPosAtEV0 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  ∀ (t : QTime),  t ≤ t0
      → ({transVel ic} t = 0 ∧ (posAtTime t) = (posAtTime 0)).
Proof.
  intros ? ? Hle.
  unfold zero, Zero_instance_IR, Zero_instance_Time.
  unfold equiv, Zero_Instace_IR_better, EquivCart.
  unfold le, Le_instance_QTime in Hle.
  pose proof (qtimePos t0) as Hq.
  pose proof correctVelTill0 as Hc.
  simpl in Hc. fold t0 in Hc.
  unfold correctVelDuring in Hc.
  apply proj1 in Hc.
  unfold initialVel in Hc.
  rewrite motorPrec0 in Hc. 
  Local Opaque Q2R.
  simpl in Hc.
  pose proof (qtimePos t) as Hqt.
  pose proof (λ ww, changesToDeriv0Deriv _ _ _ _  ww Hc) as Hd0.
  simpl QT2Q in Hd0.
  rewrite initTransVel in Hd0.
  specialize (Hd0 Hq).
  DestImp Hd0;[|reflexivity].
  split; [auto|].
  unfold posAtTime.
Local Opaque getF mkQTime.
  simpl.
  split.
Local Transparent mkQTime.
- apply TDerivativeEqQ0 with 
    (F':=(transVel ic[*]CFCos (theta ic)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite IContRMultAp, Hd0; [| lra].
  rewrite IR_mult_zero_left.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero. reflexivity.

- apply TDerivativeEqQ0 with 
    (F':=(transVel ic[*]CFSine (theta ic)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite IContRMultAp, Hd0; [| lra].
  rewrite IR_mult_zero_left.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero. reflexivity.
Qed.


Lemma correctVel0to1:
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
  let requestedVel : Polar2D Q :=
    {|
       rad := 0;
       θ := QSign (approximate (polarTheta targetPos) anglePrec) 1
            * rotspeed |} in
  correctVelDuring requestedVel t0 t1 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, BaseMotors in Hc.
  apply proj1 in Hc.
  (** lets go one by one starting from the first message *)

  unfold MotorEventsNthTime, MotorEventsNth in t0, t1.
  destruct (MotorEvents2 0 (decAuto (0<4)%nat I)) as [evStartTurn  H0m].
  simpl in t0.
  destruct (MotorEvents2 1 (decAuto (1<4)%nat I)) as [evStopTurn  H1m].
  simpl in t1.
  unfold minDelayForIndex, roscore.delay, Basics.compose in H1m.
  Local Opaque getPayloadAndEv.
  autounfold with π₁ in H1m.
  simpl in H1m.
  unfold corrSinceLastVel in Hc.
  unfold lastVelAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
  specialize (Hc (eTime evStopTurn)). simpl in Hc.
  repnd.
  rewrite numPrevEvtsEtime in Hc;[|assumption].
  rewrite H1mrrl in Hc.
  simpl in Hc.
  rewrite (locEvtIndexRW evStartTurn) in Hc;[|tauto].
  rewrite H0mrrrl in Hc.
  simpl in Hc.
  auto.
Qed.
  

Definition optimalTurnAngle : IR :=
  CRasIR (polarTheta targetPos).

Definition idealDirection : IR :=
  CRasIR (θ (Cart2Polar targetPos)).

Lemma IR_inv_Qzero:
    ∀ (x : IR), x[-]0[=]x.
Proof.
  intros.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  apply  cg_inv_zero.
Qed.
  
Local Transparent Q2R.

Open Scope nat_scope.

Lemma minDelayForIndexConseq : ∀ {tp : Topic}
   (n:nat) (resp : list (Q ** topicType VELOCITY)),
    S n < length resp
    -> 
    let msgs := (map (λ p0 : Q ** topicType VELOCITY, mkDelayedMesg (fst p0) (π₂ p0))
       resp) in
      nth (S n) (map fst resp) 0
      = (minDelayForIndex msgs (S n) - minDelayForIndex msgs n)%Q.
Proof.
  unfold minDelayForIndex, roscore.delay, Basics.compose.
  induction n; simpl; intros ? H1l.
- destruct resp as [|r1 resp]; simpl in H1l; try omega.
  simpl.
  destruct resp as [|r2 resp]; simpl in H1l; try omega.
  simpl. unfold inject_Z. ring_simplify. reflexivity.
- destruct resp as [|r1 resp]; simpl in H1l; try omega.
  simpl. rewrite IHn;[| simpl; omega].
  destruct resp as [|r2 resp]; simpl in H1l; try omega.
  simpl. unfold equiv, stdlib_rationals.Q_eq.
  unfoldMC. lra.
Qed.

Lemma MotorEvGap : ∀ (n:nat) (p : n < 4) (ps : S n < 4),
  let t0 : QTime := MotorEventsNthTime n p in
  let t1 : QTime := MotorEventsNthTime (S n) ps in
  let resp := PureSwProgram targetPos in
  let tgap :Q := nth (S n) (map fst resp) 0 in 
   |(QT2Q t1 - QT2Q t0 -  tgap)%Q| 
  ≤ (2 * (sendTimeAcc + delivDelayVar))%Q.
Proof.
  intros ? ? ? ? ? ? ?.
  unfold MotorEventsNthTime, MotorEventsNth in t0, t1.
  destruct (MotorEvents2 n p) as [evStartTurn  H0m].
  simpl in t0.
  destruct (MotorEvents2 (S n) ps) as [evStopTurn  H1m].
  simpl in t1.
  repeat (apply proj2 in H1m).
  repeat (apply proj2 in H0m).
  autounfold with π₁ in H0m, H1m.
  remember (map (λ p : Q ** topicType VELOCITY, mkDelayedMesg (fst p) (π₂ p))
              (PureSwProgram targetPos)) as ddd.
  unfold cast, nonneg_semiring_elements.NonNeg_inject in tgap.
  remember tgap as tdiff.
  subst tgap.
  apply Qball_opp in H0m.
  pose proof (Qball_plus H0m H1m) as Hs.
  clear H0m H1m.
  ring_simplify in Hs.
  apply Qball_Qabs in Hs.
  rewrite Qabs.Qabs_Qminus in Hs.
  fold t0 in Hs.
  fold t1 in Hs.
  ring_simplify in Hs.
  unfoldMC.
  match goal with
  [H: (_ <= ?r)%Q |- (_ <= ?rr)%Q] => 
    assert (r == rr)%Q as Hrw by (simpl; ring)
   end.
  rewrite Hrw in Hs. clear Hrw.
  eapply Qle_trans; [| apply Hs].
  apply QeqQle.
  unfold CanonicalNotations.norm, NormSpace_instance_Q.
  apply Qabs.Qabs_wd.
  subst ddd tdiff.
  rewrite  (@minDelayForIndexConseq VELOCITY) ; auto.
  simpl.
  ring.
Qed.


Close Scope nat_scope.

Lemma MotorEv01Gap :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
  let tgap :Q := ((|approximate (polarTheta targetPos) anglePrec|)
                * (Qinv rotspeed)) in
   |QT2Q t1 - QT2Q t0 -  tgap| 
  ≤ 2 * (sendTimeAcc + delivDelayVar)%Q.
Proof.
  intros ? ? ?.
  apply MotorEvGap.
Qed.

Definition qthetaAbs : Q := 
  (|approximate (polarTheta targetPos) anglePrec |).

Definition E2EDelVar : Q := 
  (2 * (sendTimeAcc + delivDelayVar))%Q.


Lemma  QabsNewOmega : 
      (Qabs.Qabs
          (QSign (approximate (polarTheta targetPos) anglePrec) 1 * rotspeed)%mc 
        ==
        rotspeed)%Q.
Proof.
  unfold mult, stdlib_rationals.Q_mult.
  rewrite Qabs.Qabs_Qmult.
  rewrite QAbsQSign.
  unfold CanonicalNotations.norm, NormSpace_instance_Q.
  simpl Qabs.Qabs.
  ring_simplify.
  rewrite QabsQpos.
  reflexivity.
Qed.

Lemma  AbsIRNewOmega : 
      AbsIR
          (QSign (approximate (polarTheta targetPos) anglePrec) 1 * rotspeed)%mc [=]
        rotspeed.
Proof.
  rewrite AbsIR_Qabs, QabsNewOmega.
  reflexivity.
Qed.


Definition ω :=  QSign (approximate (polarTheta targetPos) anglePrec) 1
            * rotspeed.
  

Lemma MotorEv01Gap2 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
    (Qabs.Qabs
        ((t1 - t0) * ω -
         approximate (polarTheta targetPos) anglePrec) <=
      (2) * (sendTimeAcc + delivDelayVar) * rotspeed)%Q.

  intros ? ?. unfold ω.
  pose proof MotorEv01Gap as Hg.
  simpl in Hg.
  fold t0 t1 in Hg.
  apply Qmult_le_compat_r with (z:= Qabs.Qabs ω) in Hg;
      [|apply Qabs.Qabs_nonneg].
  rewrite <- Qabs.Qabs_Qmult in Hg. idtac.
  revert Hg.
  unfoldMC.
  intros Hg.
  rewrite foldQminus in Hg.
  rewrite  QmultOverQminusR in Hg.
  rewrite foldQminus in Hg.
  unfold CanonicalNotations.norm, NormSpace_instance_Q in Hg.
  revert Hg.
  unfoldMC.
  intros Hg.
  rewrite QAbsMultSign in Hg.
  rewrite QabsNewOmega in Hg.
  exact Hg.
Qed.


(** This could be made an assumption of the motor spec.
  One will have to prove this and only then
  they can assume correct behaviour of motor.
    In this case, it should be provable becuase
  the external thing sends only 1 event.

  Lateron, we can assume that the external thing
  has to wait until they receive an acknowledgement
 *)
Lemma MotorEventsNthTimeReac:
  ∀ (n1 n2 : nat) p1 p2,
  (n1 < n2)%nat
   -> MotorEventsNthTime n1 p1 + reacTime
      < MotorEventsNthTime n2 p2.
Admitted.

Definition motorTurnOmegaPrec (ω : Q) : QTime := θ (motorPrec {| rad :=(0%Q) ; θ := ω |}).

Lemma ThetaAtEV1 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
     |{theta ic} t1 - optimalTurnAngle| ≤ 
          Q2R (rotspeed * (2 * (sendTimeAcc + delivDelayVar) + reacTime) +
               anglePrec + (motorTurnOmegaPrec ω) * (t1 - t0))%Q.
Proof.
  intros ? ?.
  pose proof correctVel0to1 as Hc.
  simpl in Hc. fold t0 in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc. simpl θ in Hc.
  fold t1 in Hc. fold (ω) in Hc.
  match type of Hc with
  context[changesTo _ _ _ (Q2R ?nv) _ (QT2Q ?om)]
    => remember om as opr
  end.
  assert ((t0 + reacTime < t1)%Q) 
    as Hassumption by (apply MotorEventsNthTimeReac; omega).
  pose proof (qtimePos reacTime) as H99.
  pose proof (OmegaThetaAtEV0 t0 QTimeLeRefl) as Ht0.
  repnd.
  apply changesToDerivInteg2
    with (F:=(theta ic)) (oldVal:=0) in Hc;
    eauto with ICR.
  clear H99.
  rewrite initTheta in Ht0r.
  rewrite Ht0r in Hc.
  rewrite Ht0l in Hc.
  rewrite  (AbsIR_minus 0)  in Hc .
  rewrite cg_inv_zero in Hc.
  rewrite IR_inv_Qzero in Hc.
  rewrite AbsIRNewOmega in Hc.
  pose proof MotorEv01Gap2 as Hg.
  Local Opaque Qabs.Qabs.
  simpl in Hg.
  fold t0 t1 in Hg.
  apply (inj_Q_leEq IR) in Hg.
  rewrite <- AbsIR_Qabs in Hg.
  rewrite inj_Q_minus in Hg.
  rewrite <- inj_Q_mult in Hc.
  Local Opaque Qmult AbsIR.
  simpl in Hc.
  rewrite Qmult_comm in Hc.
  apply AbsIR_imp_AbsSmall in Hg.
  apply AbsIR_imp_AbsSmall in Hc.
  pose proof (AbsSmall_plus _ _ _ _ _ Hc Hg) as Hadd.
  fold (ω) in Hadd.

  unfold Q2R in Hadd. ring_simplify in Hadd.
  unfold cg_minus in Hadd. ring_simplify in Hadd.
  clear Hg Hc.
  revert Hadd.
  unfoldMC. intro Hadd. unfold QT2R in Hadd.
  unfold Q2R in Hadd.
  Local Opaque inj_Q.
  autorewrite with QSimpl in Hadd. simpl in Hadd.
  match type of Hadd with 
  AbsSmall (inj_Q _ ?r%Q) _ => assert (r == rotspeed * (2 * (sendTimeAcc + delivDelayVar) + reacTime) + opr * (t1 - t0))%Q
                                    as Heqq by (unfoldMC ;ring); rewrite Heqq in Hadd; clear Heqq
  end.
  pose proof (approximateAbsSmallIR (polarTheta targetPos) anglePrec) as Hball.
  apply AbsSmall_minus in Hball.
  pose proof (AbsSmall_plus _ _ _ _ _  Hadd Hball) as Haddd.
  clear Hball Hadd. rename Haddd into Hadd.
  fold (optimalTurnAngle) in Hadd.
  unfold Q2R, cg_minus in Hadd.
  ring_simplify in Hadd. 
  rewrite <- inj_Q_plus in Hadd.
  subst opr.
  unfold Le_instance_IR.
  simpl in Hadd.
  apply AbsSmall_imp_AbsIR in Hadd.
  eapply leEq_transitive;[apply Hadd|].
  apply eqImpliesLeEq.
  apply inj_Q_wd.
  simpl. unfoldMC.
  fold (motorTurnOmegaPrec ω). ring.
Qed.

Require Export Coq.QArith.Qabs.

Lemma MotorEv01Gap3 :
   AbsIR ((Q2R (QT2Q mt1 - QT2Q mt0)) 
      - ((CRasIR (CRabs (polarTheta targetPos))) * (Qinv rotspeed)))
  [<=] Q2R ((anglePrec* (Qinv rotspeed)) + 2 * (sendTimeAcc + delivDelayVar)).
Proof.
  pose proof  MotorEv01Gap  as Hg.
  fold mt0 mt1 in Hg.
  simpl in Hg.
  apply (inj_Q_leEq IR) in Hg.
  rewrite <- AbsIR_Qabs in Hg.
  rewrite cgminus_Qminus, inj_Q_minus in Hg.
  pose proof (approximateAbsSmallIR 
      (CRabs (polarTheta targetPos)) anglePrec) as Hball.
  rewrite approximate_CRabs in Hball.
  apply AbsSmall_minus in Hball.
  apply mult_resp_AbsSmallR with (y:= Q2R (Qinv rotspeed)) in Hball;
    [| apply QposDivLe0IR].
  rewrite  IRDistMinus in Hball.
  autorewrite with QSimpl in Hball.
Local Opaque CRabs.
  simpl in Hball.
  apply AbsIR_imp_AbsSmall in Hg.
  pose proof (AbsSmall_plus _ _ _ _ _  Hg Hball) as Hadd.
  clear Hball Hg.
  unfold Q2R, cg_minus in Hadd.
  simpl in Hadd. revert Hadd.
  unfoldMC. intro Hadd.
  unfold CanonicalNotations.norm, NormSpace_instance_Q in Hadd.
  ring_simplify in Hadd.
  autounfold with IRMC.
  apply AbsSmall_imp_AbsIR.
  autorewrite with QSimpl in Hadd.
  unfold Mult_instance_IR.
  eapply AbsSmall_morph_wd;
    [| | apply Hadd].
- apply inj_Q_wd. simpl. ring.
- unfold Q2R, Qminus, cg_minus. reflexivity.
Qed.

Definition Ev01TimeGapUB : IR :=
  ((CRasIR (CRabs (polarTheta targetPos)) + anglePrec) * (Qinv rotspeed))
  + E2EDelVar.

Lemma MotorEv01Gap4 :
   Q2R (QT2Q mt1 - QT2Q mt0) ≤ Ev01TimeGapUB.
Proof.
  pose proof MotorEv01Gap3 as Hp.
  Local Opaque Q2R.
  simpl in Hp.
  apply AbsIR_imp_AbsSmall in Hp.
  unfold AbsSmall in Hp.
  apply proj2 in Hp.
  apply shift_leEq_plus in Hp.
  unfold Ev01TimeGapUB.
  eapply leEq_transitive;[apply Hp|].
  clear Hp.
  unfold E2EDelVar.
  unfoldMC.
  autounfold with IRMC.
  unfold Mult_instance_IR.
  rewrite ring_distl_unfolded.
  simpl. idtac. destruct sendTimeAcc, delivDelayVar.
  simpl. apply eqImpliesLeEq.
  simpl.  
  autorewrite with QSimpl. simpl.
  Local Transparent Q2R.
  unfold Q2R. 
  rewrite inj_Q_plus.
  ring.
Qed.

Hint Resolve qtimePosIR : ROQCOQ.
Lemma ThetaAtEV1_2 :
     (|{theta ic} mt1 - optimalTurnAngle|) ≤ 
          Q2R (rotspeed * (2 * (sendTimeAcc + delivDelayVar) + reacTime) +
               anglePrec)%Q + (Q2R (motorTurnOmegaPrec ω) * Ev01TimeGapUB).
Proof.
  intros. pose proof ThetaAtEV1 as Hom.
  Local Opaque Qabs.Qabs Q2R.
  simpl in Hom.
  Local Transparent Q2R.
  fold mt0 mt1 in Hom.
  eapply leEq_transitive;[apply Hom|].
  unfold Q2R. unfoldMC.
  rewrite inj_Q_plus. 
  apply plus_resp_leEq_lft.
  rewrite inj_Q_mult. 
  apply mult_resp_leEq_lft;[| apply qtimePosIR].
  apply MotorEv01Gap4.
Qed.
  
(** rearrange the above to show relation to rotspeed 
    first line of errors is proportional to rotspeed
    second is independent,
    third is inversly proportional.
 *)

Lemma ThetaAtEV1_3 :
  let omPrec : Q :=  (eeew 0%Q ω) in 
 |{theta ic} mt1 - optimalTurnAngle| ≤ 
   Q2R(rotspeed * (E2EDelVar + reacTime) 
    + anglePrec + omPrec * E2EDelVar)
    + Q2R (omPrec / rotspeed)%Q * ('(CRabs (polarTheta targetPos)) + Q2R anglePrec).
Proof.
  Local Opaque Q2R.
  simpl.
  pose proof ThetaAtEV1_2 as Hev.
  simpl in Hev.
  eapply leEq_transitive;[apply Hev|].
  apply eq_imp_leEq.
  unfold Ev01TimeGapUB.
  fold E2EDelVar.
  unfold eeew, motorTurnOmegaPrec.
  remember (θ (motorPrec {| rad := 0%Q; θ := ω |}) ) as ew.
  unfold cast, Cart_CR_IR.
  remember (CRasIR (CRabs (polarTheta targetPos))) as crabs.
  unfoldMC.
  autounfold with IRMC.
  autorewrite with QSimpl.
  Local Transparent Q2R.
  unfold Q2R.
  unfold Qdiv.
  autorewrite with InjQDown.
  ring.
Qed.

Lemma MotorEventsNthTimeReacLe:
  ∀ (n1 n2 : nat) p1 p2,
  (n1 < n2)%nat
   -> (MotorEventsNthTime n1 p1 + reacTime
      <= MotorEventsNthTime n2 p2)%Q.
Proof.
  intros. apply Qlt_le_weak.
  apply MotorEventsNthTimeReac.
  assumption.
Qed.

Local Transparent Q2R.

Lemma OmegaAtEv1 : let t1 := MotorEventsNthTime 1 (decAuto (1 < 4)%nat I) in
    AbsSmall (Q2R (rotspeed + motorTurnOmegaPrec ω)) ({omega ic} t1).
Proof.
  intro. pose proof correctVel0to1 as H0c.
  simpl in H0c.
  apply proj2 in H0c.
  destruct H0c as [qtrans H0c].
  simpl in H0c.
  pose proof (proj2 (proj1 H0c)) as Ht.
  apply proj2 in H0c.
  apply proj1 in H0c.
  fold t1 in H0c.
  specialize (H0c t1).
  DestImp H0c;
  [|  split;[| reflexivity];
      eapply Qle_trans;[apply Ht|];
      subst t1; apply MotorEventsNthTimeReacLe; omega].
  pose proof (AbsIRNewOmega) as Habs.
  apply eq_imp_leEq in Habs.
  pose proof (AbsIR_plus _ _ _ _ Habs H0c) as Hadd.
  unfold cg_minus in Hadd.
  apply AbsIR_imp_AbsSmall in Hadd.
  ring_simplify in Hadd.
  fold (ω) in Hadd.
  unfold Q2R in Hadd.
  autorewrite with QSimpl in Hadd.
  exact Hadd.
Qed.



Lemma correctVel1to2:
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let requestedVel : Polar2D Q := {|rad := 0;θ := 0|} in
  correctVelDuring requestedVel t1 t2 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, BaseMotors in Hc.
  apply proj1 in Hc.
  (** lets go one by one starting from the first message *)

  unfold MotorEventsNthTime, MotorEventsNth in t1, t2.
  destruct (MotorEvents2 1 (decAuto (1<4)%nat I)) as [evStartTurn  H0m].
  simpl in t1.
  destruct (MotorEvents2 2 (decAuto (2<4)%nat I)) as [evStopTurn  H1m].
  simpl in t2.
  unfold minDelayForIndex, roscore.delay, Basics.compose in H1m.
  Local Opaque getPayloadAndEv.
  autounfold with π₁ in H1m.
  simpl in H1m.
  unfold corrSinceLastVel in Hc.
  unfold lastVelAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
  specialize (Hc (eTime evStopTurn)). simpl in Hc.
  repnd.
  rewrite numPrevEvtsEtime in Hc;[|assumption].
  rewrite H1mrrl in Hc.
  simpl in Hc.
  rewrite (locEvtIndexRW evStartTurn) in Hc;[|tauto].
  rewrite H0mrrrl in Hc.
  simpl in Hc.
  auto.
Qed.

Local Opaque Q2R.

Definition θErrTurn : IR :=
Q2R (rotspeed * (E2EDelVar + 2 * reacTime) 
  + anglePrec + (eeew 0%Q ω) * (E2EDelVar + reacTime))%Q
    + Q2R ((eeew 0%Q ω) / rotspeed)%Q * ('(CRabs (polarTheta targetPos)) + Q2R anglePrec).

Lemma ThetaAtEV2 :
 (|{theta ic} mt2 - optimalTurnAngle|) ≤ θErrTurn.
Proof.
  unfold θErrTurn.
  pose proof correctVel1to2 as Hc.
  simpl in Hc. fold mt1 mt0 in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc. simpl θ in Hc.
  rewrite motorPrec0 in Hc.
  assert (mt1 + reacTime < mt2)%Q 
    as Hassumption 
    by (apply MotorEventsNthTimeReac; omega).
  pose proof (qtimePos reacTime) as H99.
  pose proof (ThetaAtEV1_3) as Ht0. simpl in Ht0.
  simpl in Ht0.
  apply changesToDerivInteg2
    with (F:=(theta ic)) (oldVal:={omega ic} mt1) in Hc;
    eauto with ICR;[| reflexivity].
  rewrite IR_inv_Qzero in Hc.
  rewrite Qmult_0_l in Hc. 
  Local Transparent Q2R.
  unfold Q2R in Hc.
  rewrite inj_Q_Zero in Hc. unfold cg_minus in Hc.
  ring_simplify in Hc.
  rewrite cring_mult_zero_op in Hc.
  setoid_rewrite  cg_inv_zero in Hc.
  rewrite inj_Q_Zero in Hc.
  ring_simplify in Hc.
  pose proof (OmegaAtEv1) as Hth.
  cbv zeta in Hth.
  apply mult_resp_AbsSmallRQt with (y:= reacTime) in Hth.
  apply AbsSmall_imp_AbsIR in Hth.
  rewrite AbsIR_mult_pos in Hth;[|apply qtimePosIR; fail].
  eapply leEq_transitive in Hth;[|apply Hc].
  clear Hc. unfold QT2R in Hth.
  autorewrite with QSimpl in Hth.
  pose proof (AbsIR_plus _ _ _ _ Hth Ht0) as Hadd.
  clear Hth Ht0.
  apply AbsIR_imp_AbsSmall in Hadd.
  revert Hadd. unfoldMC. 
  autounfold with IRMC.
  intro Hadd.
  ring_simplify in Hadd.
  autorewrite with QSimpl in Hadd.
  apply AbsSmall_imp_AbsIR in Hadd.
  eapply leEq_transitive;[apply Hadd|].
  apply eq_imp_leEq. unfold Q2R.
  autorewrite with InjQDown.
  unfold motorTurnOmegaPrec, eeew.
  remember (θ (motorPrec {| rad := 0%Q; θ := ω |})) as ew.
  simpl.
  ring.
Qed.


Lemma ThetaAtEV2P : (|{theta ic} mt2 - idealDirection|) ≤  θErrTurn.
Proof.
  apply ThetaAtEV2.
Qed.

Local Opaque Q2R.
  
Lemma OmegaAtEv2 : let t2 := MotorEventsNthTime 2 (decAuto (2 < 4)%nat I) in
    {omega ic} t2 = 0.
Proof.
  intro. pose proof correctVel1to2 as H0c.
  simpl in H0c.
  apply proj2 in H0c.
  destruct H0c as [qtrans H0c].
  simpl in H0c.
  pose proof (proj2 (proj1 H0c)) as Ht.
  apply proj2 in H0c.
  apply proj1 in H0c.
  fold t2 in H0c.
  specialize (H0c t2).
  DestImp H0c;
  [|  split;[| reflexivity];
      eapply Qle_trans;[apply Ht|];
      subst t2; apply MotorEventsNthTimeReacLe; omega].
  rewrite motorPrec0 in H0c.
  simpl in H0c.
  unfold zero, stdlib_rationals.Q_0 in H0c.
  rewrite IR_inv_Qzero in H0c.
  unfoldMC.
  unfold Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  unfold zero in H0c.
  unfold Zero_instance_QTime in H0c.
  simpl in H0c.
Local Transparent Q2R. unfold Q2R in H0c.
  rewrite inj_Q_Zero in H0c.
  apply AbsIR_eq_zero.
  apply leEq_imp_eq;[exact H0c|].
  apply AbsIR_nonneg.
Qed.

Local Opaque Q2R.

Lemma transVelAtEv2 : let t2 := MotorEventsNthTime 2 (decAuto (2 < 4)%nat I) in
    {transVel ic} t2 = 0.
Proof.
  intro. pose proof correctVel1to2 as H0c.
  simpl in H0c.
  apply proj1 in H0c.
  destruct H0c as [qtrans H0c].
  simpl in H0c.
  pose proof (proj2 (proj1 H0c)) as Ht.
  apply proj2 in H0c.
  apply proj1 in H0c.
  fold t2 in H0c.
  specialize (H0c t2).
  DestImp H0c;
  [|  split;[| reflexivity];
      eapply Qle_trans;[apply Ht|];
      subst t2; apply MotorEventsNthTimeReacLe; omega].
  rewrite motorPrec0 in H0c.
  simpl in H0c.
  unfold zero, stdlib_rationals.Q_0 in H0c.
  rewrite IR_inv_Qzero in H0c.
  unfoldMC.
  unfold Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  unfold zero in H0c.
  unfold Zero_instance_QTime in H0c.
  simpl in H0c.
Local Transparent Q2R. unfold Q2R in H0c.
  rewrite inj_Q_Zero in H0c.
  apply AbsIR_eq_zero.
  apply leEq_imp_eq;[exact H0c|].
  apply AbsIR_nonneg.
Qed.

Hint Resolve OmegaAtEv2 MotorEventsNthTimeInc: ICR.

Lemma correctVel2to3:
  let t1 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let requestedVel : Polar2D Q := {|rad:= QposAsQ speed ; θ := 0 |} in
  correctVelDuring requestedVel t1 t2 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, BaseMotors in Hc.
  apply proj1 in Hc.
  (** lets go one by one starting from the first message *)

  unfold MotorEventsNthTime, MotorEventsNth in t1, t2.
  destruct (MotorEvents2 2 (decAuto (2<4)%nat I)) as [evStartTurn  H0m].
  simpl in t1.
  destruct (MotorEvents2 3 (decAuto (3<4)%nat I)) as [evStopTurn  H1m].
  simpl in t2.
  unfold minDelayForIndex, roscore.delay, Basics.compose in H1m.
  Local Opaque getPayloadAndEv.
  autounfold with π₁ in H1m.
  simpl in H1m.
  unfold corrSinceLastVel in Hc.
  unfold lastVelAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
  specialize (Hc (eTime evStopTurn)). simpl in Hc.
  repnd.
  rewrite numPrevEvtsEtime in Hc;[|assumption].
  rewrite H1mrrl in Hc.
  simpl in Hc.
  rewrite (locEvtIndexRW evStartTurn) in Hc;[|tauto].
  rewrite H0mrrrl in Hc.
  simpl in Hc.
  auto.
Qed.

Definition θ2 := {theta ic} mt2.

Definition rotErrTrans
:= (θ (motorPrec {| rad := QposAsQ speed; θ := 0 |})).


Lemma ThetaEv2To3 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  ∀ (t : QTime),  t2 ≤ t ≤ t3
      → AbsIR ({theta ic} t[-]θ2)[<=]inj_Q ℝ (rotErrTrans * (t3 - t2))%Q.
Proof.
  intros ? ? ? Hle.
  pose proof (qtimePos t) as Hq.
  fold t2.
  pose proof correctVel2to3 as Hc.
  simpl in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc.
  fold t2 t3 in Hc.
  fold rotErrTrans in Hc.
  simpl θ in Hc.
  unfold zero, stdlib_rationals.Q_0 in Hc.
  eapply changesToDerivSameEpsIntegWeaken in Hc; 
    eauto using
    derivRot;
   [|apply MotorEventsNthTimeInc; omega|apply OmegaAtEv2].
  unfold Q2R in Hc. 
  autorewrite with CoRN in Hc.
  unfold t2 in Hc.
  fold (θ2) in Hc.
  fold t2 in Hc.
  unfold QT2R in Hc.
  autorewrite with QSimpl in Hc.
  simpl in Hc.
  assumption.
Qed.

Lemma MotorEv23Gap :
  let t0 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let tgap :Q := (approximate (|targetPos|) distPrec * (Qinv speed)) in
   |QT2Q t1 - QT2Q t0 -  tgap| 
  ≤ 2 * (sendTimeAcc + delivDelayVar)%Q.
Proof.
  intros ? ? ?.
  apply MotorEvGap.
Qed.

Definition Ev23TimeGapUB : IR :=
  ((CRasIR ((|targetPos|)) + distPrec) * (Qinv speed))
  + E2EDelVar.

Definition θErrTrans : IR :=
(QT2R rotErrTrans) * Ev23TimeGapUB.

Lemma MotorEv23Gap2_2 :
  let t0 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
   AbsIR ((Q2R (QT2Q t1 - QT2Q t0)) 
      - ((CRasIR (|targetPos|)) * (Qinv speed)))
  [<=] Q2R ((distPrec* (Qinv speed)) + 2 * (sendTimeAcc + delivDelayVar)).
Proof.
  intros ? ? .
  pose proof  MotorEv23Gap  as Hg.
  simpl in Hg.
  fold t0 t1 in Hg.
  apply (inj_Q_leEq IR) in Hg.
  rewrite <- AbsIR_Qabs in Hg.
  rewrite cgminus_Qminus, inj_Q_minus in Hg.
  pose proof (approximateAbsSmallIR (|targetPos |) distPrec) as Hball.
  apply AbsSmall_minus in Hball.
  apply mult_resp_AbsSmallR with (y:= Q2R (Qinv speed)) in Hball;
    [| apply QposDivLe0IR].
  rewrite  IRDistMinus in Hball.
  autorewrite with QSimpl in Hball.
  simpl in Hball.
  apply AbsIR_imp_AbsSmall in Hg.
  pose proof (AbsSmall_plus _ _ _ _ _  Hg Hball) as Hadd.
  clear Hball Hg.
  unfold Q2R, cg_minus in Hadd.
  simpl in Hadd. revert Hadd.
  unfoldMC. intro Hadd.
  ring_simplify in Hadd.
  autounfold with IRMC.
  apply AbsSmall_imp_AbsIR.
  autorewrite with QSimpl in Hadd.
  unfold Mult_instance_IR.
  eapply AbsSmall_morph_wd;
    [| | apply Hadd].
- apply inj_Q_wd. simpl. ring.
- unfold Q2R, Qminus, cg_minus. reflexivity.
Qed.

Lemma MotorEv23Gap2_3 :
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
   Q2R (QT2Q t3 - QT2Q t2) ≤ Ev23TimeGapUB.
Proof.
  intros ? ?.
  pose proof MotorEv23Gap2_2 as Hp.
  fold t2 t3 in Hp.
  Local Opaque Q2R.
  simpl in Hp.
  apply AbsIR_imp_AbsSmall in Hp.
  unfold AbsSmall in Hp.
  apply proj2 in Hp.
  apply shift_leEq_plus in Hp.
  unfold Ev23TimeGapUB.
  eapply leEq_transitive;[apply Hp|].
  clear Hp.
  unfold E2EDelVar.
  unfoldMC.
  autounfold with IRMC.
  unfold Mult_instance_IR.
  rewrite ring_distl_unfolded.
  simpl. idtac. destruct sendTimeAcc, delivDelayVar.
  simpl. apply eqImpliesLeEq.
  simpl.  
  autorewrite with QSimpl. simpl.
  Local Transparent Q2R.
  unfold Q2R. 
  rewrite inj_Q_plus.
  ring.
Qed.

Definition Ev23TimeGapLB : IR :=
  ((CRasIR ((|targetPos|)) - QposAsQ distPrec) * (Qinv speed))
  - E2EDelVar.

Lemma MotorEv23GapLB :
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
   Ev23TimeGapLB  ≤  Q2R (t3 - t2).
Proof.
  intros ? ?.
  pose proof MotorEv23Gap2_2 as Hp.
  fold t2 t3 in Hp.
  Local Opaque Q2R.
  simpl in Hp.
  apply AbsIR_imp_AbsSmall in Hp.
  unfold AbsSmall in Hp.
  apply proj1 in Hp.
  apply shift_plus_leEq in Hp.
  unfold Ev23TimeGapLB.
  eapply leEq_transitive;[|apply Hp].
  clear Hp.
  unfold E2EDelVar.
  unfoldMC.
  autounfold with IRMC.
  unfold Mult_instance_IR.
  rewrite ring_distl_unfolded.
  simpl.  destruct sendTimeAcc, delivDelayVar.
  simpl. apply eqImpliesLeEq.
  simpl.  
  autorewrite with QSimpl. simpl.
  Local Transparent Q2R.
  unfold Q2R. 
  rewrite inj_Q_inv.
  rewrite inj_Q_inv.
  pose proof QDivQopp as Hq.
  unfold Qdiv in Hq.
  rewrite <- Hq.
  rewrite inj_Q_inv.
  rewrite inj_Q_plus.
  ring.
Qed.


Lemma ThetaEv2To3_2 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  ∀ (t : QTime),  t2 ≤ t ≤ t3
      → AbsIR ({theta ic} t[-]θ2)[<=]θErrTrans.
Proof.
  intros ? ? ? Hb. apply ThetaEv2To3 in Hb.
  fold t2 t3 in Hb.
  unfold θErrTrans.
  rewrite inj_Q_mult in Hb.
  eapply leEq_transitive;[apply Hb|].
  eapply mult_resp_leEq_lft;[| eauto with ROSCOQ; fail].
  apply MotorEv23Gap2_3.
Qed.

Lemma ThetaEv2To3_3 :
  ∀ (t : QTime),  mt2 ≤ t ≤ mt3
      → AbsIR ({theta ic} t[-]optimalTurnAngle)
        ≤ θErrTrans + θErrTurn.
Proof.
  intros ? Hb. apply ThetaEv2To3_2 in Hb.
  pose proof ThetaAtEV2 as Ht.
  cbv zeta in Ht.
  
  fold θ2 in Ht.
  apply AbsIR_imp_AbsSmall in Ht.
  apply AbsIR_imp_AbsSmall in Hb.
  apply AbsSmall_imp_AbsIR.
  pose proof (AbsSmall_plus _ _ _ _ _  Hb Ht) as Hadd.
  clear Ht Hb. 
  autounfold with IRMC in Hadd.
  unfold cg_minus in Hadd.
  ring_simplify in Hadd.
  assumption.
Qed.

Lemma ThetaEv2To3P : ∀ (t : QTime),  mt2 ≤ t ≤ mt3 
  → |{theta ic} t - idealDirection| ≤ θErrTrans + θErrTurn.
Proof.
  apply ThetaEv2To3_3.
Qed.

Lemma MotorEventsNthTimeIncIR:
  ∀ (n1 n2 : nat) p1 p2,
  (n1 < n2)%nat
   -> QT2T (MotorEventsNthTime n1 p1) 
      [<=] QT2T (MotorEventsNthTime n2 p2).
Proof.
  intros.
  rewrite <- QT2T_Q2R.
  rewrite <- QT2T_Q2R.
  apply inj_Q_leEq.
  apply MotorEventsNthTimeInc.
  assumption.
Qed.


Definition Ev2To3Interval : TIntgBnds.
  exists (QT2T (MotorEventsNthTime 2 (decAuto (2<4)%nat I)), 
            QT2T (MotorEventsNthTime 3 (decAuto (3<4)%nat I))).
  simpl.
  apply MotorEventsNthTimeIncIR.
  omega.
Defined.

Definition distTraveled : IR := Cintegral Ev2To3Interval (transVel ic).


Add Ring cart2dir : Cart2DIRRing.

Variable nztp : ([0] [<] normIR (' targetPos)).

Definition rotOrigininPos : Cart2D TContR:=
  rotateOriginTowardsF (' targetPos) nztp (position ic).


Definition YDerivRot : TContR :=
(transVel ic) * (FSin (theta ic - FConst optimalTurnAngle)).

Definition XDerivRot : TContR :=
(transVel ic) * (FCos (theta ic - FConst optimalTurnAngle)).

Lemma DerivRotOriginTowardsTargetPos : 
  (isDerivativeOf XDerivRot (X rotOrigininPos)
   × isDerivativeOf YDerivRot (Y rotOrigininPos)).
Proof.
  unfold YDerivRot, XDerivRot.
  apply DerivativerotateOriginTowards2; eauto with ICR.
Qed.

Hint Resolve (fst DerivRotOriginTowardsTargetPos) 
             (snd DerivRotOriginTowardsTargetPos) : ICR.

Hint Unfold Mult_instance_TContR Plus_instance_TContR
  Negate_instance_TContR : TContR.

Lemma YDerivAtTime : ∀ (t: Time),
  {YDerivRot} t 
  = {transVel ic} t[*]Sin ({theta ic} t[-]optimalTurnAngle).
Proof.
  intros ?.
  unfold YDerivRot.
  unfoldMC.
  autounfold with TContR.
  autorewrite with IContRApDown.
  reflexivity.
Qed.

Lemma XDerivAtTime : ∀ (t: Time),
  {XDerivRot} t 
  = {transVel ic} t[*]Cos ({theta ic} t[-]optimalTurnAngle).
Proof.
  intros ?.
  unfold XDerivRot.
  unfoldMC.
  autounfold with TContR.
  autorewrite with IContRApDown.
  reflexivity.
Qed.


Definition rotOrgPosAtTime : Time → (Cart2D IR) :=
  CartFunEta rotOrigininPos.



Lemma PosRotAxisAtEV0:
  ∀ t : QTime, t ≤ mt0 → rotOrgPosAtTime t = 0.
Proof.
  intros ? Hle.
  apply TransVelPosAtEV0 in Hle.
  apply proj2 in Hle.
  unfold posAtTime in Hle.
  unfold equiv, EquivCart in Hle.
  simpl in Hle.
  destruct (initPos ic) as [Hx Hy].
  repnd. 
  setoid_rewrite Hx in Hlel.
  setoid_rewrite Hy in Hler.
  unfold rotOrgPosAtTime, rotOrigininPos.
  rewrite rotateOriginTowardsFAp.
  unfold rotateOriginTowards.
  simpl.
  unfold zero, Zero_instance_Cart2D, equiv, EquivCart.
  simpl.
  rewrite Hler, Hlel.
  unfoldMC.
  autounfold with IRMC.
  rewrite inj_Q_Zero.
  split; ring.
Qed.

Definition transErrRot
:= (rad (motorPrec {| rad := 0 ; θ := ω |})).


Hint Resolve MotorEventsNthTimeIncSn : ICR.

Definition rotDerivAtTime (t : Time) : Cart2D IR:=
  {|X:= {XDerivRot} t; Y:= {YDerivRot} t|}.

 
Lemma RotXYDerivLeSpeed : ∀ (t : Time) (ub : IR),
  AbsIR ({transVel ic} t) ≤ ub
  → XYAbs (rotDerivAtTime t) ≤ {|X:=ub; Y:=ub|} .
Proof.
  intros ? ? Hb.
  unfold rotDerivAtTime, XYAbs, le, Cart2D_instance_le.
  simpl.
  rewrite YDerivAtTime, XDerivAtTime.
  rewrite AbsIR_resp_mult.
  rewrite AbsIR_resp_mult.
  match goal with
  [|- _ ∧ (_ ≤ ?r) ] => rewrite <- (mult_one _ r)
  end.
  split; apply mult_resp_leEq_both; trivial;
      try apply AbsIR_nonneg;
  [apply AbsIR_Cos_leEq_One|apply AbsIR_Sin_leEq_One].
Qed.


Lemma RotDerivInteg : ∀ (a b : QTime) (ubx uby : IR),
  a ≤ b
  → (∀ (t:QTime), 
        a ≤ t ≤ b
        → XYAbs (rotDerivAtTime t) ≤ {|X:=ubx; Y:=uby|})
  → XYAbs (rotOrgPosAtTime b - rotOrgPosAtTime a)
    ≤ {|X:=ubx * (b-a)%Q ; Y:=uby * (b-a)%Q|}.
Proof.
  intros ? ?  ? ? Hle Hd.
  pose proof (λ t p, proj1 (Hd t p)) as Hx.
  pose proof (λ t p, proj2 (Hd t p)) as Hy.
  simpl in Hx, Hy.
  eapply TDerivativeAbsQ0 in Hx; auto;
    [|apply (fst DerivRotOriginTowardsTargetPos)].
  eapply TDerivativeAbsQ0 in Hy; auto;
    [|apply (snd DerivRotOriginTowardsTargetPos)].
  split; auto.
Qed.

Lemma LeRotIntegSpeed : ∀ (a b : QTime) (ub : IR),
   a ≤ b
  → (∀ (t:QTime), a ≤ t ≤ b → AbsIR ({transVel ic} t) ≤ ub)
  → XYAbs (rotOrgPosAtTime b - rotOrgPosAtTime a) 
      ≤ {|X:=ub* (b-a)%Q; Y:=ub* (b-a)%Q|} .
Proof.
  intros.
  apply RotDerivInteg; [assumption|].
  intros.
  apply RotXYDerivLeSpeed; auto.
Qed.

Lemma LeRotIntegSpeed2 : ∀ (a b : QTime) (tub : IR) (ub : IR),
   a ≤ b
  → Q2R (b - a)%Q ≤ tub
  → (∀ (t:QTime), a ≤ t ≤ b → AbsIR ({transVel ic} t) ≤ ub)
  → XYAbs (rotOrgPosAtTime b - rotOrgPosAtTime a) 
      ≤ {|X:=ub* tub%Q; Y:=ub* tub%Q|} .
Proof.
  intros ? ? ? ? Hle Htle Hd.
  eapply Cart2D_instance_le_IRtransitive;[apply LeRotIntegSpeed|]; 
    eauto.
  specialize (Hd a).
  DestImp Hd; [|split;auto; unfold le,Le_instance_QTime; reflexivity].
  split; apply mult_resp_leEq_lft; auto;
  (eapply leEq_transitive;[|apply Hd]);
  apply AbsIR_nonneg.
Qed.

Lemma XYDerivEv0To1 : ∀ (t:QTime), 
  mt0 ≤ t ≤ mt1 
  → AbsIR ({transVel ic} t) ≤ QT2Q transErrRot.
Proof.
  intros ? Hb.
  pose proof correctVel0to1 as H01.
  simpl in H01.
  fold mt0 mt1 in H01.
  apply proj1 in H01.
  Local Opaque Q2R.
  simpl in H01.
  fold ω transErrRot in H01.
  eapply changesToDerivSameDeriv in H01; eauto with ICR;
    [|apply MotorEventsNthTimeIncSn | apply TransVelPosAtEV0; unfold le, Le_instance_QTime; reflexivity].
  autorewrite with CoRN in H01.
  assumption.
Qed.

Local Transparent Q2R.


Lemma AutoRWX0 :
  {X rotOrigininPos} mt0 [=] 0.
Proof.
  apply (λ p , proj1 (PosRotAxisAtEV0 mt0 p)).
  unfold le, Le_instance_QTime; reflexivity.
Qed.

Lemma AutoRWY0 :
  {Y rotOrigininPos} mt0 [=] 0.
Proof.
  apply (λ p , proj2 (PosRotAxisAtEV0 mt0 p)).
  unfold le, Le_instance_QTime; reflexivity.
Qed.

Hint Rewrite AutoRWX0 AutoRWY0: ICR.



Lemma Zero_Instace_IR_mess :
  Zero_Instace_IR_better =  Zero_instance_IR.
  unfold Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  reflexivity.
Qed.

Lemma Zero_Instace_Cart2DMess :
 @Zero_instance_Cart2D _ Zero_Instace_IR_better
 = @Zero_instance_Cart2D _ Zero_instance_IR.
Proof.
  unfold Zero_instance_Cart2D.
  unfold equiv, EquivCart. simpl.
  unfold zero.
  rewrite Zero_Instace_IR_mess.
  split; reflexivity.
Qed.

Instance Cart2DIRZeroMess : (Zero (Cart2D IR)) 
:= @Zero_instance_Cart2D _ Zero_instance_IR.

Lemma PosRotAxisAtEV1 :
  XYAbs (rotOrgPosAtTime mt1) 
      ≤ sameXY  (QT2R transErrRot * Ev01TimeGapUB).
Proof.
  assert (rotOrgPosAtTime mt1 = rotOrgPosAtTime mt1 -0).
  idtac. unfold Cart2DIRZeroMess.  ring.
  rewrite H.
  rewrite <-  Zero_Instace_Cart2DMess.
  rewrite <- (PosRotAxisAtEV0 mt0);
    [| unfold le, Le_instance_QTime; reflexivity].
  apply LeRotIntegSpeed2.
  - exact EautoTimeICR0.
  - exact MotorEv01Gap4.
  - exact XYDerivEv0To1.
Qed.

Lemma SpeedEv1To2: 
  ∃ qtrans : QTime, (mt1 ≤ qtrans ≤ mt1 + reacTime) ∧
  (∀ t : QTime,
       mt1 ≤ t ≤ qtrans → AbsIR ({transVel ic} t) ≤ QT2Q transErrRot)
  ∧ (∀ t:QTime, qtrans ≤ t ≤ mt2 
        → AbsIR ({transVel ic} t) ≤ 0).
Proof.  
  pose proof correctVel1to2 as Hc.
  fold mt1 mt2 in Hc.
  cbv zeta in Hc.
  apply proj1 in Hc.
  Local Opaque Q2R.
  simpl in Hc.
  rewrite motorPrec0 in Hc.
  simpl in Hc.
  destruct Hc as [qtrans Hc].
  exists qtrans.
  repnd.
  split;[split; assumption|].
  pose proof (λ t p, (betweenRAbs _ _ _ _ (qtimePosIR 0)
       (Hcrr t p))) as Hcr.
  clear Hcrr.
  split;[clear Hcrl | clear Hcr]; intros ? Hb.
- apply Hcr in Hb.
  unfold QT2R in Hb.
  autorewrite with CoRN in Hb.
  eapply leEq_transitive;[apply Hb|].
  apply XYDerivEv0To1.
  unfold le, Le_instance_QTime.
  split; [apply EautoTimeICR0|reflexivity].
- apply Hcrl in Hb.
  autorewrite with CoRN in Hb.
  assumption.
Qed.

Local Transparent Q2R.

Lemma multZeroIRMC :
  ∀ (r : IR),
    0*r =0.
Proof.
  intros.
  autounfold with IRMC.
  autorewrite with CoRN.
  reflexivity.
Qed.


Hint Rewrite multZeroIRMC : CoRN.


Lemma PosRotAxisAtEV1to2 :
  XYAbs (rotOrgPosAtTime mt2 - rotOrgPosAtTime mt1) 
      ≤ sameXY  (Q2R (transErrRot * reacTime)).
Proof.
  pose proof SpeedEv1To2 as Hc.
  destruct Hc as [qtrans Hc].
  repnd.
  unfold le, Le_instance_QTime, plus, Plus_instance_QTime in Hclr.
  simpl in Hclr.
  apply LeRotIntegSpeed2 with (tub:= QT2R reacTime) in Hcrl;
  [| assumption| apply inj_Q_leEq; simpl; lra ].
  
  unfold le, Le_instance_QTime, plus in Hcll.
  assert ((mt1 + reacTime < mt2)%Q) 
    as Hassumption by (apply MotorEventsNthTimeReac; omega).
  apply LeRotIntegSpeed2 with (tub:= Q2R ((mt2 - qtrans))) in Hcrr;
  [| unfold le, Le_instance_QTime; lra | apply inj_Q_leEq; simpl; reflexivity].
  clear Hassumption.
  rewrite multZeroIRMC in Hcrr.
  pose proof (XYAbsLeAdd _ _ _ _ Hcrr Hcrl) as Hadd.
  clear Hcrr Hcrl.
  assert ((rotOrgPosAtTime mt2 - rotOrgPosAtTime qtrans +
          (rotOrgPosAtTime qtrans - rotOrgPosAtTime mt1))
      = (rotOrgPosAtTime mt2 - rotOrgPosAtTime mt1)) as Heq by ring.
  rewrite Heq in Hadd. clear Heq.
  rewrite Zero_Instace_Cart2DMess in Hadd.
  fold Cart2DIRZeroMess in Hadd.
  fold zero in Hadd.
  unfold Cart2DIRZeroMess in Hadd.
  ring_simplify in Hadd.
  unfold Q2R. unfold sameXY.
  rewrite  inj_Q_mult.
  exact Hadd.
Qed.


Lemma PosRotAxisAtEV2 :
  XYAbs (rotOrgPosAtTime mt2) 
      ≤ sameXY  ((QT2R transErrRot * (QT2R reacTime + Ev01TimeGapUB))).
Proof.
  pose proof (XYAbsLeAdd _ _ _ _ PosRotAxisAtEV1to2 PosRotAxisAtEV1) 
    as Hadd.
  ring_simplify in Hadd.
  assert ((rotOrgPosAtTime mt2 - rotOrgPosAtTime mt1 + rotOrgPosAtTime mt1)
        = rotOrgPosAtTime mt2) as Heq by ring.
  rewrite Heq in Hadd.
  clear Heq.
  rewrite sameXYAdd in Hadd.
  eapply ProperLeCartIR;[| | apply Hadd];
    [reflexivity|].
  apply ProperSameXY.
  unfold QT2R, Q2R.
  autounfold with IRMC.
  rewrite inj_Q_mult.
  ring.
Qed.

(* consider changing types of [θErrTrans]
    and [θErrTurn] to [Qpos]*)
Variable ThetaErrLe90 :
   θErrTrans + θErrTurn ≤  ('½) * π.


Lemma ThetaErrLe90IR :
   θErrTrans + θErrTurn ≤ Pi [/]TwoNZ.
Proof.
  rewrite <- PiBy2NoMC.
  assumption.
Qed.

Hint Resolve ThetaErrLe90IR : ICR.

Lemma ThetaErrGe0:
   [0] [<=] θErrTrans + θErrTurn.
Proof.
  pose proof (ThetaEv2To3_3 
      (MotorEventsNthTime 2 (decAuto (2 < 4)%nat I))) as H.
  unfold le, Le_instance_QTime in H.
  DestImp H;[| split;[reflexivity| apply MotorEventsNthTimeInc; omega]].
  eapply leEq_transitive;[| apply H].
  apply AbsIR_nonneg.
Qed.

Lemma CosThetaErrGe0:
   [0] [<=] Cos (θErrTrans + θErrTurn).
Proof.
  apply Cos_nonneg.
  - eauto using leEq_transitive, MinusPiBy2Le0, ThetaErrGe0.
  - apply ThetaErrLe90IR.
Qed.

Hint Resolve ThetaErrGe0 CosThetaErrGe0 : ICR.

Lemma ThetaErrLe1180 : 
  θErrTrans + θErrTurn ≤  π.
Proof.
  rewrite PiBy2NoMC in ThetaErrLe90.
  eapply leEq_transitive;[apply ThetaErrLe90 |].
  apply nonneg_div_two'.
  eauto using less_leEq, pos_Pi.
Qed.


Definition transErrTrans
:= (rad (motorPrec {| rad := QposAsQ speed; θ := 0 |})).


Lemma SpeedUbEv2To3 : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  -> AbsIR ({transVel ic} t)[<=](speed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  pose proof correctVel2to3 as Hc.
  fold t2 t3 in Hc.
  cbv zeta in Hc.
  apply proj1 in Hc.
  simpl in Hc.
  fold (transErrTrans) in Hc.
  destruct Hc as [qtrans Hc].
  repnd.
  pose proof transVelAtEv2 as ht.
  fold t2 in ht.
  cbv zeta in ht.
  unfold between in Hcrr.
  setoid_rewrite ht in Hcrr.
  pose proof (λ t p, (betweenLAbs _ _ _ _ (qtimePosIR transErrTrans)
       (Hcrr t p)))
     as Hqt. clear Hcrr ht.
  setoid_rewrite IR_inv_Qzero in Hqt.
  setoid_rewrite AbsIR_minus in Hqt.
  setoid_rewrite IR_inv_Qzero in Hqt.
  setoid_rewrite AbsIR_minus in Hcrl.
  pose proof (λ t p, (AbsIR_bnd_AbsIR  _ _ _
          (Hcrl t p)))
     as Hmrl. clear Hcrl.
  setoid_rewrite (AbsIRQpos speed) in Hmrl.
  setoid_rewrite (AbsIRQpos speed) in Hqt.
  unfold QT2R in Hqt.
  unfold Q2R.
  autorewrite with InjQDown.
  rename Hqt into Hmrr.
  pose proof (Qlt_le_dec t qtrans) as Hdec.
  Dor Hdec;[clear Hmrl | clear Hmrr].
- apply Qlt_le_weak in Hdec.
  specialize (Hmrr t (conj Hbl Hdec)). 
  assumption.
- unfold le, Le_instance_QTime in Hbr.
  assert (t <= t3)%Q as Hup by lra.
  specialize (Hmrl t (conj Hdec Hup)).
  assumption.
Qed.
  

(** prepping for [TDerivativeAbsQ] *)
Lemma YDerivEv2To3 : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  → AbsIR ({YDerivRot} t) 
      ≤   (Sin (θErrTrans + θErrTurn)) * (speed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  unfold YDerivRot.
  autounfold with IRMC TContRMC.
  fold (theta ic[-](ConstTContR optimalTurnAngle)).
  rewrite YDerivAtTime.
  rewrite AbsIR_resp_mult.
  rewrite mult_commut_unfolded.
  apply mult_resp_leEq_both; try apply 
    AbsIR_nonneg;[|].
- apply ThetaEv2To3_3 in Hb.
  rewrite  AbsIRSine;
    [| apply AbsIR_imp_AbsSmall;
       eapply leEq_transitive;[apply Hb|apply ThetaErrLe1180]].
  apply TrigMon.Sin_resp_leEq; [| | assumption].
  + eauto using leEq_transitive, 
      MinusPiBy2Le0,AbsIR_nonneg.
  + apply ThetaErrLe90IR.
- apply SpeedUbEv2To3; assumption.
Qed.


(** trivial simplification *)
Lemma YDerivEv2To3_1 : ∀ (t:QTime), 
  mt2 ≤ t ≤ mt3 
  → AbsIR ({YDerivRot} t [-] [0]) 
      ≤   (Sin (θErrTrans + θErrTurn)) * (speed + transErrTrans)%Q.
Proof.
  intros.
  rewrite cg_inv_zero.
  eapply YDerivEv2To3; eauto.
Qed.



Lemma YChangeEv2To3 :
  AbsIR ({Y rotOrigininPos} mt3 [-] {Y rotOrigininPos} mt2) 
      ≤   Q2R (mt3 - mt2)%Q * ((Sin (θErrTrans + θErrTurn))
                       * (speed + transErrTrans)%Q).
Proof.
  pose proof (YDerivEv2To3_1) as Hyd.
  apply (TDerivativeAbsQ (Y rotOrigininPos)) in Hyd;
    eauto 2 with ICR;
    [|apply MotorEventsNthTimeInc; omega].
  autorewrite with CoRN in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  apply eqImpliesLeEq.
  autounfold with IRMC.
  ring.
Qed.

(** Whis this spec is totally in terms of the parameters,
    it does not clarify how ttanslation speed matters, because 
    [Ev23TimeGapUB] has terms that depend on speed.
    So does [θErrTrans]. 
    One can unfold Ev23TimeGapUB and cancel out some terms. *)
Lemma YChangeEv2To3_2 :
  AbsIR ({Y rotOrigininPos} mt3 [-] {Y rotOrigininPos} mt2) 
      ≤  Ev23TimeGapUB  * ((Sin (θErrTrans + θErrTurn))
                       * (speed + transErrTrans)%Q).
Proof.
  intros.
  pose proof (YChangeEv2To3) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  clear Hyd.
  apply mult_resp_leEq_rht;[apply MotorEv23Gap2_3; fail|].
  eapply leEq_transitive;[apply AbsIR_nonneg| apply YDerivEv2To3].
  instantiate (1:=MotorEventsNthTime 2 (decAuto (2 < 4)%nat I)).
  unfold le, Le_instance_QTime.
  split;[reflexivity|].
  apply MotorEventsNthTimeInc. omega.
Qed.

Lemma qpCancel  : ∀ (q : Qpos) (r: IR),
  (inj_Q IR (QposAsQ q)) [*] r [*] (inj_Q IR (/q)%Q) [=] r.
Proof.
  intros.
  symmetry.
  autounfold with IRMC.
  rewrite  mult_commut_unfolded, mult_assoc_unfolded.
  rewrite <- inj_Q_mult.
  match goal with
  [|- _ [=] ?r ] => remember r as rr
  end.
  rewrite <- mult_one.
  rewrite  mult_commut_unfolded.
  subst rr.
  apply mult_wdl.
  rewrite <- inj_Q_One.
  apply inj_Q_wd.
  simpl. destruct q as [qq qp].
  simpl. field.
  lra.
Qed.


Lemma YChangeEv2To3_3 :
  AbsIR ({Y rotOrigininPos} mt3 [-] {Y rotOrigininPos} mt2) 
      ≤ (Sin (θErrTrans + θErrTurn) * 
        ((CRasIR (|targetPos |) + distPrec) 
          + Ev23TimeGapUB * QT2R transErrTrans
          + Q2R speed * E2EDelVar)).
Proof.
  intros.
  pose proof (YChangeEv2To3_2) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  clear Hyd.
  apply eqImpliesLeEq.
  unfold Ev23TimeGapUB.
  unfoldMC. autounfold with IRMC.
  rewrite mult_commut_unfolded, <- mult_assoc_unfolded.
  apply mult_wdr.
  unfold QT2R, Q2R.
  rewrite inj_Q_plus.
  ring_simplify.
  rewrite qpCancel.
  rewrite qpCancel.
  ring_simplify.
  autorewrite with InjQDown.
  apply plus_resp_eq.
  reflexivity.
Qed.

Lemma transErrRotEq :
  (eeev 0 ω) = transErrRot.
reflexivity.
Qed.

Lemma transErrTransEq :
  (eeev speed 0) = transErrTrans.
reflexivity.
Qed.


Definition ErrY': IR :=  '(eeev 0 ω) * (QT2R reacTime + Ev01TimeGapUB)
+ (Sin (θErrTrans + θErrTurn)) * (CRasIR (|targetPos |) + distPrec + Ev23TimeGapUB * '(eeev speed 0) + (Q2R speed) * E2EDelVar).

Lemma Ev3Y' : AbsIR ({Y rotOrigininPos} mt3)  ≤ ErrY'.
Proof.
  pose proof YChangeEv2To3_3 as Ha.
  pose proof PosRotAxisAtEV2 as Hb.
  apply proj2 in Hb.
  unfold XYAbs in Hb.
  Local Opaque rotOrigininPos.
  simpl in Hb.
  apply AbsIR_imp_AbsSmall in Hb.
  apply AbsIR_imp_AbsSmall in Ha.
  pose proof (AbsSmall_plus _ _ _ _ _ Hb Ha) as Hadd.
  clear Ha Hb.
  match type of Hadd with
    AbsSmall ?l _ => remember l as ll
  end.
  autounfold with IRMC in Hadd.
  unfold cg_minus in Hadd.
  Local Opaque Sin.
  simpl in Hadd. ring_simplify in Hadd.
  apply AbsSmall_imp_AbsIR in Hadd.
  eapply leEq_transitive;[apply Hadd|].
  subst ll. clear.
  apply eqImpliesLeEq.
  reflexivity.
Qed.


Hint Resolve injQ_nonneg : CoRN.

Hint Resolve QPQTQplusnNeg : ROSCOQ.

Variable speedTransErrTrans : (0 <= speed - transErrTrans)%Q.


(** This proof can be generalized for even functions.
    Similarly, [AbsIRSin] can be generalized for odd functions *)
  
Lemma XDerivEv2To3UBAux : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  → AbsIR ({XDerivRot} t) ≤ (speed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  unfold XDerivRot.
  autounfold with IRMC TContRMC.
  fold (theta ic[-](ConstTContR optimalTurnAngle)).
  rewrite XDerivAtTime.
  rewrite AbsIR_resp_mult.
  match goal with
  [|- _ [<=] ?r ] => rewrite <- (mult_one _ r)
  end.
  apply mult_resp_leEq_both;
      try apply AbsIR_nonneg.
- apply SpeedUbEv2To3. assumption.
- apply AbsIR_Cos_leEq_One.
Qed.

Lemma XDerivEv2To3UB : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  → ({XDerivRot} t) ≤ (speed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  eapply leEq_transitive;[| apply (XDerivEv2To3UBAux t); assumption].
  apply leEq_AbsIR.
Qed.

Lemma XChangeUBEv2To3 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
   ({X rotOrigininPos} t3 [-] {X rotOrigininPos} t2) 
      ≤  ((t3 - t2) * (speed + transErrTrans))%Q.
Proof.
  intros ? ?.
  unfold Q2R.
  rewrite Qmult_comm.
  rewrite inj_Q_mult.
  eapply TDerivativeUBQ; eauto 2 with ICR;
   [apply MotorEventsNthTimeInc; omega|].
  apply XDerivEv2To3UB.
Qed.

Lemma XChangeUBEv2To3_2 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
   ({X rotOrigininPos} t3 [-] {X rotOrigininPos} t2) 
      ≤  (Ev23TimeGapUB * (speed + transErrTrans)%Q).
Proof.
  intros.
  pose proof (XChangeUBEv2To3) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  fold t2 t3. clear Hyd.
  unfold Q2R. rewrite inj_Q_mult.
  apply mult_resp_leEq_rht;[apply MotorEv23Gap2_3; fail|].
  eauto 2 with CoRN ROSCOQ.
Qed.


Lemma SpeedLbEv2To3 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  ∃ qtrans : QTime, (t2 <= qtrans <= t2 + reacTime)%Q ∧
  (∀ t:QTime, t2 ≤ t ≤ qtrans →  0 ≤ ({transVel ic} t))
  ∧ (∀ t:QTime, qtrans ≤ t ≤ t3 →
        Q2R (speed - transErrTrans)%Q [<=] ({transVel ic} t)).
Proof.
  intros ? ?.
  pose proof correctVel2to3 as Hc.
  fold t2 t3 in Hc.
  cbv zeta in Hc.
  apply proj1 in Hc.
  simpl in Hc.
  fold (transErrTrans) in Hc.
  destruct Hc as [qtrans Hc].
  exists qtrans.
  repnd.
  split;[split; assumption|].
  split;[clear Hcrl | clear Hcrr]; intros ? Hb.
- apply Hcrr in Hb.
  unfold between in Hb.
  apply proj1 in Hb.
  unfold t2 in Hb.
  rewrite transVelAtEv2 in Hb.
  rewrite leEq_imp_Min_is_lft in Hb;[assumption|].
  autorewrite with QSimpl. apply inj_Q_leEq.
  simpl. assumption.
- apply Hcrl in Hb.
  apply AbsIR_imp_AbsSmall in Hb.
  unfold AbsSmall in Hb.
  apply proj1 in Hb.
  apply shift_plus_leEq in Hb.
  eapply leEq_transitive;[|apply Hb].
  autorewrite with QSimpl.
  apply inj_Q_leEq.
  simpl.
  lra.
Qed.

Lemma XDerivLBEv2To3 : 
  ∃ qtrans : QTime, (mt2 <= qtrans <= mt2 + reacTime)%Q ∧
  (∀ t:QTime, mt2 ≤ t ≤ qtrans →  0 ≤ ({XDerivRot} t))
  ∧ (∀ t:QTime, qtrans ≤ t ≤ mt3 →
        (Cos (θErrTrans + θErrTurn)) * (speed - transErrTrans)%Q 
          [<=] (({XDerivRot} t))).
Proof.
  pose proof SpeedLbEv2To3 as Hs.
  fold mt2 mt3 in Hs.
  cbv zeta in Hs. destruct Hs as [qtrans Hs].
  exists qtrans. repnd.
  split;[split;assumption|].
  unfold XDerivRot.
  autounfold with IRMC TContRMC.
  unfold Le_instance_QTime, stdlib_rationals.Q_0.
  fold (theta ic[-](ConstTContR optimalTurnAngle)).
  split;[clear Hsrr | clear Hsrl]; intros t Hb.
- rewrite XDerivAtTime.
  pose proof Hb as Hbb. apply Hsrl in Hb. clear Hsrl.
  rewrite inj_Q_Zero.
  autounfold with IRMC in Hb.
  rewrite inj_Q_Zero in Hb.
  apply mult_resp_nonneg;[assumption|].
  clear Hb.
  apply Cos_nonnegAbs.
  eapply leEq_transitive;[apply ThetaEv2To3_3| apply ThetaErrLe90IR].
  unfold le, Le_instance_QTime.
  repnd. split; try lra.
  pose proof MotorEventsNthTimeReac.
  assert ((mt2 + reacTime < mt3)%Q) 
    as Hassumption by (apply MotorEventsNthTimeReac; omega).
   lra.
- rewrite XDerivAtTime.
  assert ((mt2 <= t <= mt3)%Q) as Hbb by lra.
  apply Hsrr in Hb.
  clear Hsrr.
  rewrite mult_commut_unfolded.
  apply ThetaEv2To3_3 in Hbb.
  apply mult_resp_leEq_both; trivial;
    [eauto 2 with CoRN; fail| apply CosThetaErrGe0| ].
  setoid_rewrite CosEven2 at 2;
    [|eapply leEq_transitive;[apply Hbb| apply ThetaErrLe90IR]].
  apply TrigMon.Cos_resp_leEq;
        trivial;[apply AbsIR_nonneg| apply ThetaErrLe1180].
Qed.

Lemma XChangeLBEv2To3 :
  ∃ qtrans : QTime,  (mt2 <= qtrans <= mt2 + reacTime)%Q
  ∧ (Cos (θErrTrans + θErrTurn) 
        * (speed - transErrTrans)%Q 
        * (mt3 - qtrans)%Q)
      ≤  ({X rotOrigininPos} mt3 [-] {X rotOrigininPos} mt2).
Proof.
  pose proof XDerivLBEv2To3 as H.
  cbv zeta in H.
  destruct H as [qtrans H]. exists qtrans.
  repnd.
  split;[split;assumption|].
  match goal with
  [|- ?l ≤ _] => assert (l [=] l [+] [0] [*] (Q2R(qtrans -mt2)%Q))
        as Heq by ring
  end.
  rewrite <- inj_Q_Zero in Heq.
  rewrite Heq. clear Heq.
  assert ({X rotOrigininPos} mt3[-]{X rotOrigininPos} mt2
          [=]
          ({X rotOrigininPos} mt3[-]{X rotOrigininPos} qtrans)
          [+]({X rotOrigininPos} qtrans [-]{X rotOrigininPos} mt2))
     as Heq by (unfold cg_minus; ring).
  rewrite Heq. clear Heq.
  assert ((mt2 + reacTime < mt3)%Q) 
    as Hassumption by (apply MotorEventsNthTimeReac; omega).
  apply plus_resp_leEq_both;
  eapply TDerivativeLBQ; eauto 2 with ICR; try lra.
Qed.

Lemma XChangeLBEv2To3_2 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  (Cos (θErrTrans + θErrTurn) 
      * (speed - transErrTrans)%Q 
      * (Ev23TimeGapLB - QT2Q reacTime))
  ≤  ({X rotOrigininPos} t3 [-] {X rotOrigininPos} t2).
Proof.
  intros ? ?.
  destruct XChangeLBEv2To3 as [qtrans Hd].
  fold t2 t3 in Hd.
  repnd.
  eapply leEq_transitive;[|apply Hdr].
  apply mult_resp_leEq_lft.
- assert (mt3-mt2-reacTime <=(mt3 - qtrans))%Q as Hle by lra.
  apply (inj_Q_leEq IR) in Hle.
  eapply leEq_transitive;[|apply Hle].
  rewrite inj_Q_minus.
  unfoldMC.
  autounfold with IRMC.
  unfold Q2R.
  rewrite inj_Q_inv.
  apply minus_resp_leEq.
  apply MotorEv23GapLB.
- apply mult_resp_nonneg; eauto 1 with ICR;[].
  apply injQ_nonneg. simpl. assumption.
Qed.

Lemma Liveness :
  ∃ (ts : QTime), ∀ (t : QTime), 
      ts < t → (|(posAtTime t) - targetPosR|) ≤ cast Q IR acceptableDist.
Abort.

End iCREATECPS.
End RobotProgam.


Definition rotSpeedRadPerSec : Qpos := QposMake 1 2.

Definition speedMetresPerSec : Qpos := QposMake 1 10.

Definition anglePrecRadPerSec : Qpos := QposMake 1 100.

Definition distPrecRadPerSec : Qpos := QposMake 1 100.

Definition distSec : Qpos := QposMake 5 1.

Definition robotProgramInstance : Cart2D Q → list (Q ** Polar2D Q) :=
  robotPureProgam 
          rotSpeedRadPerSec 
          speedMetresPerSec
          anglePrecRadPerSec
          distPrecRadPerSec
          distSec.

Definition target1Metres := {|X:= - Qmake 1 2 ; Y:=  - Qmake 1 2|}.

Definition microSeconds (q : Q) : Z :=
Zdiv ((Qnum q) * 100) (Qden q).

Definition approxTime (lm: list (Q ** Polar2D Q)) : list (Z ** Polar2D Q) := 
map (λ p, ((microSeconds (fst p)), snd p)) lm.

Lemma trial1 : approxTime (robotProgramInstance target1Metres) ≡ [].
vm_compute.
Abort.

