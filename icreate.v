Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)

Require Export ROSCyberPhysicalSystem.
Require Export Vector.

Definition isVecDerivativeOf 
    {n : nat} (f f' : Vector n TContR) : Type.
  revert f f'.
  induction n as [| np Hind]; intros f f';[exact unit|].
  destruct f as [fv ft].
  destruct f' as [fv' ft'].
  exact ((isDerivativeOf ft ft') × (Hind fv fv')).
Defined.
Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Export CartCR.

(** CatchFileBetweenTagsStartCreate *)

Record iCreate : Type := {
  position :> Cart2D TContR;          (* x, y co-ordinates*)
  theta : TContR;                       (* orientation *)
  transVel : TContR;             (* translation vel (along [theta]) *)
  omega : TContR;

  (** derivatives *)
  derivRot : isDerivativeOf omega theta;
  derivX : isDerivativeOf (transVel [*] (CFCos theta)) (X position);
  derivY : isDerivativeOf (transVel [*] (CFSine theta)) (Y position);

  (** Initial (at time:=0) Conditions *)  

  initPos:  ({X position} 0) = 0 ∧ ({Y position} 0) = 0;
  initTheta:  ({theta} 0) = 0
  
}.

(** CatchFileBetweenTagsEndCreate *)


Definition unitVec (theta : TContR)  : Cart2D TContR :=
  {|X:= CFCos theta; Y:=CFSine theta|}.


(** Robot is asked to go to the  [target] relative to current position.
    This function defines the list of messages that the robot will send to
    the motor so that it will go to the target position.
    [X] axis of target points towards the direction that robot will move
    and [Y] points to its left side. it might be better to make Y
    point in robot's direction. Then add 90 in cartesian <-> polar conversion. *)

Section RobotProgam.
Variables   rotspeed speed anglePrec distPrec delay : Qpos.

Instance NormSpace_instance_Q : NormSpace Q Q := Qabs.Qabs.

Definition robotPureProgam 
      (target : Cart2D Q) : list (Q × Polar2D Q):=
    let polarTarget : Polar2D CR := Cart2Polar target in
    let approxTheta : Q := approximate (θ polarTarget) anglePrec in
    let rotDirection : Q := QSign approxTheta 1 in (** +1 or -1*)
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

Variable reacTime : Q.
Variable tVelPrec : Q.
Variable omegaPrec : Q.


  
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

Variable initialVel : (Polar2D Q).
Variable initialPos : Q.

Definition lastVelAndTime
  (t : QTime) : ((Polar2D Q) × QTime) :=
  lastPayloadAndTime VELOCITY (localEvts MOVABLEBASE) t initialVel.

Definition correctVelDuring
  (lastVelCmd : (Polar2D Q)) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (robot: iCreate) :=

changesTo (transVel robot) lastTime uptoTime (rad lastVelCmd) reacTime tVelPrec 
∧ changesTo (omega robot) lastTime uptoTime (θ lastVelCmd) reacTime omegaPrec.
(** TODO : second bit of conjunction is incorrect it will force the
   orientation in [iCreate] to jump from [2π] to [0] while turning.
   changes_to is based on a notion of distance or norm. we need to generalize 
    it to use the norm typeclass and then define appropriate notion for distance
    for angles*)

Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime)
  (robot: iCreate) :=
let (lastVel, lastTime) := lastVelAndTime uptoTime in
correctVelDuring lastVel lastTime uptoTime robot.


Definition BaseMotors  : Device iCreate :=
λ (robot: iCreate) (evs : nat -> option Event) ,
  (∀ t: QTime, corrSinceLastVel evs t robot).



Definition PureSwProgram:
  PureProcWDelay TARGETPOS VELOCITY:=
  robotPureProgam.

Definition SwProcess 
      : Process Message (list Message):= 
  mkPureProcess (delayedLift2Mesg (PureSwProgram)).

Variable procTime : QTime.
Variable timingAcc : Qpos.
Require Import CoRN.model.metric2.Qmetric.

Definition qtball : Q → Q → Prop :=
  (ball timingAcc).

Notation "a ≊t b" := (qtball  a b) (at level 100).

Definition ControllerNode : RosSwNode :=
  Build_RosSwNode (SwProcess) (procTime, timingAcc).


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

Variable expectedDelay : Qpos.
Variable maxVariation : Qpos.

Instance rllllfjkfhsdakfsdakh : @RosLocType iCreate Topic Event  RosLoc _.
  apply Build_RosLocType.
  - exact locNode.
  - exact locTopics.
  - exact (λ _ _ t , ball maxVariation t (QposAsQ expectedDelay)).
Defined.

Variable acceptableDist : Q.
Variable icreate : iCreate.
Variable eo : (@PossibleEventOrder _  icreate minGap _ _ _ _ _ _ _ _ _).

Definition posAtTime (t: Time) : Cart2D IR :=
  {| X:= {X (position icreate)} t ; Y := {Y (position icreate)} t |}.

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
Theorem comp_ind_type :
  ∀ P: nat → Type,
    (∀ n: nat, (∀ m: nat, m < n → P m) → P n)
    → ∀ n:nat, P n.
Proof.
 intros P H n.
 assert (∀ n:nat , ∀ m:nat, m < n → P m).
 intro n0. induction n0 as [| n']; intros.
 omega.
 destruct (eq_nat_dec m n'); subst; auto.
 apply IHn'; omega.
 apply H; apply X.
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
            ∧ ball timingAcc
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

Lemma  nth_error_nil :
  ∀ (A : Type) (n : nat), nth_error (@nil A) n ≡ None.
Proof.
  induction n ;auto.
Qed.

Hint Rewrite nth_error_nil : Basics.


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

(** change message semantics so that message receipt 
    is at a ball near ed + deliveryTime.
    make the balls size be a parameter *)
Lemma MotorEvents :
  let resp := PureSwProgram targetPos in
  ∀ n: nat, 
      n < 4
      → {ev : Event | (isRecvEvt ev)  ∧ eLoc ev ≡ MOVABLEBASE
            ∧ eLocIndex ev ≡ n
            ∧ Some (eMesg ev) 
               ≡ nth_error
                    (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) n
            ∧ ball (timingAcc+maxVariation)
                ( eTime (projT1 SwEvents0) + expectedDelay
                     + minDelayForIndex
                         (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) 
                         n 
                     + procTime)%Q 
                (QT2Q (eTime ev)) }.
Proof.
  intros ? n Hlt.
  pose proof (SwEventsSn n Hlt) as Hsws.
  destruct Hsws as [ev Hsws]. repnd.
  pose proof (eventualDelivery eo _ Hswsrrl) as Hsend.
  destruct Hsend as [Er  Hsend]. repnd. exists Er.
  eapply SWOnlySendsToMotor in Hsendl; eauto.
  split;[trivial|].
  split;[trivial|].
Abort.
  
Lemma MotorEventsOnly4 :
  ∀ n : nat, 3 < n -> (localEvts MOVABLEBASE n) ≡ None.
Abort.

Close Scope nat_scope.

Lemma Liveness :
  ∃ (ts : QTime), ∀ (t : QTime), 
      ts < t → (|(posAtTime t) - targetPosR|) ≤ cast Q IR acceptableDist.
Abort.


(** It would be quite complicated to maintain bounds on position when both
    [omega] and [speed] are nonzero. derivative on [X position] depends on
    all of [speed] and [theta] and [omega] *)

Require Export CoRN.ftc.IntegrationRules.

(*
Lemma TBarrowPos : forall rob (a b : Time),
       CIntegral a b ((transVel rob) [*] CFCos (theta rob)) 
       [=] {X (position rob)} b [-] {X (position rob)} a.
  intros. apply TBarrow with (pItvl := I).
  apply derivX.
Qed.
*)
(** The integral is too complicated for the general case. Handle the
    case we want in the application. Given a rough estimate of current
    position (received by Vicon )and an idea about the goal, what
    message should we send to iCreate? what can we prove
    about how the robot will react to that message? *)


(** for rotation, it is easy. for the change of position, we can bound
    Cos and Sin by 1 and hence the maximal change in X/Y coordinate per second
      is [tVelPrec] *)

(** For translation. things are complicated. Ideally, done in the frame from
    robot's position which is still not well known, such that the Y axis is
    in the direction of the target. *)

(** It seems that [CoRN.ftc.IntegrationRules.IntegrationBySubstition] would be
    useful. however, the head of the integral is a multiplication and only then
    we have a composition in the RHS of the multiplication *)
End iCREATECPS.
End RobotProgam.
