Definition sin1 (T:Type) :=
  {x:T | forall  y:T, x=y }.

Definition sin2 (T:Type) :=
  {_:T | forall x y:T, x=y }.

Lemma sin21 :
forall T, sin2 T -> sin1 T.
unfold sin2, sin1. intros T hs.
destruct hs as [x hs].
exists x.
auto.
Qed.

Lemma sin12 :
forall T, sin1 T -> sin2 T.
unfold sin2, sin1. intros T hs.
destruct hs as [x hs].
exists x.
congruence.
Qed.

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

Definition initialVel : (Polar2D Q) := {|rad:=0; θ:=0|}.

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

  initPos:  ({X position} 0) ≡ 0 ∧ ({Y position} 0) ≡ 0;
  initTheta:  ({theta} 0) ≡ 0;
  initTransVel : ({transVel} 0) ≡ (rad initialVel);
  initOmega : ({omega} 0) ≡ (θ initialVel)
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

Variable reacTime : QTime.
(** It is more sensible to change the type o [QNonNeg]
    as the value certainly does not represent time.
    However, the coercion QT2Q does not work then *)
Variable tVelPrec : Q → QTime.
Variable omegaPrec : Q → QTime.

Variable tVelPrec0 : tVelPrec 0 ≡ 0.
Variable omegaPrec0 : omegaPrec 0 ≡ 0.
  
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
  (t : QTime) : ((Polar2D Q) × QTime) :=
  lastPayloadAndTime VELOCITY (localEvts MOVABLEBASE) t initialVel.


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
    (tVelPrec (rad lastVelCmd))
  ∧ 
  changesTo 
    (omega robot) 
    lastTime uptoTime 
    (θ lastVelCmd) 
    reacTime 
    (omegaPrec (θ lastVelCmd)).

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
  (∀ t: QTime, corrSinceLastVel evs t robot)
  ∧ ∀ n:nat, isDeqEvtOp (evs n).


Definition PureSwProgram:
  PureProcWDelay TARGETPOS VELOCITY:=
  robotPureProgam.

Definition SwProcess 
      : Process Message (list Message):= 
  mkPureProcess (delayedLift2Mesg (PureSwProgram)).

Variable procTime : QTime.
Variable sendTimeAcc : Qpos.
Require Import CoRN.model.metric2.Qmetric.

Definition qtball : Q → Q → Prop :=
  (ball sendTimeAcc).

Notation "a ≊t b" := (qtball  a b) (at level 100).

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

Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" := 
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e ≡ (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof. auto. Qed.

Ltac show_hyp H :=
  apply ltac_something_show in H.

Ltac hide_hyp H :=
  apply ltac_something_hide in H.


Ltac show_hyps :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Ltac Replace T :=
assert T as Heq by reflexivity; rewrite Heq; clear Heq.

Ltac ReplaceH T H :=
assert T as Heq by reflexivity; rewrite Heq in H; clear Heq.

Hint Resolve derivRot  derivX derivY initPos initTheta initTransVel initOmega: ICR.
Hint Resolve qtimePos : ROSCOQ.

Instance Plus_instance_QTime : Plus QTime := Qtadd.

Open Scope nat_scope.

Lemma deqSingleMessage2 : forall evD,
  isDeqEvt evD
  -> (deqMesg evD ≡ Some (eMesg evD)).
Proof.
  intros ? Hd.
  unfold isDeqEvt in Hd.
  unfold deqMesg. destruct (eKind evD); try (inversion Hd; fail);[].
  eexists; eauto.
Defined.

Lemma moveMapInsideSome : forall tp lm,
  opBind (getPayload tp)  (Some lm)
  ≡ (getPayloadR tp) (fst lm).
Proof.
  intros ?. destruct lm; reflexivity.
Qed.


Hint Unfold π₁ ProjectionFst_instance_prod : π₁.

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
  rewrite deqSingleMessage2;[| assumption].
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

Definition decAuto :  ∀ (P: Prop) `{Decision P},
  (if decide P then True else False) -> P.
  intros ? ? Hd.
  destruct (decide P); tauto.
Defined.

Close Scope nat_scope.

(** Also, this is the way 0 is defined for CR *)

Instance Zero_Instace_IR_better : Zero IR := inj_Q IR 0.

Lemma correctVelTill0:
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
    correctVelDuring initialVel (mkQTime 0 I) t0 icreate.
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
      → ({omega icreate} t = 0 ∧ {theta icreate} t = {theta icreate} 0).
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
  ReplaceH ((θ initialVel) ≡ 0)%Q Hc.
  rewrite omegaPrec0 in Hc.
  exact Hc.
Qed.

Lemma TContRMult : ∀ (f g : TContR) t,
  ({f [*] g} t) = {f} t [*] {g} t.
Proof.
  intros.
  reflexivity.
Qed.

Hint Rewrite TContRMult : TContRIn.
  
Lemma IR_mult_zero_left : ∀ (x : IR), 0[*]x[=]0.
  intros x.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  apply cring_mult_zero_op.
Qed.

  
Lemma TransVelPosAtEV0 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  ∀ (t : QTime),  t ≤ t0
      → ({transVel icreate} t = 0 ∧ (posAtTime t) = (posAtTime 0)).
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
  ReplaceH ((rad initialVel) ≡ 0)%Q Hc.
  rewrite tVelPrec0 in Hc.
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
    (F':=(transVel icreate[*]CFCos (theta icreate)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite TContRMult, Hd0; [| lra].
  rewrite IR_mult_zero_left.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero. reflexivity.

- apply TDerivativeEqQ0 with 
    (F':=(transVel icreate[*]CFSine (theta icreate)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite TContRMult, Hd0; [| lra].
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
  correctVelDuring requestedVel t0 t1 icreate.
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
  



Lemma TransVelPosAtEV1 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
  ∀ (t : QTime),  t0 ≤ t ≤ t1
      → ({transVel icreate} t = 0 ∧ (posAtTime t) = (posAtTime 0)).
Proof.
  intros ? ? ? Hle.
  unfold le, Le_instance_QTime in Hle.
  pose proof correctVel0to1 as Hc.
  simpl in Hc. fold t0 in Hc.
  unfold correctVelDuring in Hc.
  apply proj1 in Hc. simpl rad in Hc.
  unfold zero, stdlib_rationals.Q_0 in Hc.
  rewrite tVelPrec0 in Hc.
  pose proof (qtimePos t) as Hqt.
  pose proof (λ ww, changesToDeriv0Deriv _ _ _ _  ww Hc) as H1d.
  fold t1 in H1d.
  pose proof TransVelPosAtEV0 as H0d.
  simpl in H0d. fold t0 in H0d.
  specialize (H0d t0). unfold le, Le_instance_QTime in H0d.
  repnd.
  DestImp H0d; [|lra].
  repnd. 
  rewrite H0dl in H1d.
  DestImp H1d;[|lra].
  DestImp H1d;[|reflexivity].
  split; [apply H1d; lra|].
  rewrite <- H0dr.
  unfold posAtTime, equiv, EquivCart.
  simpl.
  split.
- apply TDerivativeEqQ0 with 
    (F':=(transVel icreate[*]CFCos (theta icreate)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite TContRMult, H1d;
    [| lra].
  rewrite IR_mult_zero_left.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero. reflexivity.

- apply TDerivativeEqQ0 with 
    (F':=(transVel icreate[*]CFSine (theta icreate)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite TContRMult, H1d; [| lra].
  rewrite IR_mult_zero_left.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero. reflexivity.
Qed.

Definition optimalTurnAngle : IR :=
  CRasIR (θ (Cart2Polar targetPos)).

Definition turnAcc : IR.
Admitted.

Lemma QTimeLeRefl : ∀ {t : QTime},
  t ≤ t.
intros.
unfold le, Le_instance_QTime; lra.
Qed.

Lemma IR_inv_Qzero:
    ∀ (x : IR), x[-]0[=]x.
Proof.
  intros.
  unfold zero, Zero_Instace_IR_better.
  rewrite inj_Q_Zero.
  apply  cg_inv_zero.
Qed.

Lemma QAbsQSign : 
  ∀ a c, |QSign a c| = |c|.
Proof.
  intros.
  unfold QSign, CanonicalNotations.norm,
  NormSpace_instance_Q.
  destruct (decide (a < 0)) as [Hd | Hd]; auto.
  apply Qabs.Qabs_opp.
Qed.

  

Instance Proper_Qeq_Inj_Q :
  Proper (Qeq ==> @st_eq IR) (inj_Q IR).
Proof.
  intros a b Hab.
  apply inj_Q_wd.
  auto.
Qed.

Ltac InjQRingSimplify :=
  unfold Q2R, Z2R; autorewrite with QSimpl;
let H99 := fresh "HSimplInjQ" in
let H98 := fresh "HSimplInjQ" in
match goal with
[|- context [inj_Q _ ?q]] => pose proof (Qeq_refl q) as H99;
                            ring_simplify in H99;
                            match type of H99 with
                            | (?qn == _)%Q => 
                             assert (q == qn)%Q as H98 by ring;
                             rewrite H98; clear H99; clear H98
                            end
end.

Lemma QabsQpos : ∀ (qp: Qpos),
   ((Qabs.Qabs qp) == qp)%Q.
  intros.
  destruct qp; simpl.
  rewrite Qabs.Qabs_pos; lra.
Qed.

Lemma QeqQle : ∀ x y,
  Qeq x y -> Qle x y.
Proof.
  intros ? ?  Hq.
  rewrite Hq.
  reflexivity.
Qed.

Lemma MotorEv01Gap :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
  let tgap :Q := ((|approximate (polarTheta targetPos) anglePrec|)
                * (Qinv rotspeed)) in
   |QT2Q t1 - QT2Q t0 -  tgap| 
  ≤ 2 * (sendTimeAcc + delivDelayVar)%Q.
Proof.
  intros ? ? ?.
  unfold MotorEventsNthTime, MotorEventsNth in t0, t1.
  destruct (MotorEvents2 0 (decAuto (0<4)%nat I)) as [evStartTurn  H0m].
  simpl in t0.
  destruct (MotorEvents2 1 (decAuto (1<4)%nat I)) as [evStopTurn  H1m].
  simpl in t1.
  repeat (apply proj2 in H1m).
  repeat (apply proj2 in H0m).
  autounfold with π₁ in H0m, H1m.
  unfold minDelayForIndex, roscore.delay, Basics.compose in H0m, H1m.
  simpl in H1m, H0m.
  unfold zero, stdlib_rationals.Q_0 in H1m, H0m.
  ring_simplify in H1m.
  ring_simplify in H0m.
  unfold cast, nonneg_semiring_elements.NonNeg_inject in tgap.
  unfold dec_recip, stdlib_rationals.Q_recip in H1m.
  idtac. unfold CanonicalNotations.norm in tgap.
  unfold CanonicalNotations.norm in H1m.
  fold tgap in H1m.
  remember tgap as tdiff.
  subst tgap.
  apply Qball_opp in H0m.
  pose proof (Qball_plus H0m H1m) as Hs.
  clear H0m H1m.
  ring_simplify in Hs.
  apply Qball_Qabs in Hs.
  rewrite Qabs.Qabs_Qminus in Hs.
  unfoldMC.
  match goal with
  [H: (_ <= ?r)%Q |- (_ <= ?rr)%Q] => 
    assert (r == rr)%Q as Hrw by (simpl; ring)
   end.
  rewrite Hrw in Hs.
  eapply Qle_trans; [| apply Hs].
  apply QeqQle.
  unfold CanonicalNotations.norm, NormSpace_instance_Q.
  apply Qabs.Qabs_wd.
  fold t0. 
  fold t1. 
  simpl.
  ring.
Qed.

Lemma QmultOverQminusR : ∀ a b c : Q,
  ((a - b) * c == a * c - b * c)%Q.
Proof.
  intros ? ? ?.
  ring.
Qed.


Lemma foldQminus : ∀ a b : Q,
  (a + - b == (a - b) )%Q.
Proof.
  intros ? ?. reflexivity.
Qed.


Lemma OmegaThetaPosAtEV1 :
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
     |{theta icreate} t1 - optimalTurnAngle| ≤ turnAcc.
Proof.
  intros ? ?.
  pose proof correctVel0to1 as Hc.
  simpl in Hc. fold t0 in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc. simpl θ in Hc.
  fold t1 in Hc.
  match type of Hc with
  context[changesTo _ _ _ (Q2R ?nv) _ (QT2Q ?om)]
    => remember om as opr;
       remember nv as newVal
  end.
  assert ((t0 + reacTime < t1)%Q) 
    as Hassumption by admit.
  pose proof (qtimePos reacTime) as H99.
  pose proof (OmegaThetaAtEV0 t0 QTimeLeRefl) as Ht0.
  repnd.
  apply changesToDerivInteg2
    with (F:=(theta icreate)) (oldVal:=0) in Hc;
    eauto with ICR.
  rewrite initTheta in Ht0r.
  rewrite Ht0r in Hc.
  rewrite Ht0l in Hc.
  rewrite  (AbsIR_minus 0)  in Hc .
  rewrite cg_inv_zero in Hc.
  rewrite IR_inv_Qzero in Hc.
  pose proof HeqnewVal as Habs.
  apply (f_equal Q2R) in Habs.
  apply (f_equal AbsIR) in Habs.
  unfold Q2R in Habs.
  apply seq_refl in Habs. symmetry in Habs.
  rewrite AbsIR_Qabs in Habs.
  unfold mult, stdlib_rationals.Q_mult in Habs.
  rewrite Qabs.Qabs_Qmult in Habs.
  rewrite QAbsQSign in Habs.
  unfold CanonicalNotations.norm, NormSpace_instance_Q in Habs.
  simpl Qabs.Qabs  in Habs.
  revert Habs.
  clear H99.
  InjQRingSimplify.
  intros Habs.
  rewrite <- Habs in Hc. rewrite QabsQpos in Hc.
  pose proof MotorEv01Gap as Hg.
  simpl in Hg.
  fold t0 t1 in Hg.
  apply Qmult_le_compat_r with (z:= Qabs.Qabs newVal) in Hg.
  rewrite <- Qabs.Qabs_Qmult in Hg. idtac.
  revert Hg.
  unfoldMC.
  intros Hg.
  rewrite foldQminus in Hg.
  rewrite  QmultOverQminusR in Hg.
  rewrite foldQminus in Hg.
  rewrite  HeqnewVal  in Hg at 2.
  
Lemma QAbsMultSign: forall a b : Q,
  ((Qabs.Qabs a) * / b * ((QSign a 1) * b) == a)%Q.
Admitted.
  unfold CanonicalNotations.norm, NormSpace_instance_Q in Hg.
  revert Hg.
  unfoldMC.
  intros Hg.
  rewrite QAbsMultSign in Hg.
  rewrite AbsIR_Qabs in Habs.

Abort.
 


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
