Require Export Coq.Program.Tactics.
Require Export LibTactics.

Require Export CPS.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Variable initialVel : Q.
Variable initialPos : Q.


Record Train : Type := {
  posX :> TContR;
  velX : TContR;
  deriv : isDerivativeOf velX posX;
    (** this probably already implies continuity, which is now
        explicitly put in TContR *)
  initVel : {velX} (mkQTime 0 I)  = initialVel;
  initPos : {posX} (mkQTime 0 I)  = initialPos
}.


Inductive Topic :=  MOTOR | PSENSOR.

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.



(** When adding a nrew topic, add cases of this function *)
Definition topic2Type (t : Topic) : Type :=
match t with
| MOTOR => Q
| PSENSOR => bool
end.


Instance  ttttt : @TopicClass Topic _.
  constructor. exact topic2Type.
Defined.

Definition left := false.
Definition right := true.

Inductive RosLoc := 
 BASEMOTOR | PROXSENSOR (b:bool) | SWCONTROLLER.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.

Close Scope Q_scope.


Definition getVelM  : Message -> option Q :=
  getPayload MOTOR.

Definition getSensorSide (m : Message ) : option bool :=
  getPayload PSENSOR m.

Definition getProxSide (m : Message) : option bool :=
  getPayload PSENSOR m.

Section TrainProofs.

(** To define IO devices, we already need
    an Event type *)
Context  
  (minGap : Q)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


(** In some cases, the equations might invove transcendental 
  functions like sine, cos which can output 
  irrationals even on rational *)



Definition getVelEv (e : Event) : option Q  :=
  getRecdPayload MOTOR e.

Definition getVelOEv : (option Event) ->  option Q  :=
getRecdPayloadOp MOTOR.


Definition getVelAndTime (oev : option Event) 
    : option (Q * Event)  :=
getPayloadAndEv MOTOR oev.


Definition ProxPossibleTimeEvPair 
  (maxDelay: QTime) (side : bool)
  (t: QTime) (ev: Event) 
  :=
   (t < (eTime ev) < (t + maxDelay))%Q
  /\ (eMesg ev) = (mkImmMesg PSENSOR side).

(** [side] is just an identifier *)
Definition ProximitySensor (alertDist : Q) (maxDelay: QTime) (side : bool)
  : Device (Time -> ℝ) :=
fun  (distanceAtTime : (Time -> ℝ))
     (evs : nat -> option Event) 
  =>
    (∀ t:QTime,
       (distanceAtTime t  [<=] alertDist)
       -> ∃ n, ∃ ev,
          evs n = Some ev /\ isSendEvt ev /\
            (ProxPossibleTimeEvPair maxDelay side t) ev)
    /\
    (∀ (n: nat), 
        isSendEvtOp (evs n)
        -> ∃ t : QTime, (distanceAtTime t  [<=]  alertDist)
                /\ opLiftF (ProxPossibleTimeEvPair maxDelay side t) (evs n)).

Definition inIntervalDuring
  (interval: interval) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  Squash (forall t : QTime, ( tStart <= t <= tEnd   -> (interval) (f t)))%Q.
  
Definition isEqualDuring
  (vel: Q) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  (forall t : QTime, ( tStart <= t <= tEnd   -> (f t) [=] vel))%Q.

Variable reactionTime : Q.
Variable velAccuracy : Q.
Variable transitionValues : interval.

(*
Notation "a <== b <== c" := ((a [<=] b) /\ (b [<=] c)) 
  (at level 201,left associativity).
*)

Definition simpleBetween (b a c eps : IR) 
  := ((Min a c  [<=] b) /\ (b [<=] Max a c)).

(** This can use [core.changsTo] *)
Definition correctVelDuring
  (lastVel : Q) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (velAtTime: Time -> ℝ) :=

(exists  (qt : QTime), 
  lastTime <= qt <= (lastTime + reactionTime)
  /\ ((forall t : QTime, (qt <= t <= uptoTime -> (velAtTime t) [=] lastVel)))
  /\ (forall t : QTime, (lastTime <= t <= qt)  
          -> (simpleBetween (velAtTime t) (velAtTime lastTime) lastVel 0)))%Q.
  
Close Scope Q_scope.


(** all velocity messages whose index  < numPrevEvts .
    the second item is the time that messsage was dequed.
    last message, if any  is the outermost (head)
    Even though just the last message is needed,
    this list is handy for reasoning; it is a convenient
    thing to do induction over
 *)

Definition velocityMessages (t : QTime) :=
  (filterPayloadsUptoTime MOTOR (localEvts BASEMOTOR) t).

Definition lastVelAndTime
  (t : QTime) : (Q * QTime) :=
  lastPayloadAndTime MOTOR (localEvts BASEMOTOR) t initialVel.



Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime) 
  (velAtTime: Time -> ℝ) :=
  let (lastVel, lastTime) := lastVelAndTime uptoTime in
  correctVelDuring lastVel lastTime uptoTime velAtTime.


Definition SlowMotorQ 
   : Device (Time -> ℝ) :=
fun  (velAtTime: Time -> ℝ) (evs : nat -> option Event) 
  => forall t: QTime, corrSinceLastVel evs t velAtTime.

(** it is a pure function that repeatedly
   reads a message from the [PSENSOR] topic
   and publish on the [MOTOR] *)
Definition SwControllerProgram (speed : Q):
  SimplePureProcess PSENSOR MOTOR :=
fun side  => match side with
            | true => (-speed)%Q
            | false => speed
            end.

Lemma SPP : SimplePureProcess PSENSOR MOTOR
            = (bool -> Q).
Proof.
reflexivity.
Qed.

Definition SwProcess (speed : Q) 
      : Process Message (list Message):= 
  mkPureProcess (liftToMesg (SwControllerProgram speed)).

Definition digiControllerTiming  : 
  QTime :=  (mkQTime (1#2)%Q I).
 
Definition ControllerNode (speed : Q): RosSwNode :=
  Build_RosSwNode (SwProcess speed) (digiControllerTiming, (QposMake 1 3)).

Require Import Psatz.

Lemma onlyNeededForOldProofsAux:
  ∀ sp nd ns si,
     possibleDeqSendOncePair2 (procOutMsgs (ControllerNode sp) 
        (localEvts SWCONTROLLER) nd) 
         (procTime (ControllerNode sp))
        (timingAcc (ControllerNode sp)) (localEvts SWCONTROLLER) nd ns si
  -> {es : Event | {ed : Event | isDeqEvt ed × isSendEvt es
          × (nd < ns)
              × (eTime es < eTime ed + 1)%Q
        ×
        localEvts SWCONTROLLER nd = Some ed 
        × localEvts SWCONTROLLER ns = Some es ×
         {dmp : bool|  fst (eMesg ed) = ((mkMesg PSENSOR dmp))
                  ∧ (mkImmMesg MOTOR ((SwControllerProgram sp) dmp)) = (eMesg es) }}}.
Proof.
  intros ? ? ? ? Hp.
  unfold possibleDeqSendOncePair2 in Hp.
  unfold procOutMsgs in Hp.
  simpl in Hp. unfold SwProcess in Hp. 
  rewrite getNewProcLPure in Hp.
  destruct (localEvts SWCONTROLLER nd) as [evd|];[| tauto].
  destruct (localEvts SWCONTROLLER ns) as [evs|];[| tauto].
  unfold isDeqEvt, isSendEvt.
  exists evs. exists evd.
  destruct (eKind evd); try tauto.
  destruct (eKind evs); try tauto.
  split; auto.
  split; auto.
  repnd.
  split;[omega|].
  unfold getDeqOutput2, getOutput, liftToMesg in Hprrr, Hprrl.
  simpl in Hprrr, Hprrl.
  remember (getPayload PSENSOR (eMesg evd)) as evdp.
  destruct evdp
      as [dmp|];[| rewrite nth_error_nil in Hprrl; discriminate].
  destruct si; simpl in Hprrl
    ;[| rewrite nth_error_nil in Hprrl; discriminate].
  rewrite <-Hprl in Hprrr.
  unfold mkImmMesg, minDelayForIndex in Hprrr.
  unfold compose, fold_right in Hprrr.
  simpl in Hprrr.
  apply proj1 in Hprrr.
  simpl in Hprrr.
  unfold inject_Z in Hprrr.
  split; [lra|].
  split; auto.
  split; auto.
  exists dmp.
  unfold value in Hprrl.
  inverts Hprrl.
  split; auto.
  apply MsgEta; auto.
Qed.

Ltac repnd2 :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] =>
            let lname := fresh H "l" in 
            let rname := fresh H "r" in 
              destruct H as [lname rname]
           | [ H : _ × _ |- _ ] =>
            let lname := fresh H "l" in 
            let rname := fresh H "r" in 
              destruct H as [lname rname]
         end.

Lemma onlyNeededForOldProofs:
  ∀ sp nd ns si,
     possibleDeqSendOncePair2 (procOutMsgs (ControllerNode sp) 
        (localEvts SWCONTROLLER) nd) 
         (procTime (ControllerNode sp))
        (timingAcc (ControllerNode sp)) (localEvts SWCONTROLLER) nd ns si
  -> {es : Event | {ed : Event | isDeqEvt ed × isSendEvt es
          × (nd < ns)
              × (eTime ed < eTime es < eTime ed + 1)%Q
        ×
        localEvts SWCONTROLLER nd = Some ed 
        × localEvts SWCONTROLLER ns = Some es ×
         {dmp : bool|  fst (eMesg ed) = ((mkMesg PSENSOR dmp))
                  ∧ (mkImmMesg MOTOR ((SwControllerProgram sp) dmp)) = (eMesg es) }}}.
Proof.
  intros ? ? ? ? Hp.
  apply onlyNeededForOldProofsAux in Hp.
  destruct Hp as [es Hp].
  destruct Hp as [ed Hp].
  exists es.
  exists ed.
  repnd2.
  dands; try assumption;[].
  apply timeIndexConsistent.
  apply locEvtIndex in Hprrrrrl.
  apply locEvtIndex in Hprrrrl.
  repnd.
  congruence.
Qed.


Lemma VelPosUB :forall (tst : Train)
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   (forall (t:Time), (clcr ta tb) t -> ({velX tst} t) [<=] c)
   -> ({posX tst} tb[-] {posX tst} ta)[<=]c[*](tb[-]ta).
Proof.
  intros. apply TDerivativeUB2 with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Lemma VelPosLB :forall (tst : Train)
   (ta tb : Time) (Hab : ta[<]tb) (c : ℝ),
   (forall (t:Time), (clcr ta tb) t -> c [<=] ({velX tst} t))
   -> c[*](tb[-]ta)[<=] ({posX tst} tb[-] {posX tst} ta).
Proof.
  intros. apply TDerivativeLB2 with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Lemma QVelPosUB :forall (tst : Train)
   (ta tb : QTime) (Hab : (ta<=tb)%Q) (c : Q),
   (forall (t:QTime), (ta <= t <= tb)%Q -> ({velX tst} t) [<=] c)
   -> (({posX tst} tb[-] {posX tst} ta)[<=] c*(tb-ta))%Q.
Proof.
  intros. unfold Q2R.
  rewrite inj_Q_mult.
  apply TDerivativeUBQ with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Lemma QVelPosLB :forall (tst : Train)
   (ta tb : QTime) (Hab : (ta<=tb)%Q) (c : Q),
   (forall (t:QTime), (ta <= t <= tb)%Q -> Q2R c [<=] ({velX tst} t))
   -> Q2R (c*(tb-ta))[<=] ({posX tst} tb[-] {posX tst} ta).
Proof.
  intros. unfold Q2R.
  rewrite inj_Q_mult.
  apply TDerivativeLBQ with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Variable boundary : ℝ.

Definition rboundary : ℝ := (boundary).
Definition lboundary : ℝ := ([0] [-] boundary).

Variable alertDist : Q.
Variable safeDist : ℝ.
Variable maxDelay : QTime.
Variable hwidth : ℝ. (* half of width *)
Definition speed : Q := 1.


Variable reactionTimeGap : (reactionTime < minGap)%Q.
Definition lEndPos (ts : Train) (t : Time) : ℝ :=
  (getF (posX ts) t [-]  hwidth).

Definition rEndPos (ts : Train) (t : Time) : ℝ :=
  (getF (posX ts) t [+]  hwidth).

Definition velAtTime (ts : Train) (t : Time) : ℝ :=
  (getF (velX ts) t).

Definition centerPosAtTime (ts : Train) (t : Time) : ℝ :=
  (getF (posX ts) t).

Definition velBound : interval :=
  (nbdAround [0] (speed [+] velAccuracy)).

Definition transitionInterval : interval :=
  velBound.


Definition proxView (side :bool) :=
match side with
| true => (fun ts t => (rboundary [-] (rEndPos ts t)))
| false => (fun ts t => ((lEndPos ts t) [-] lboundary))
end.


Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| BASEMOTOR => DeviceSemantics (fun ts => getF (velX ts)) SlowMotorQ
| PROXSENSOR  side=> DeviceSemantics
                      (proxView side)
                      (ProximitySensor alertDist maxDelay side)
| SWCONTROLLER => SwSemantics (ControllerNode speed)
end.


Definition locTopics (rl : RosLoc) : TopicInfo :=
match rl with
| BASEMOTOR => ((MOTOR::nil), nil)
| PROXSENSOR _ => (nil, (PSENSOR::nil))
| SWCONTROLLER => ((PSENSOR::nil), (MOTOR::nil))
end.

Instance rllllfjkfhsdakfsdakh : @CPS Train Topic Event  RosLoc _.
  apply Build_CPS.
  - exact locNode.
  - exact locTopics.
  - exact (fun srs dest del => (del <  1)%Q ).
Defined.



Variable tstate : Train.
Variable eo : (@CPSExecution _  tstate minGap _ _ _ _ _ _ _ _ _).

Definition  TrainSpec (t:Time) : Prop :=
    ((lEndPos tstate t) [-] safeDist [>=] lboundary )
    /\((rEndPos tstate t) [+] safeDist [<=] rboundary ).

Definition motorEvents : nat -> option Event 
   := localEvts BASEMOTOR.

Lemma QPositionLe :forall (tst : Train)
   (ta tb : QTime) (Hab : (ta<=tb)%Q),
   (forall (t:QTime), (ta <= t <= tb)%Q -> ({velX tst} t) [<=] 0)
   -> ({posX tst} tb[<=] {posX tst} ta).
Proof.
  intros ? ? ? ?  Hq.
  apply QVelPosUB in Hq; auto.
  unfold Q2R in Hq.
  rewrite inj_Q_mult in Hq.
  rewrite inj_Q_Zero in Hq.
  rewrite cring_mult_zero_op in Hq.
  apply shift_leEq_plus in Hq.
  rewrite cm_lft_unit_unfolded in Hq.
  trivial.
Qed.

Lemma QPositionGe :forall (tst : Train)
   (ta tb : QTime) (Hab : (ta<=tb)%Q),
   (forall (t:QTime), (ta <= t <= tb)%Q -> Q2R 0 [<=] ({velX tst} t))
   -> ({posX tst} ta[<=] {posX tst} tb).
Proof.
  intros ? ? ? ?  Hq.
  apply QVelPosLB in Hq; auto.
  unfold Q2R in Hq.
  rewrite inj_Q_mult in Hq.
  rewrite inj_Q_Zero in Hq.
  rewrite cring_mult_zero_op in Hq.
  apply shift_plus_leEq in Hq.
  rewrite cm_lft_unit_unfolded in Hq.
  trivial.
Qed.

Lemma QPositionGeIf :forall (tst : Train) (c : IR)
   (ta tb : QTime) (Hab : (ta<=tb)%Q),
   (forall (t:QTime), (ta <= t <= tb)%Q -> ({velX tst} t) [<=] 0)
   -> c [<=] {posX tst} tb
   -> c [<=] {posX tst} ta.
Proof.
  intros ? ? ? ? ? Hq Hc.
  apply QPositionLe in Hq; auto.
  eauto using leEq_transitive.
Qed.

Lemma QPositionLeIf :forall (tst : Train) (c : IR)
   (ta tb : QTime) (Hab : (ta<=tb)%Q),
   (forall (t:QTime), (ta <= t <= tb)%Q -> 0 [<=] ({velX tst} t))
   -> {posX tst} tb  [<=] c
   -> {posX tst} ta  [<=] c.
Proof.
  intros ? ? ? ? ? Hq Hc.
  apply QPositionGe in Hq; auto.
  eauto using leEq_transitive.
Qed.



(** need to force deque events to happen
    and also within acceptable time.
    right now, the motor can disregard
    all messages *)

Close Scope Q_scope.


Lemma DeqSendOncePair : forall ns nd sp,
  possibleDeqSendOncePair (ControllerNode sp) (localEvts SWCONTROLLER) nd ns
  -> {es : Event | {ed : Event | isDeqEvt ed × isSendEvt es
          × (nd < ns)
              × (eTime ed < eTime es < eTime ed + digiControllerTiming)%Q
        ×
        localEvts SWCONTROLLER nd = Some ed 
        × localEvts SWCONTROLLER ns = Some es ×
         {dmp : bool|  fst (eMesg ed) = ((mkMesg PSENSOR dmp))
                  ∧ (mkImmMesg MOTOR ((SwControllerProgram sp) dmp)) = (eMesg es) }}}.
Proof.
  intros ? ? ? Hnc.
  apply PureProcDeqSendOncePair in Hnc.
  simpl in Hnc.
  destruct Hnc as [es Hnc].
  destruct Hnc as [ed Hnc].
  exists es. exists ed.  simpl.
  exrepd. 
  pose proof (noSpamRecv eo _ a) as Hvr.
  dands; trivial.
  rewrite <- locEvtIndex in e.
  TrimAndRHS e. rewrite e in Hvr.
  simpl in Hvr. 
  specialize (s Hvr). clear Hvr. trivial.
Abort.

(*
Lemma DeqSendOncePair2 : forall ns nd sp,
  possibleDeqSendOncePair2 (ControllerNode sp) 
    (localEvts SWCONTROLLER) nd ns

  -> {es : Event | {ed : Event | isDeqEvt ed × isSendEvt es
          × (nd < ns)
              × (eTime ed < eTime es < eTime ed + 1)%Q
        ×
        localEvts SWCONTROLLER nd = Some ed 
        × localEvts SWCONTROLLER ns = Some es ×
         {dmp : bool|  fst (eMesg ed) = ((mkMesg PSENSOR dmp))
                  ∧ (mkImmMesg MOTOR ((SwControllerProgram sp) dmp)) = (eMesg es) }}}.
Proof.
  intros ? ? ? Hnc.
  apply PureProcDeqSendOncePair in Hnc.
  simpl in Hnc.
  destruct Hnc as [es Hnc].
  destruct Hnc as [ed Hnc].
  exists es. exists ed.  simpl.
  exrepd. 
  pose proof (noSpamRecv eo _ a) as Hvr.
  dands; trivial.
  rewrite <- locEvtIndex in e.
  TrimAndRHS e. rewrite e in Hvr.
  simpl in Hvr. 
  specialize (s Hvr). clear Hvr. trivial.
Qed.
*)

Lemma swControllerMessages : 
  forall es : Event,
  SWCONTROLLER = eLoc es
  -> isSendEvt es
  -> {(eMesg es) = (mkImmMesg MOTOR speed)}
      + {(eMesg es) = (mkImmMesg MOTOR (-speed))%Q}.
Proof.
  intros es Hsw Hsend.
  pose proof (locEvtIndex 
                SWCONTROLLER 
                (eLocIndex es) 
                es) as Hiff.
  TrimAndRHS Hiff.
  symmetry in Hsw.
  specialize (Hiff (conj Hsw eq_refl)).
  pose proof (corrNodes 
                  eo 
                  SWCONTROLLER 
                  (eLocIndex es)) as Hnc.
  rewrite Hiff in Hnc.
  TrimAndRHS Hnc. unfold isSendEvtOp in Hnc.
  simpl in Hnc.
  specialize (Hnc Hsend). destruct Hnc as [mDeq  Hnc].
  destruct Hnc as [si Hnc].
  unfold procTime, digiControllerTiming,
  timingAcc, compose in Hnc. simpl in Hnc.
  unfold digiControllerTiming in Hnc.
  simpl in Hnc.
  apply onlyNeededForOldProofs in Hnc.
  simpl in Hnc. exrepd. 
  rewrite  e0 in Hiff. inversion Hiff as [Heq]. clear Hiff.
  subst. unfold mkImmMesg. unfold mkMesg in H2.
  destruct dmp;[right | left]; symmetry; apply H2.
Qed.


Lemma velMessages:
  forall n : nat,
     match getVelOEv (motorEvents n) with
     | Some v => {v = speed} + {v = (-speed)%Q}
     | None => True
     end.
Proof.
  intros n.
  unfold motorEvents,getVelOEv, getRecdPayloadOp, getRecdPayload.
  remember (localEvts BASEMOTOR n)  as oev.
  destruct oev as [ ev| ]; simpl; [| auto; fail].
  remember (deqMesg ev)  as om.
  destruct om as [ sm| ]; simpl; [| auto; fail].
  pose proof Heqom as Hem.
  apply deqSingleMessage2  in Hem.
  apply deqIsRecvEvt in Heqom.
  
  (** someone must have sent this message
      which is contained in the receive (enque)
      event evEnq. let the sent message
      be [sm] and the corresponding event be [es] *)
  pose proof (recvSend eo _ Heqom) as Hrecv.
  repnd.
  destruct Hrecv as [es Hrecv].
  pose proof (proj2 (proj2 Hrecv)) as Hsend.
  TrimAndRHS Hrecv.
  unfold PossibleSendRecvPair in Hrecv.
  simpl in Hrecv.
  repnd. symmetry in Heqoev. 
  apply locEvtIndex in Heqoev.
  repnd. rewrite Heqoevl in Hrecvrl.
  (** since [BASEMOTOR] only receives on [MOTOR]
      topic, the message [sm] must have that topic *)
  unfold validRecvMesg in Hrecvrl.
  simpl in Hrecvrl.
  rewrite <- Hem in Hrecvrl.
  rewrite RemoveOrFalse in Hrecvrl.
  unfold validSendMesg in Hrecvrrl.
  unfold mtopic in Hrecvrrl.
  simpl. simpl. simpl. simpl in Hrecvrrl.
  rewrite Hrecvl in Hrecvrrl.
  remember (eLoc es) as sloc.
  rewrite <- Hem in Hrecvrrl.
  unfold mtopic in Hrecvrl.
  simpl in Hrecvrl.
  rewrite <- Hrecvrl in Hrecvrrl.
  (** Only [SWCONTROLLER] sends on that topic *)
  destruct sloc; simpl in Hrecvrrl;
  try rewrite RemoveOrFalse in Hrecvrrl.
    try contradiction;
    try discriminate.

  discriminate.
  clear Hrecvrrl.
  apply swControllerMessages in Hsend;
    [| trivial].
  destruct Hsend as [Hsend | Hsend];
  apply (f_equal (fst)) in Hsend;
  simpl in Hsend;
  rewrite Hrecvl in Hsend;
  rewrite <- Hem in Hsend;
  unfold getPayload;
  inverts Hsend as Hsend; simpl; rewrite Hsend; simpl; auto.
Qed.

Lemma  TrainVelBounded : forall (t:QTime),
   velBound (velAtTime tstate t).
Proof.
  intro t.
  pose proof (corrNodes 
                  eo 
                  BASEMOTOR t) as Hnc.
  unfold corrSinceLastVel in Hnc.
Abort.



Lemma MotorOnlyReceivesFromSw :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Er = BASEMOTOR
  -> eLoc Es = SWCONTROLLER.
Proof.
  intros ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrr.
  unfold validRecvMesg in Hsendlrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  simpl in  XXl.
  apply (f_equal ( fst)) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  rewrite Hl in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  unfold mtopic in Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  unfold mtopic in Hsendlrl.
  simpl in Hsendlrrl,Hsendlrl. rewrite <- Hsendlrl in Hsendlrrl.
  destruct (eLoc Es); simpl in Hsendlrrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

(** except the last 2 lines, the proof is same as the above *)
Lemma SwOnlyRecievesFromSensor :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Er = SWCONTROLLER
  -> {side: bool | eLoc Es = PROXSENSOR side}.
Proof.
  intros ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrr.
  unfold validRecvMesg in Hsendlrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  simpl in  XXl.
  apply (f_equal ( fst)) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  rewrite Hl in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  unfold mtopic in Hsendlrrl, Hsendlrl.
  rewrite <- XXl in Hsendlrrl.
  simpl in Hsendlrl, Hsendlrrl.
  simpl in Hsendlrrl. rewrite <- Hsendlrl in Hsendlrrl.
  destruct (eLoc Es); simpl in Hsendlrrl;
    try contradiction;
    try rewrite  RemoveOrFalse in Hsendlrrl; 
    try discriminate;
    try contradiction.
  exists b. reflexivity.
Qed.

(** Ideally, device specs should imply a bound like this.
    For a fine grained analysis, this might be less useful *)
Variable velPos : forall (t : Time), 
  Q2R (-speed) [<=] ({velX tstate} t) /\ ({velX tstate} t) [<=] speed.


Lemma centerPosChange : forall (ta tb : Time),
  ta[<]tb
  -> (centerPosAtTime tstate tb [-] centerPosAtTime tstate ta) [<=](tb[-]ta).
Proof.
  intros. unfold centerPosAtTime. rewrite <- (one_mult _ (tb[-]ta)).
  apply VelPosUB;[ trivial |].
  intros. rewrite <- inj_Q_One.
  apply velPos.
Qed.

Lemma centerPosChangeLB : forall (ta tb : Time),
  ta[<]tb
  -> (ta[-]tb) [<=] (centerPosAtTime tstate tb [-] centerPosAtTime tstate ta).
Proof.
  intros. unfold centerPosAtTime.
  rewrite <- minusInvR.
  rewrite <- mult_minus1.
  apply VelPosLB;[ trivial |].
  intros. rewrite <- inj_Q_One.
  rewrite <- inj_Q_inv.
  apply velPos.
Qed.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring RisaRing: (CRing_Ring ℝ).
Require Import Setoid.

Open Scope Q_scope.

Lemma centerPosChangeQAux : forall (ta tb : QTime),
  ((ta < tb)%Q)
  -> (centerPosAtTime tstate tb [-] centerPosAtTime tstate ta) [<=] (tb - ta).
Proof.
  intros ? ? Hlt.
  pose proof (centerPosChange ta tb) as Hcc.
  destruct ta as [qta  ap].
  destruct tb as [qtb  bp].
  lapply Hcc; [clear Hcc; intro Hcc |apply inj_Q_less;trivial].
  eapply leEq_transitive; eauto.
  trivial. unfold Q2R. rewrite inj_Q_minus. simpl. unfold Q2R. simpl.
  apply leEq_reflexive.
Qed.


(** this proof is not possible when [ta] and [tb] are
    rationals *)
Lemma centerPosChangeQ : forall (ta tb : QTime),
  (ta <= tb)%Q
  -> (centerPosAtTime tstate tb [-] centerPosAtTime tstate ta) [<=] (tb - ta).
Proof.
  intros ? ? Hlt.
  apply Qle_lteq in Hlt.
  destruct Hlt as [Hlt| Hlt].
- apply centerPosChangeQAux; trivial.
- apply (inj_Q_wd IR) in Hlt.
  unfold centerPosAtTime.
  unfold Q2R.
  rewrite inj_Q_minus. rewrite Hlt.
  apply TContRExtQ2 with (f:= posX tstate) in Hlt.
  rewrite Hlt.
  rewrite cg_minus_correct.
  rewrite cg_minus_correct.
  apply leEq_reflexive.
Qed.

Lemma centerPosChangeLBQ : forall (ta tb : QTime),
  ta < tb
  -> Q2R (ta - tb) [<=] (centerPosAtTime tstate tb [-] centerPosAtTime tstate ta).
Proof.
  intros ? ? Hlt.
  pose proof (centerPosChangeLB ta tb) as Hcc.
  destruct ta as [qta  ap].
  destruct tb as [qtb  bp].
  lapply Hcc; [clear Hcc; intro Hcc |apply inj_Q_less;trivial].
  eapply leEq_transitive; eauto.
  trivial. unfold Q2R. rewrite inj_Q_minus. simpl. unfold Q2R. simpl.
  apply leEq_reflexive.
Qed.



Lemma centerPosUB : forall (ts tf : QTime) (td : Q) (ps : ℝ),
  ts < tf < ts + td
  -> centerPosAtTime tstate ts[<=] ps
  -> centerPosAtTime tstate tf[<=] (ps [+] td).
Proof.
  intros ? ? ? ? Hint Hcs.
  repnd.
  apply qSubLt in Hintr.
  rename Hintl into Htlt.
  apply centerPosChangeQAux in Htlt.
  remember (centerPosAtTime tstate tf) as cpvt. clear Heqcpvt.
  remember (centerPosAtTime tstate ts) as cpst. clear Heqcpst.
  rename Hintr into Hqlt.
  apply inj_Q_less with (R1:=ℝ)  in Hqlt.
  unfold Q2R in Htlt.
  apply (leEq_less_trans _ _ _ _ Htlt) in Hqlt ; eauto.
  clear Htlt ts tf.
  apply less_leEq in Hqlt.
  eapply (plus_resp_leEq_both _ _ _ _ _ Hcs) in Hqlt; eauto.
  clear Hcs. rename Hqlt into hh.
  rewrite realCancel in hh.
  eapply leEq_transitive; eauto. clear hh.
  unfold Q2R. apply leEq_reflexive.
Qed.


Lemma centerPosLB : forall (ts tf : QTime) (td : Q) (ps : ℝ),
  ts < tf < ts + td
  -> ps [<=] centerPosAtTime tstate ts
  -> (ps [-] td) [<=] centerPosAtTime tstate tf.
Proof.
  intros ? ? ? ? Hint Hcs.
  repnd.
  apply qSubLt in Hintr.
  rename Hintl into Htlt.
  apply centerPosChangeLBQ in Htlt.
  remember (centerPosAtTime tstate tf) as cpvt. clear Heqcpvt.
  remember (centerPosAtTime tstate ts) as cpst. clear Heqcpst.
  rename Hintr into Hqlt.
  apply inj_Q_less with (R1:=IR)  in Hqlt.
  unfold Q2R in Htlt.
  apply inv_resp_leEq in Htlt.
  rewrite minusInvR in Htlt.
  rewrite inj_Q_minus in Htlt.
  rewrite minusInvR in Htlt.
  rewrite <- inj_Q_minus in Htlt.
  apply (leEq_less_trans _ _ _ _ Htlt) in Hqlt ; eauto.
  clear Htlt ts tf.
  apply less_leEq in Hqlt.
  apply inv_resp_leEq in Hqlt.
  rewrite minusInvR in Hqlt.
  eapply (plus_resp_leEq_both _ _ _ _ _ Hcs) in Hqlt; eauto.
  clear Hcs. rename Hqlt into hh.
  rewrite realCancel in hh.
  eapply leEq_transitive; eauto. clear hh.
  unfold Q2R. apply leEq_reflexive.
Qed.


Lemma centerPosUB2 : forall (ts tf : QTime) (td : Q) (pf: Q),
  (ts < tf < (ts + td))
  -> centerPosAtTime tstate ts[<=] (pf-td)
  -> centerPosAtTime tstate tf[<=] pf.
Proof.
  intros ? ? ? ?  Hint Hcs.
  apply centerPosUB with (td:= (td)) (tf:=tf) in Hcs; [| trivial; fail].
  eapply leEq_transitive; eauto. clear Hcs Hint.
  unfold Q2R. rewrite <- inj_Q_plus.
  apply inj_Q_leEq.
  simpl. lra.
Qed.

Lemma centerPosLB2 : forall (ts tf : QTime) (td : Q) (pf: Q),
  (ts < tf < (ts + td))
  -> Q2R (pf+td) [<=] centerPosAtTime tstate ts
  -> Q2R pf [<=] centerPosAtTime tstate tf.
Proof.
  intros ? ? ? ?  Hint Hcs.
  apply centerPosLB with (td:= (td)) (tf:=tf) in Hcs; [| trivial; fail].
  eapply leEq_transitive; eauto. clear Hcs Hint.
  unfold Q2R. rewrite <- inj_Q_minus.
  apply inj_Q_leEq.
  unfold cg_minus. simpl. lra.
Qed.

(*
Lemma centerPosUB3 : forall (ts tf td : QTime) (pf: R),
  (ts < tf < (ts + td))
  -> centerPosAtTime tstate ts[<=] (pf [-] td)
  -> centerPosAtTime tstate tf[<=] pf.
Proof.
  intros ? ? ? ?  Hint Hcs.
  apply centerPosUB with (td:= (td)) (tf:=tf) in Hcs; [| trivial; fail].
  eapply leEq_transitive; eauto. clear Hcs Hint.
  unfold Q2R. rewrite <- inj_Q_plus.
  apply inj_Q_leEq.
  simpl. lra.
Qed.
*)

Definition ConcreteValues : Prop :=
hwidth =  2 
                      /\ boundary =  100 
                      /\ alertDist =   16
                      /\ (maxDelay = mkQTime 1 I)
                      /\ (reactionTime = 1)
                      /\ (initialVel = 0)
                      /\ (initialPos = 0).

  
Variable concreteValues : ConcreteValues.

Lemma reactionTime1 : reactionTime = 1.
Proof.
  unfold ConcreteValues in concreteValues. tauto.
Qed.

Definition posVelMeg : Message :=
  (mkImmMesg MOTOR speed).

Open Scope Z_scope.

Definition MotorRecievesPositivVelAtLHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => 
            isDeqEvt ev
              -> fst (eMesg ev) = fst posVelMeg
              -> (centerPosAtTime tstate (eTime ev)) [<=]  -78
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt _ => 
                fst (eMesg ev) = fst posVelMeg
                -> (centerPosAtTime tstate (eTime ev)) [<=] -79
            | deqEvt => 
                fst (eMesg ev) = (mkMesg PSENSOR false)
                -> (centerPosAtTime tstate (eTime ev)) [<=] -80
            end
| _ => True
end.

Lemma QShiftMinus: ∀ a b c, (a - b < c -> a  <  b + c)%Q.
Proof.
  intros. lra.
Qed.


Ltac SensorMsgInvert Hmd :=
    (simpl in Hmd;
    let T:= constr:(f_equal (getPayloadR PSENSOR)) in apply T in Hmd;
    simpl in Hmd;
    apply (f_equal (fun op => opExtract op false)) in Hmd;
    simpl in Hmd).

Lemma  PosVelAtLHSAux : forall (ev : Event),
          MotorRecievesPositivVelAtLHS ev.
Proof.
  induction ev as [ev Hind] using 
    (@well_founded_induction_type Event (causedBy eo) (causalWf eo)) .
  unfold MotorRecievesPositivVelAtLHS.
  remember (eLoc ev) as evloc.
  destruct evloc; auto.

- intro Hdeqx. pose proof (recvSend eo _ Hdeqx) as Hsend.
  destruct Hsend as [Es Hsend].
  repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
  apply Hind in Hsendrl. clear Hind.
  (** topic subscrions and topology say that [Es] must have
      happened at [SWCONTROLLER] *)
  symmetry in Heqevloc.
  pose proof  (MotorOnlyReceivesFromSw _ _ 
      Hsendrr Hdeqx Hsendl Heqevloc) as Hsw.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrl Hsendlrl.
  rewrite Heqevloc in Hsendlrrr.
  rewrite Hsw in Hsendlrrr.
  simpl in Hsendlrrr.
  (** Now, lets unpack the induction hypothesis *)
  unfold MotorRecievesPositivVelAtLHS in Hsendrl.
  rewrite Hsw in Hsendrl.
  unfold isSendEvt in Hsendrr.
  destruct (eKind Es); (try inversion Hsendrr ).
  rewrite Hsendll in Hsendrl.
  parallelForall Hsendrl. clear x.
  remember (eTime ev) as evt. clear Heqevt.
  remember (eTime Es) as est. clear Heqest.
  Local Opaque Q2R.
  simpl in Hsendrl.
  apply QShiftMinus in Hsendlrrr.
  eapply centerPosUB2; try split; eauto.

- rename ev into es. remember (eKind es) as eks.
  destruct eks; [|auto].
  + symmetry in Heqeks.
    pose proof (corrNodes 
                eo 
                SWCONTROLLER 
                (eLocIndex es)) as Hnc.

    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hxx.
    TrimAndRHS Hxx. rewrite Hxx in Hnc;[| split; auto; fail].
    simpl  in Hnc. TrimAndRHS Hnc. clear Hxx.
    specialize (Hnc (isSendEvtIf Heqeks)).
    destruct Hnc as [m Hnc].
    destruct Hnc as [si Hnc].
    apply onlyNeededForOldProofs in Hnc.
    simpl in Hnc. 
    destruct Hnc as [es0 Hnc].
    destruct Hnc as [ed Hnc].
    fold (inBetween (eTime ed) (eTime es0) (eTime ed + 1)) in Hnc.
    exrepd. rename e into H4. rename e0 into H5.
    pose proof (sameLocCausal eo _ H4 H5 l) as Hcaus.
    clear l.
    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hiff.
    TrimAndRHS Hiff.
    rewrite Hiff in H5; auto;[].
    inversion H5 as [Heqs].  clear H5.
    symmetry in Heqs. subst es0. rename H0 into H7.
    rewrite <- H7. intro Heq. clear H7.
    simpl in Heq. 
    let T:= constr:(f_equal (getPayloadR MOTOR)) in 
    apply T in Heq. rename Heq into Heqq.
    simpl in Heqq. inversion Heqq as [Heq]. clear Heqq.
    unfold speed in Heq.
    destruct dmp; simpl in Heq;[inversion Heq; fail| clear Heq].
    specialize (Hind ed Hcaus). clear Hiff. clear Hcaus.
    unfold MotorRecievesPositivVelAtLHS in Hind.
    apply locEvtIndex in H4. repnd. subst m. 
    rewrite H4l in Hind. clear H4l. 
    unfold isDeqEvt in a.
    destruct (eKind ed); inversion a.
    rename H into H6.
    specialize (Hind H6). clear H6.
    unfold inBetween in i.
    clear concreteValues Heqeks Heqevloc eo reactionTimeGap transitionValues velAccuracy boundary 
      alertDist safeDist maxDelay hwidth.
    eapply centerPosUB2; eauto.

  + clear Hind. symmetry in Heqeks. rename es into ed.
    pose proof (recvSend eo ed (isDeqEvtIf Heqeks)) as Hsend.
    destruct Hsend as [Es Hsend].
    repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
    symmetry in Heqevloc.
    pose proof  (SwOnlyRecievesFromSensor _ _ 
      Hsendrr (isDeqEvtIf Heqeks) Hsendl Heqevloc) as Hsw.
    exrepd.
    unfold PossibleSendRecvPair in Hsendl.
    repnd. clear Hsendlrrl Hsendlrl.
    rewrite Heqevloc in Hsendlrrr.
    rewrite side0 in Hsendlrrr. simpl in Hsendlrrr.
    rewrite <- Hsendll. intros Hmd.
    apply QShiftMinus in Hsendlrrr.
    eapply centerPosUB2; eauto.
    clear Hsendlrrr.
    pose proof (corrNodes 
                  eo 
                  (PROXSENSOR side)) as Hnc.
    simpl in Hnc.
    unfold DeviceSemantics, ProximitySensor in Hnc.
    unfold ProxPossibleTimeEvPair in Hnc.
    TrimAndLHS Hnc.
    pose proof (locEvtIndex (PROXSENSOR side) (eLocIndex Es) Es) as Hx.
    TrimAndRHS Hx.
    specialize (Hnc (eLocIndex Es)).
    rewrite Hx in Hnc; [| auto]. clear Hx.
    simpl in Hnc.
    specialize (Hnc Hsendrr).
    destruct Hnc as [t Hnc].
    rewrite inBetweenFold in Hnc.
    repnd. unfold inBetween in Hncrl.
    eapply centerPosUB2; eauto.
    clear Hncrl.
    rewrite Hncrr in Hmd.
    SensorMsgInvert Hmd.
    subst. unfold proxView in Hncl.
    (* apply less_leEq in Hncl. *)
    (* rewrite AbsIR_minus in Hncl. *)
    (* apply AbsIR_bnd in Hncl. *)
    unfold lEndPos, lboundary in Hncl.
    pose proof concreteValues as Hcon.


Open Scope nat_scope.
    AndProjN 0 Hcon as Hhw.
    AndProjN 1 Hcon as Hbb.
    AndProjN 2 Hcon as Hal.
    AndProjN 3 Hcon as Hmd.
Close Scope nat_scope.

    unfold centerPosAtTime.
    clear Hcon. subst. clear Hmd Hal Hbb Hhw.
    remember ({posX tstate} t) as cpt.
    clear dependent t.
    clear dependent Event.
    clear concreteValues velPos tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime  alertDist minGap.
    apply shift_leEq_plus in Hncl.
    apply shift_leEq_plus in Hncl.
    eapply leEq_transitive; eauto. clear dependent cpt.
    rewrite <- inj_Q_Zero.
    Local Transparent Q2R.
    unfold Q2R, Z2R.
    rewrite <- inj_Q_minus.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_plus.
    apply inj_Q_leEq.
    simpl. unfold cg_minus. simpl.
    simpl.  unfold QT2Q.
    simpl. unfold inject_Z. simpl. lra.
Qed.

Close Scope Z_scope.

Definition negVelMeg :  Message :=
  (mkImmMesg MOTOR (-speed)).

Open Scope Z_scope.

Definition MotorRecievesNegVelAtRHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => 
            isDeqEvt ev
              -> fst (eMesg ev) = fst negVelMeg
              -> 78 [<=]  (centerPosAtTime tstate (eTime ev))
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt _ => 
                fst  (eMesg ev) =  fst negVelMeg
                -> 79 [<=] (centerPosAtTime tstate (eTime ev))
            | deqEvt => 
                fst (eMesg ev) = (mkMesg PSENSOR true)
                -> 80 [<=] (centerPosAtTime tstate (eTime ev))
            end
| _ => True
end.

Lemma  NegVelAtRHSAux : forall (ev : Event),
          MotorRecievesNegVelAtRHS ev.
Proof.
  induction ev as [ev Hind] using 
    (@well_founded_induction_type Event (causedBy eo) (causalWf eo)).
  unfold MotorRecievesNegVelAtRHS.
  remember (eLoc ev) as evloc.
  destruct evloc; auto.


- intro Hdeqx. pose proof (recvSend eo _ Hdeqx) as Hsend.
  destruct Hsend as [Es Hsend].
  repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
  apply Hind in Hsendrl. clear Hind.
  (** topic subscrions and topology say that [Es] must have
      happened at [SWCONTROLLER] *)
  symmetry in Heqevloc.
  pose proof  (MotorOnlyReceivesFromSw _ _ 
      Hsendrr Hdeqx Hsendl Heqevloc) as Hsw.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrl Hsendlrl.
  rewrite Heqevloc in Hsendlrrr.
  rewrite Hsw in Hsendlrrr.
  simpl in Hsendlrrr.
  (** Now, lets unpack the induction hypothesis *)
  unfold MotorRecievesNegVelAtRHS in Hsendrl.
  rewrite Hsw in Hsendrl.
  unfold isSendEvt in Hsendrr.
  destruct (eKind Es); (try inversion Hsendrr ).
  rewrite Hsendll in Hsendrl.
  parallelForall Hsendrl. clear x.
  remember (eTime ev) as evt. clear Heqevt.
  remember (eTime Es) as est. clear Heqest.
  Local Opaque Q2R.
  simpl in Hsendrl.
  apply QShiftMinus in Hsendlrrr.
  eapply centerPosLB2; try split; eauto.

- rename ev into es. remember (eKind es) as eks.
  destruct eks; [|auto].
  + symmetry in Heqeks.
    pose proof (corrNodes 
                eo 
                SWCONTROLLER 
                (eLocIndex es)) as Hnc.

    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hxx.
    TrimAndRHS Hxx. rewrite Hxx in Hnc;[| split; auto; fail].
    simpl  in Hnc. TrimAndRHS Hnc. clear Hxx.
    specialize (Hnc (isSendEvtIf Heqeks)).
    destruct Hnc as [m Hnc].
    destruct Hnc as [si Hnc].
    apply onlyNeededForOldProofs in Hnc.
    simpl in Hnc. 
    destruct Hnc as [es0 Hnc].
    destruct Hnc as [ed Hnc].
    fold (inBetween (eTime ed) (eTime es0) (eTime ed + 1)) in Hnc.
    exrepd. rename e into H4. rename e0 into H5.
    pose proof (sameLocCausal eo _ H4 H5 l) as Hcaus.
    clear l.
    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hiff.
    TrimAndRHS Hiff.
    rewrite Hiff in H5; auto;[].
    inversion H5 as [Heqs].  clear H5.
    symmetry in Heqs. subst es0. rename H0 into H7.
    rewrite <- H7. intro Heq. clear H7.
        let T:= constr:(f_equal (getPayloadR MOTOR)) in 
    apply T in Heq. rename Heq into Heqq.
    simpl in Heqq. inversion Heqq as [Heq]. clear Heqq.
    unfold speed in Heq.
    destruct dmp; simpl in Heq;[clear Heq| inversion Heq; fail].
    specialize (Hind ed Hcaus). clear Hiff. clear Hcaus.
    unfold MotorRecievesNegVelAtRHS in Hind.
    apply locEvtIndex in H4. repnd. subst m. 
    rewrite H4l in Hind. clear H4l.
    unfold isDeqEvt in a.
    destruct (eKind ed); inversion a.
    rename H into H6.
    specialize (Hind H6). clear H6.
    unfold inBetween in i.
    clear concreteValues Heqeks Heqevloc eo reactionTimeGap transitionValues velAccuracy boundary 
      alertDist safeDist maxDelay hwidth.
    eapply centerPosLB2; eauto.

  + clear Hind. symmetry in Heqeks. rename es into ed.
    pose proof (recvSend eo _ (isDeqEvtIf Heqeks)) as Hsend.
    destruct Hsend as [Es Hsend].
    repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
    symmetry in Heqevloc.
    pose proof  (SwOnlyRecievesFromSensor _ _ 
      Hsendrr (isDeqEvtIf Heqeks) Hsendl Heqevloc) as Hsw.
    exrepd.
    unfold PossibleSendRecvPair in Hsendl.
    repnd. clear Hsendlrrl Hsendlrl.
    rewrite Heqevloc in Hsendlrrr.
    rewrite side0 in Hsendlrrr. simpl in Hsendlrrr.
    rewrite <- Hsendll. intros Hmd.
    apply QShiftMinus in Hsendlrrr.
    eapply centerPosLB2; eauto.
    clear Hsendlrrr.
    pose proof (corrNodes 
                  eo 
                  (PROXSENSOR side)) as Hnc.
    simpl in Hnc.
    unfold DeviceSemantics, ProximitySensor in Hnc.
    unfold ProxPossibleTimeEvPair in Hnc.
    TrimAndLHS Hnc.
    pose proof (locEvtIndex (PROXSENSOR side) (eLocIndex Es) Es) as Hx.
    TrimAndRHS Hx.
    specialize (Hnc (eLocIndex Es)).
    rewrite Hx in Hnc; [| auto]. clear Hx.
    simpl in Hnc.
    specialize (Hnc Hsendrr).
    destruct Hnc as [t Hnc].
    rewrite inBetweenFold in Hnc.
    repnd. unfold inBetween in Hncrl.
    eapply centerPosLB2; eauto.
    clear Hncrl.
    rewrite Hncrr in Hmd.
    SensorMsgInvert Hmd.
    subst. unfold proxView in Hncl.
    (* apply less_leEq in Hncl. *)
    (* apply AbsIR_bnd in Hncl. *)
    unfold rEndPos, rboundary in Hncl.
    pose proof concreteValues as Hcon.

Open Scope nat_scope.
    AndProjN 0 Hcon as Hhw.
    AndProjN 1 Hcon as Hbb.
    AndProjN 2 Hcon as Hal.
    AndProjN 3 Hcon as Hmd.
Close Scope nat_scope.

    unfold centerPosAtTime.
    clear Hcon. subst. clear Hmd Hal Hbb Hhw.
    remember ({posX tstate} t) as cpt.
    clear dependent t.
    clear dependent Event.
    clear concreteValues velPos tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime  alertDist minGap.
    rewrite CAbGroups.minus_plus in Hncl.
    apply shift_leEq_plus in Hncl.
    apply minusSwapLe in Hncl.
    eapply leEq_transitive; eauto. clear dependent cpt.
    unfold Z2R. unfold inject_Z.
    Local Transparent Q2R.
    unfold Q2R, Z2R.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_minus.
    apply inj_Q_leEq.
    simpl. unfold cg_minus. simpl.
     lra.
Qed.



Close Scope Z_scope.

Lemma velocityMessagesAuxMsg: forall upto mt,
  member mt (filterPayloadsUptoIndex MOTOR (localEvts BASEMOTOR) upto)
  -> {fst mt  = speed} + {fst mt = (-speed)}.
Proof.
  induction upto as [ | upt Hind]; simpl; intros mt Hmem;[contradiction|].
  pose proof (velMessages upt) as Hvm.
  unfold getPayloadAndEv, getRecdPayload in Hmem.
  unfold getVelOEv, getRecdPayloadOp, 
    getRecdPayload, motorEvents in Hvm. simpl in Hvm.
  simpl in Hmem.
  destruct (localEvts BASEMOTOR upt) as [ev|]; simpl in Hvm, Hmem;
    [| auto; fail].
  fold (getVelM) in Hvm, Hmem.
  destruct (opBind getVelM (deqMesg ev)) as [vel|];
    [| auto; fail].
  simpl in Hmem.
  destruct Hmem as [Hmem| Hmem];[auto;fail| subst].
  simpl. destruct Hvm; auto.
Qed.

Lemma velocityMessagesMsg: forall m t,
  member m (velocityMessages t)
  -> {fst m  = speed} + {fst m = (-speed)}.
Proof.
  intros ? ? Hmem.
  apply velocityMessagesAuxMsg in Hmem.
  trivial.
Qed.

Open Scope Z_scope.

Lemma posVelAtLHS : forall evp,
  getRecdPayload MOTOR evp = Some speed
  -> eLoc evp = BASEMOTOR
  -> (centerPosAtTime tstate (eTime evp)) [<=]  -78.
Proof.
  intros ? Hp Hl.
  pose proof (PosVelAtLHSAux evp) as Hev.
  unfold MotorRecievesPositivVelAtLHS in Hev.
  rewrite Hl in Hev.
  pose proof (getRecdPayloadSpecMesg MOTOR) as Hd.
  simpl in Hd.
  specialize (Hd _ _ Hp). repnd.
  specialize (Hev Hdl Hdr).
  trivial.
Qed.
  
Lemma negVelAtRHS : forall evp,
  getRecdPayload MOTOR evp = Some (-speed)%Q
  -> eLoc evp = BASEMOTOR
  -> 78 [<=] (centerPosAtTime tstate (eTime evp)) .
Proof.
  intros ? Hp Hl.
  pose proof (NegVelAtRHSAux evp) as Hev.
  unfold MotorRecievesNegVelAtRHS in Hev.
  rewrite Hl in Hev.
  pose proof (getRecdPayloadSpecMesg MOTOR) as Hd.
  simpl in Hd.
  specialize (Hd _ _ Hp). repnd.
  specialize (Hev Hdl Hdr).
  trivial.
Qed.

Close Scope Z_scope.

Definition priorMotorMesg (vel: Q) (t : QTime):=
(λ ev : Event,
         eTime ev < t
         ∧ getRecdPayload MOTOR ev = Some vel 
          ∧ eLoc ev = BASEMOTOR).

Open Scope Z_scope.
Lemma motorLastPosVelAux : forall (lm : list (Q * Event)) (t : QTime),
  1 [<=] (centerPosAtTime tstate t)
  -> lm = velocityMessages t
  -> sig (latestEvt  (priorMotorMesg speed t)).
Proof.
  intro. unfold priorMotorMesg.
  induction lm as [|hlm tlm Hind]; intros ? Hcent Heq.
- simpl. assert False;[| contradiction].
  pose proof (corrNodes 
                eo 
                BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, correctVelDuring in Hm.
  unfold lastPayloadAndTime in Hm. unfold velocityMessages in Heq.
  rewrite <- Heq in Hm. unfold last in Hm.
  pose proof concreteValues as Hinit.
Open Scope nat_scope.
  AndProjN 4 Hinit as Hrt.
  AndProjN 5 Hinit as Hv.
  AndProjN 6 Hinit as Hp.
Close Scope nat_scope.
  clear Hinit. 
  subst. clear Hrt Heq. unfold hd in Hm.
  rewrite mapNil in Hm.
  rewrite (initVel tstate) in Hm.
  destruct Hm as [qtrans Hm]. repnd.
  
  eapply QPositionGeIf with (ta:=(mkQTime 0 I)) in Hcent; auto;
    [|apply qtimePos|].
  + rewrite initPos in Hcent.
    rewrite Hp in Hcent.
    unfold Q2R in Hcent.
    apply leEq_inj_Q in Hcent.
    simpl in Hcent.
    unfold inject_Z in Hcent. lra.
  + intros qt H0t. 
    pose proof (Qlt_le_dec qt qtrans) as Hd.
    destruct Hd as [Hd|Hd];[clear Hmrl | clear Hmrr].
    apply Qlt_le_weak in Hd.
    * rewrite Hv in Hmrr. specialize (Hmrr qt (conj (proj1 H0t) Hd)).
      unfold core.between in Hmrr.
      apply proj2 in Hmrr.
      eapply leEq_transitive; eauto.
      rewrite Max_id. apply inj_Q_leEq.
      simpl. unfold inject_Z. simpl. lra.

    * rewrite Hv in Hmrl. specialize (Hmrl qt (conj Hd (proj2 H0t))).
      rewrite Hmrl.
      apply inj_Q_leEq.
      simpl. unfold inject_Z. simpl. lra.
- (** check if nth event is +1 Deq . if so, exists n. else
      it is a -1. if not, by a lemma similar to PosVelAtNegPos,
      we can prove that centerpos at (eTime (nth event)) >=50
      . hence it is >0, hence, apply induction nyp with 
      t:=(eTime (nth event)) 
    *)
  pose proof (corrNodes 
                eo 
                BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, correctVelDuring in Hm.
  unfold lastPayloadAndTime in Hm. unfold velocityMessages in Heq.
  rewrite <- Heq in Hm.
  match type of Heq with
  | ?h::_ = ?r => assert (member h r) as Hvm;
      [rewrite <- Heq; simpl; right; reflexivity|]
  end.
  apply velocityMessagesMsg in Hvm.
  pose proof Heq as Hcorr.
  unfold velocityMessages in Hcorr.
  pose proof (filterPayloadsTimeCorr MOTOR BASEMOTOR) as Hs.
  simpl in Hs.
  apply Hs in Hcorr. clear Hs.
  destruct Hvm as [Hvm | Hvm].
  + clear Hm Hind. (** last message was of positive vel *)
    exists (snd hlm). simpl in Hvm.
    simpl. rewrite Hvm in Hcorr.
    fold (posVelMeg) in Hcorr. repnd.
    pose proof (filterPayloadsTimeLatest MOTOR BASEMOTOR) as Hlat.
    simpl in Hlat. 
    apply Hlat in Heq.
    eapply latestEvtStr; eauto.
    intros ? Hp. simpl. repnd.
    rewrite Hprl. dands; auto.

  + unfold hd in Hm. (** last message was of negative vel *)
    destruct hlm as [hq ht].
    simpl in Hvm. simpl in Hcorr.
    simpl in Hcorr. repnd. simpl in Hm. 
    specialize (fun gt => Hind (eTime ht) gt Hcorrrrr).
    clear Hm Hcent. subst hq.
    lapply Hind;[clear Hind; intros Hind|].
    * destruct Hind as [evInd Hind]. exists evInd.
      unfold latestEvt in Hind. repnd.
      split; [dands; auto; eauto using Qlt_trans|].
      intros ? Hpp.
      repnd. 
      let slem:= eval simpl in (filterPayloadsTimeComp MOTOR) in
        eapply slem in Hpprl; eauto.
      unfold velocityMessages in Heq.
      rewrite <- Heq in Hpprl.
      simpl in Hpprl.
      destruct Hpprl as [Hh| Ht];
        [|subst; apply (f_equal fst) in Ht; inverts Ht; fail].
      subst tlm. 
      let slem:= eval simpl in (filterPayloadsTimeCorr2 MOTOR) in
        apply slem in Hh.
      simpl in Hh. repnd.
      apply Hindr; dands; auto.
    * clear Hind Heq Hcorrrrr.
      eapply negVelAtRHS in Hcorrl; eauto.
      eapply leEq_transitive;[ | apply Hcorrl].
      UnfoldLRA.
Qed.

Lemma motorLastNegVelAux : forall (lm : list (Q * Event)) (t : QTime),
  (centerPosAtTime tstate t) [<=] -1
  -> lm = velocityMessages t
  -> sig (latestEvt  (priorMotorMesg (-speed) t)).
Proof.
  intro. unfold priorMotorMesg.
  induction lm as [|hlm tlm Hind]; intros ? Hcent Heq.
- simpl. assert False;[| contradiction].
  pose proof (corrNodes 
                eo 
                BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, correctVelDuring in Hm.
  unfold lastPayloadAndTime in Hm. unfold velocityMessages in Heq.
  rewrite <- Heq in Hm. unfold last in Hm.
  pose proof concreteValues as Hinit.
Open Scope nat_scope.
  AndProjN 4 Hinit as Hrt.
  AndProjN 5 Hinit as Hv.
  AndProjN 6 Hinit as Hp.
Close Scope nat_scope.
  clear Hinit. 
  subst. clear Hrt Heq. unfold hd in Hm.
  rewrite mapNil in Hm.
  rewrite (initVel tstate) in Hm.
  destruct Hm as [qtrans Hm]. repnd.
  
  eapply QPositionLeIf with (ta:=(mkQTime 0 I)) in Hcent; auto;
    [|apply qtimePos|].
  + rewrite initPos in Hcent.
    rewrite Hp in Hcent.
    unfold Q2R in Hcent.
    apply leEq_inj_Q in Hcent.
    unfold inject_Z in Hcent. simpl in Hcent.
    lra.
  + intros qt H0t.
    pose proof (Qlt_le_dec qt qtrans) as Hd.
    destruct Hd as [Hd|Hd];[clear Hmrl | clear Hmrr].
    apply Qlt_le_weak in Hd.
    * rewrite Hv in Hmrr. specialize (Hmrr qt (conj (proj1 H0t) Hd)).
      unfold core.between in Hmrr.
      apply proj1 in Hmrr.
      eapply leEq_transitive; eauto.
      rewrite Min_id. UnfoldLRA.

    * rewrite Hv in Hmrl. specialize (Hmrl qt (conj Hd (proj2 H0t))).
      rewrite Hmrl.
      apply inj_Q_leEq.
      simpl. unfold inject_Z. simpl. lra.
- (** check if nth event is +1 Deq . if so, exists n. else
      it is a -1. if not, by a lemma similar to PosVelAtNegPos,
      we can prove that centerpos at (eTime (nth event)) >=50
      . hence it is >0, hence, apply induction nyp with 
      t:=(eTime (nth event)) 
    *)
  pose proof (corrNodes 
                eo 
                BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, correctVelDuring in Hm.
  unfold lastPayloadAndTime in Hm. unfold velocityMessages in Heq.
  rewrite <- Heq in Hm.
  match type of Heq with
  | ?h::_ = ?r => assert (member h r) as Hvm;
      [rewrite <- Heq; simpl; right; reflexivity|]
  end.
  apply velocityMessagesMsg in Hvm.
  pose proof Heq as Hcorr.
  unfold velocityMessages in Hcorr.
  pose proof (filterPayloadsTimeCorr MOTOR BASEMOTOR) as Hs.
  simpl in Hs.
  apply Hs in Hcorr. clear Hs.
  apply Sumbool.sumbool_not in Hvm.
  destruct Hvm as [Hvm | Hvm].
  + clear Hm Hind. (** last message was of positive vel *)
    exists (snd hlm). simpl in Hvm.
    simpl. rewrite Hvm in Hcorr.
    fold (posVelMeg) in Hcorr. repnd.
    pose proof (filterPayloadsTimeLatest MOTOR BASEMOTOR) as Hlat.
    simpl in Hlat. 
    apply Hlat in Heq.
    eapply latestEvtStr; eauto.
    intros ? Hp. simpl. repnd.
    rewrite Hprl. dands; auto.

  + unfold hd in Hm. (** last message was of negative vel *)
    destruct hlm as [hq ht].
    simpl in Hvm. simpl in Hcorr.
    simpl in Hcorr. repnd. simpl in Hm. 
    specialize (fun gt => Hind (eTime ht) gt Hcorrrrr).
    clear Hm Hcent. subst hq.
    lapply Hind;[clear Hind; intros Hind|].
    * destruct Hind as [evInd Hind]. exists evInd.
      unfold latestEvt in Hind. repnd.
      split; [dands; auto; eauto using Qlt_trans|].
      intros ? Hpp.
      repnd. 
      let slem:= eval simpl in (filterPayloadsTimeComp MOTOR) in
        eapply slem in Hpprl; eauto.
      unfold velocityMessages in Heq.
      rewrite <- Heq in Hpprl.
      simpl in Hpprl.
      destruct Hpprl as [Hh| Ht];
        [|subst; apply (f_equal fst) in Ht; inverts Ht; fail].
      subst tlm. 
      let slem:= eval simpl in (filterPayloadsTimeCorr2 MOTOR) in
        apply slem in Hh.
      simpl in Hh. repnd.
      apply Hindr; dands; auto.
    * clear Hind Heq Hcorrrrr.
      eapply posVelAtLHS in Hcorrl; eauto.
      eapply leEq_transitive;[apply Hcorrl|].
      UnfoldLRA.
Qed.

(** in the aux version, lm was there only for induction.
    lets get rid of it*)
Lemma motorLastPosVel: forall (t : QTime),
  1 [<=] (centerPosAtTime tstate t)
  -> sig (latestEvt (priorMotorMesg speed t)).
Proof.
  intros. eapply motorLastPosVelAux; eauto.
Qed.

(** in the aux version, lm was there only for induction.
    lets get rid of it*)
Lemma motorLastNegVel: forall (t : QTime),
  (centerPosAtTime tstate t) [<=] (Z2R (-1))
  -> sig (latestEvt (priorMotorMesg (-speed) t)).
Proof.
  intros. eapply motorLastNegVelAux; eauto.
Qed.


Lemma SensorOnlySendsToSw :   forall Es Er side,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Es = PROXSENSOR side
  -> eLoc Er = SWCONTROLLER.
Proof.
  intros ? ? ? Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrr.
  unfold validSendMesg in Hsendlrrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  apply (f_equal ( fst)) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  simpl in Hsendlrrl, XXl. 
  unfold mtopic in Hsendlrrl. simpl in Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  rewrite Hl in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite RemoveOrFalse in Hsendlrrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl. unfold validRecvMesg, mtopic in Hsendlrl.
  simpl in Hsendlrl. rewrite <- Hsendlrrl in Hsendlrl.
  destruct (eLoc Er); simpl in Hsendlrl;
    try rewrite RemoveOrFalse in Hsendlrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

Lemma SwOnlySendsToMotor :   forall Es Er,
  isSendEvt Es
  -> isRecvEvt Er
  -> PossibleSendRecvPair Es Er
  -> eLoc Es = SWCONTROLLER
  -> eLoc Er = BASEMOTOR.
Proof.
  intros ? ?  Hs Hr Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  repnd. clear Hsendlrrr.
  unfold validSendMesg in Hsendlrrl.
  pose proof (deqSingleMessage _ Hr) as XX.
  destruct XX as [m XX].
  repnd. rewrite <- XXl in Hsendlrl.
  apply (f_equal ( fst)) in XXl.
  rewrite <- Hsendll in XXl. simpl in Hsendlrrl.
  simpl in Hsendlrrl, XXl. 
  unfold mtopic in Hsendlrrl. simpl in Hsendlrrl.
  rewrite <- XXl in Hsendlrrl.
  rewrite Hl in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite RemoveOrFalse in Hsendlrrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl. unfold validRecvMesg, mtopic in Hsendlrl.
  simpl in Hsendlrl. rewrite <- Hsendlrrl in Hsendlrl.
  destruct (eLoc Er); simpl in Hsendlrl;
    try rewrite RemoveOrFalse in Hsendlrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.
  
Lemma timeDiffLBPosVel : forall (ts te : Time) (ps pe : ℝ),
  {tstate} ts [<=] ps
  -> pe [<=] {tstate} te
  -> ts [<=] te
  -> ps [<] pe
  -> (pe[-]ps) [<=] te [-] ts.
Proof.
  intros ? ? ? ? Htl Htr Hte Hplt.
  assert ({tstate} ts [<] {tstate} te) as Hlt by eauto 4 with CoRN.
  apply TContRlt in Hlt; trivial;[].
  pose proof (minus_resp_leEq_both _ _ _ _ _ Htr Htl).
  eapply leEq_transitive; eauto.
  apply centerPosChange.
  trivial.
Qed.

Lemma timeDiffLBNegVel : forall (ts te : Time) (ps pe : ℝ),
  {tstate} te [<=] pe
  -> ps [<=] {tstate} ts
  -> ts [<=] te
  -> pe [<] ps
  ->  (ps[-]pe) [<=] te [-] ts .
Proof.
  intros ? ? ? ? Htl Htr Hte Hplt.
  assert ({tstate} te [<] {tstate} ts) as Hlt by eauto 4 with CoRN.
  apply TContRgt in Hlt; trivial;[].
  pose proof (minus_resp_leEq_both _ _ _ _ _ Htl Htr) as HH.
  apply inv_cancel_leEq.
  rewrite minusInvR.
  rewrite minusInvR.
  eapply leEq_transitive; eauto.
  apply centerPosChangeLB.
  trivial.
Qed.

Close Scope Q_scope.
Open Scope nat_scope.

Lemma NegAfterLatestPos : forall evMp evMn t (n:nat),
  priorMotorMesg (-speed) t evMn
  -> (latestEvt (priorMotorMesg speed t)) evMp
  -> (eTime evMp < eTime evMn)%Q
  -> (S (eLocIndex evMn) <= n)%nat
  -> let lm := filterPayloadsUptoIndex MOTOR (localEvts BASEMOTOR) n in
     match lm with
     | hdp::tlp =>
          (eTime (snd hdp) < t)%Q -> (fst hdp) = (-speed)%Q
     | nil => True
     end.
Proof.
  intros  ? ? ? ? Hp Hl Het Hle.
  induction Hle as [| np Hnp Hind].
- simpl. unfold priorMotorMesg in Hp.
  repnd.
  pose proof (locEvtIndex BASEMOTOR (eLocIndex evMn) evMn) as Hxx.
  rewrite ((proj1 Hxx) (conj Hprr eq_refl)).
  simpl. rewrite Hprl. simpl. reflexivity.
- simpl. simpl in Hind.
  pose proof (velocityMessagesAuxMsg (S np)) as Hxy.
  pose proof (filterPayloadsIndexCorr2 MOTOR BASEMOTOR (S np)) as Hxz.
  simpl in Hxy, Hxz.
  remember ((getPayloadAndEv MOTOR (localEvts BASEMOTOR np)))
    as oplev.
  destruct oplev as [plev|];[clear Hind| exact Hind].
  simpl. simpl in Hxz, Hxy. 
  specialize (Hxz _ (inr eq_refl)).
  specialize (Hxy _ (inr eq_refl)).
  intros Hplt.
  destruct Hxy as [hxy | Hxy];trivial;[].
  provefalse. 
  unfold latestEvt in Hl.
  repnd. rewrite hxy in Hxzl. clear Hxzrr.
  unfold priorMotorMesg in Hlr.
  specialize (Hlr _ (conj Hplt (conj Hxzl Hxzrl))).
  clear Hxzl Hxzrl.
  revert Hlr.
  remember (localEvts BASEMOTOR np) as oev.
  destruct oev as [ev|];
  simpl in Heqoplev;[|inverts Heqoplev; fail].
  destruct (getRecdPayload MOTOR ev); inverts Heqoplev.
  simpl in Hplt. simpl.
  intro Hcc. assert (eTime evMp < eTime ev)%Q;[| lra].
  clear Hcc.
  symmetry in Heqoev. apply locEvtIndex in Heqoev.
  repnd.
  fold (lt (eLocIndex evMn) np) in Hnp.
  rewrite <- Heqoevr  in Hnp.
  apply timeIndexConsistent in Hnp.
  remember (eTime ev).
  remember (eTime evMp).
  lra.
Qed.

Lemma PosAfterLatestNeg : forall evMp evMn t (n:nat),
  priorMotorMesg (speed) t evMn
  -> (latestEvt (priorMotorMesg (-speed) t)) evMp
  -> (eTime evMp < eTime evMn)%Q
  -> (S (eLocIndex evMn) <= n)%nat
  -> let lm := filterPayloadsUptoIndex 
                  MOTOR (localEvts BASEMOTOR) n in
     match lm with
     | hdp::tlp =>
          (eTime (snd hdp) < t)%Q -> (fst hdp) = (speed)
     | nil => True
     end.
Proof.
  intros  ? ? ? ? Hp Hl Het Hle.
  induction Hle as [| np Hnp Hind].
- simpl. unfold priorMotorMesg in Hp.
  repnd.
  pose proof (locEvtIndex BASEMOTOR (eLocIndex evMn) evMn) as Hxx.
  rewrite ((proj1 Hxx) (conj Hprr eq_refl)).
  simpl. rewrite Hprl. simpl. reflexivity.
- simpl. simpl in Hind.
  pose proof (velocityMessagesAuxMsg (S np)) as Hxy.
  pose proof (filterPayloadsIndexCorr2 MOTOR BASEMOTOR (S np)) as Hxz.
  simpl in Hxy, Hxz.
  remember ((getPayloadAndEv MOTOR (localEvts BASEMOTOR np)))
    as oplev.
  destruct oplev as [plev|];[clear Hind| exact Hind].
  simpl. simpl in Hxz, Hxy. 
  specialize (Hxz _ (inr eq_refl)).
  specialize (Hxy _ (inr eq_refl)).
  intros Hplt.
  destruct Hxy as [Hxy | Hxy];trivial;[].
  provefalse. 
  unfold latestEvt in Hl.
  repnd. rewrite Hxy in Hxzl. clear Hxzrr.
  unfold priorMotorMesg in Hlr.
  specialize (Hlr _ (conj Hplt (conj Hxzl Hxzrl))).
  clear Hxzl Hxzrl.
  revert Hlr.
  remember (localEvts BASEMOTOR np) as oev.
  destruct oev as [ev|];
  simpl in Heqoplev;[|inverts Heqoplev; fail].
  destruct (getRecdPayload MOTOR ev); inverts Heqoplev.
  simpl in Hplt. simpl.
  intro Hcc. assert (eTime evMp < eTime ev)%Q;[| lra].
  clear Hcc.
  symmetry in Heqoev. apply locEvtIndex in Heqoev.
  repnd.
  fold (lt (eLocIndex evMn) np) in Hnp.
  rewrite <- Heqoevr  in Hnp.
  apply timeIndexConsistent in Hnp.
  remember (eTime ev).
  remember (eTime evMp).
  lra.
Qed.

Open Scope Z_scope.

Lemma VelNegAfterLatestPosAux : forall evMp evMn t ev,
  priorMotorMesg (-speed) t evMn
  -> (latestEvt (priorMotorMesg speed t)) evMp
  -> (eTime evMp < eTime evMn)%Q
  -> ((eLocIndex evMn) < eLocIndex ev)%nat
  -> (eLoc ev = BASEMOTOR)
  -> (eTime ev < t)%Q
  -> ({velX tstate}  (eTime ev) [<=] -1).
Proof.
  intros  ? ? ? ? Hp Hl Het Hle Hloc Hevt.
  pose proof (NegAfterLatestPos _ _ _ _ Hp Hl Het Hle) as Hnn.
  simpl in Hnn.
  pose proof (corrNodes 
              eo 
              BASEMOTOR  (eTime ev)) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, 
      lastPayloadAndTime, filterPayloadsUptoTime in Hm.
  rewrite numPrevEvtsEtime in Hm; [| trivial];[].
    (* we know that 
      the default case of [hd] wont get invoked in Hm
      Luckily, [initialVel] is correct,
      but let's not depend on that because
      we already have a message/event that must be
      in that list *)
  pose proof (fun pl => filterPayloadsIndexComp  
        MOTOR BASEMOTOR (eLocIndex ev) pl evMn) as Hcomp.
  unfold priorMotorMesg in Hp.
  repnd. rewrite Hprl in Hcomp. rewrite Hprr in Hcomp.
  specialize (Hcomp _ eq_refl eq_refl).
  lapply Hcomp;[clear Hcomp; intro Hcomp| omega].
  remember ((filterPayloadsUptoIndex MOTOR 
        (localEvts BASEMOTOR) (eLocIndex ev))) as lf.
  destruct lf as [ | plev lft ];[inverts Hcomp; fail|].
  clear Hcomp. simpl in Hm.
  apply filterPayloadsIndexCorr in Heqlf.
  repnd.
  clear Heqlfrrr.
  assert (eLocIndex (snd plev) <  eLocIndex ev)%nat as Hev by omega.
  apply timeIndexConsistent in Heqlfrrl.
  DestImp Hnn;[| eauto using Qlt_trans].
  unfold correctVelDuring, corrSinceLastVel, lastVelAndTime, 
    velocityMessages, filterPayloadsUptoTime in Hm.
  destruct Hm as [qt Hm].
  repnd. clear Hmrr.
  specialize (Hmrl (eTime ev)). rewrite Hnn in Hmrl.
  apply evSpacIndex in Hev;[| congruence].
  assert (eTime (snd plev) + reactionTime <= eTime ev)%Q
    by (  remember (eTime ev);  remember (eTime evMp); remember (eTime (snd plev)); lra).
  assert (qt <= eTime ev)%Q as Hqt by 
    eauto using Qle_trans.
  rewrite Hmrl;
    [|split; trivial]; apply leEq_reflexive; fail.
Qed.

Lemma VelPosAfterLatestNegAux : forall evMp evMn t ev,
  priorMotorMesg (speed) t evMn
  -> (latestEvt (priorMotorMesg (-speed) t)) evMp
  -> (eTime evMp < eTime evMn)%Q
  -> ((eLocIndex evMn) < eLocIndex ev)%nat
  -> (eLoc ev = BASEMOTOR)
  -> (eTime ev < t)%Q
  -> 1 [<=] {velX tstate}  (eTime ev).
Proof.
  intros  ? ? ? ? Hp Hl Het Hle Hloc Hevt.
  pose proof (PosAfterLatestNeg _ _ _ _ Hp Hl Het Hle) as Hnn.
  simpl. simpl in Hnn.
  pose proof (corrNodes 
              eo 
              BASEMOTOR  (eTime ev)) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, 
      lastPayloadAndTime, filterPayloadsUptoTime in Hm.
  rewrite numPrevEvtsEtime in Hm; [| trivial];[].
    (* we know that 
      the default case of [hd] wont get invoked in Hm
      Luckily, [initialVel] is correct,
      but let's not depend on that because
      we already have a message/event that must be
      in that list *)
  pose proof (fun pl => filterPayloadsIndexComp  
        MOTOR BASEMOTOR (eLocIndex ev) pl evMn) as Hcomp.
  unfold priorMotorMesg in Hp.
  repnd. rewrite Hprl in Hcomp. rewrite Hprr in Hcomp.
  specialize (Hcomp _ eq_refl eq_refl).
  lapply Hcomp;[clear Hcomp; intro Hcomp| omega].
  remember ((filterPayloadsUptoIndex MOTOR 
        (localEvts BASEMOTOR) (eLocIndex ev))) as lf.
  destruct lf as [ | plev lft ];[inverts Hcomp; fail|].
  clear Hcomp. simpl in Hm.
  apply filterPayloadsIndexCorr in Heqlf.
  repnd.
  clear Heqlfrrr.
  assert (eLocIndex (snd plev) <  eLocIndex ev)%nat as Hev by omega.
  apply timeIndexConsistent in Heqlfrrl.
  DestImp Hnn;[| eauto using Qlt_trans].
  unfold correctVelDuring, corrSinceLastVel, lastVelAndTime, 
    velocityMessages, filterPayloadsUptoTime in Hm.
  destruct Hm as [qt Hm].
  repnd. clear Hmrr.
  specialize (Hmrl (eTime ev)). rewrite Hnn in Hmrl.
  apply evSpacIndex in Hev;[| congruence].
  assert (eTime (snd plev) + reactionTime <= eTime ev)%Q
    by (  remember (eTime ev);  remember (eTime evMp); remember (eTime (snd plev)); lra).
  assert (qt <= eTime ev)%Q as Hqt by 
    eauto using Qle_trans.
  rewrite Hmrl;
    [|split; trivial]; apply leEq_reflexive; fail.
Qed.

Open Scope Q_scope.

Lemma VelNegAfterLatestPos : forall evMp evMn tunsafe
    (t : QTime),
  priorMotorMesg (-speed) tunsafe evMn
  -> (latestEvt (priorMotorMesg speed tunsafe)) evMp
  -> (eTime evMp < eTime evMn)%Q
  -> ((eTime evMn) + reactionTime) <= t <= tunsafe
  -> ({velX tstate} t [<=] -1).
Close Scope Q_scope.
Proof.
  intros  ? ? ? ? Hp Hl Het Hbet.
  pose proof (corrNodes 
              eo 
              BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, 
      lastPayloadAndTime, filterPayloadsUptoTime in Hm.
    (* we know that 
      the default case of [hd] wont get invoked in Hm
      Luckily, [initialVel] is corrent,
      but let's not depend on that because
      we already have a message/event that must be
      in that list *)
  pose proof (fun pl => filterPayloadsIndexComp  
        MOTOR BASEMOTOR (numPrevEvts (localEvts BASEMOTOR) t) pl evMn) as Hcomp.
  pose proof Hp as Hpb.
  unfold priorMotorMesg in Hp.
  repnd. rewrite Hprl in Hcomp. rewrite Hprr in Hcomp.
  specialize (Hcomp _ eq_refl eq_refl).
  rewrite reactionTime1 in Hbetl. 
  DestImp Hcomp;[|apply numPrevEvtsSpec; trivial; remember (eTime evMn);  remember (eTime evMp); lra].

  remember(filterPayloadsUptoIndex MOTOR (localEvts BASEMOTOR)
             (numPrevEvts (localEvts BASEMOTOR) t)) as lf.
  destruct lf as [ | plev lft ];[inverts Hcomp; fail|].
  inverts Hcomp as; simpl in Hm.
- intros Hcomp.
  pose proof (NegAfterLatestPos _ _ _ 
      (numPrevEvts (localEvts BASEMOTOR) t) Hpb Hl Het) as Hnn.
  rewrite <- Heqlf in Hnn. simpl in Hnn.
  DestImp Hnn;[|apply numPrevEvtsSpec; trivial;  remember (eTime evMn);  remember (eTime evMp); lra].
  eapply filterPayloadsIndexSorted in Hcomp; eauto.
  apply filterPayloadsTimeCorr in Heqlf.
  rename Heqlf into Hf. repnd. 
  assert (eTime (snd plev) < tunsafe)%Q by  ( remember (eTime evMn);  remember (eTime evMp); 
     remember (eTime (snd plev)); lra).
  DestImp Hnn;[|trivial;fail].
  eapply VelNegAfterLatestPosAux in Hcomp; eauto.
  rewrite Hnn in Hm.
  revert Hfrrl.
  revert Hm.
  revert Hcomp.
  clear. intros Hv Hm Hlt.
  unfold correctVelDuring, corrSinceLastVel, lastVelAndTime, 
    velocityMessages, filterPayloadsUptoTime in Hm.
  destruct Hm as [qt Hm].
  repnd.
  pose proof (Qlt_le_dec qt t) as Hdec.
  apply Qlt_le_weak in Hlt.
  destruct Hdec as [Hdec | Hdec]; [clear Hmrr|clear Hmrl].
  + apply Qlt_le_weak in Hdec.
    rewrite Hmrl; [| split]; auto;[|]; apply leEq_reflexive.
  + unfold core.between in Hmrr.
    specialize (Hmrr _ (conj Hlt Hdec)).
    unfold simpleBetween in Hmrr.
    repnd.
    trivial. unfold speed in Hmrrr.
    unfold Q2R, Z2R , inject_Z in Hmrrr, Hv.
    revert Hmrrl. simplInjQ.
    intro Hmrrl.
    eapply leEq_transitive; eauto.
    apply Max_leEq; auto.
    unfold inject_Z.
    simplInjQ.
    apply leEq_reflexive.
- unfold correctVelDuring, corrSinceLastVel, lastVelAndTime, 
    velocityMessages, filterPayloadsUptoTime in Hm.
  destruct Hm as [qt Hm].
  repnd. clear Hmrr.
  specialize (Hmrl t). rewrite reactionTime1 in Hmlr.
  assert (qt <= t)%Q by lra.
  rewrite Hmrl;
    [|split; trivial]; apply leEq_reflexive; fail.
Qed.

Open Scope Q_scope.

Lemma VelPosAfterLatestNeg : forall evMp evMn tunsafe
    (t : QTime),
  priorMotorMesg (speed) tunsafe evMn
  -> (latestEvt (priorMotorMesg (-speed) tunsafe)) evMp
  -> (eTime evMp < eTime evMn)
  -> ((eTime evMn) + reactionTime) <= t <= tunsafe
  -> (Z2R 1 [<=] {velX tstate} t).
Close Scope Q_scope.
Proof.
  intros  ? ? ? ? Hp Hl Het Hbet.
  pose proof (corrNodes 
              eo 
              BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, 
      lastPayloadAndTime, filterPayloadsUptoTime in Hm.
    (* we know that 
      the default case of [hd] wont get invoked in Hm
      Luckily, [initialVel] is corrent,
      but let's not depend on that because
      we already have a message/event that must be
      in that list *)
  pose proof (fun pl => filterPayloadsIndexComp  
        MOTOR BASEMOTOR (numPrevEvts (localEvts BASEMOTOR) t) pl evMn) as Hcomp.
  pose proof Hp as Hpb.
  unfold priorMotorMesg in Hp.
  repnd. rewrite Hprl in Hcomp. rewrite Hprr in Hcomp.
  specialize (Hcomp _ eq_refl eq_refl).
  rewrite reactionTime1 in Hbetl. 
  DestImp Hcomp;[|apply numPrevEvtsSpec; trivial; remember (eTime evMn);  remember (eTime evMp); lra].
  remember(filterPayloadsUptoIndex MOTOR (localEvts BASEMOTOR)
             (numPrevEvts (localEvts BASEMOTOR) t)) as lf.
  destruct lf as [ | plev lft ];[inverts Hcomp; fail|].
  inverts Hcomp as; simpl in Hm.
- intros Hcomp.
  pose proof (PosAfterLatestNeg _ _ _ 
      (numPrevEvts (localEvts BASEMOTOR) t) Hpb Hl Het) as Hnn.
  rewrite <- Heqlf in Hnn. simpl in Hnn.
  DestImp Hnn;[|apply numPrevEvtsSpec; trivial; remember (eTime evMn);  remember (eTime evMp); lra].
  eapply filterPayloadsIndexSorted in Hcomp; eauto.
  apply filterPayloadsTimeCorr in Heqlf.
  rename Heqlf into Hf. repnd. 
  assert (eTime (snd plev) < tunsafe)%Q by   ( remember (eTime evMn);  remember (eTime evMp); 
     remember (eTime (snd plev)); lra).
  DestImp Hnn;[|trivial;fail].
  eapply VelPosAfterLatestNegAux in Hcomp; eauto.
  rewrite Hnn in Hm.
  revert Hfrrl.
  revert Hm.
  revert Hcomp.
  clear. intros Hv Hm Hlt.
  unfold correctVelDuring, corrSinceLastVel, lastVelAndTime, 
    velocityMessages, filterPayloadsUptoTime in Hm.
  destruct Hm as [qt Hm].
  repnd.
  pose proof (Qlt_le_dec qt t) as Hdec.
  apply Qlt_le_weak in Hlt.
  destruct Hdec as [Hdec | Hdec]; [clear Hmrr|clear Hmrl].
  + apply Qlt_le_weak in Hdec.
    rewrite Hmrl; [| split]; auto;[|];
     apply leEq_reflexive.
  + unfold core.between in Hmrr.
    specialize (Hmrr _ (conj Hlt Hdec)).
    unfold simpleBetween in Hmrr.
    repnd.
    trivial. unfold speed in Hmrrr.
    unfold Q2R, Z2R , inject_Z in Hmrrr, Hv.
    revert Hmrrl. simplInjQ.
    intro Hmrrl.
    eapply leEq_transitive;[| apply Hmrrl].
    apply leEq_Min; auto.
    unfold inject_Z.
    apply leEq_reflexive.
- unfold correctVelDuring, corrSinceLastVel, lastVelAndTime, 
    velocityMessages, filterPayloadsUptoTime in Hm.
  destruct Hm as [qt Hm].
  repnd. clear Hmrr.
  specialize (Hmrl t). rewrite reactionTime1 in Hmlr.
  assert (qt <= t)%Q by lra.
  rewrite Hmrl;
    [|split; trivial]; apply leEq_reflexive; fail.
Qed.


Lemma RHSSafe : forall t: QTime,  (centerPosAtTime tstate t) [<=]  95.
Proof.
  intros. apply leEq_def. intros Hc.
  apply less_leEq in Hc.
  assert (Z2R 1[<=]centerPosAtTime tstate t) as Hle1 by
  (eapply leEq_transitive; eauto; unfold Z2R, inject_Z
    ;apply inj_Q_leEq; simpl;  lra).
  apply motorLastPosVel in Hle1.
  destruct Hle1 as [evMp Hlat].
  pose proof (Hlat) as Hlatb.
  unfold latestEvt, priorMotorMesg in Hlat. apply proj1 in Hlat.
  repnd. eapply posVelAtLHS in Hlatrl ; eauto.

  (** Applying IVT *)
  assert (Z2R (-78) [<] Z2R 95) as H99 by UnfoldLRA.
  assert (centerPosAtTime tstate (eTime evMp) [<] centerPosAtTime tstate t)
    as Hlt by eauto 4 with CoRN.
  clear H99. unfold centerPosAtTime in Hlatrl, Hc.
  assert (Z2R (-78) [<=] Z2R 86) as H91 by UnfoldLRA.
  assert (Z2R (86) [<=] Z2R 95) as H92 by UnfoldLRA.
  apply IVTTimeMinMax with (e:=[1]) (y:=Z2R 86)  in Hlt; simpl; 
    try split; eauto 3 with CoRN;[].
  clear H91 H92.
  destruct Hlt as [tivt H99].
  destruct H99 as [Hclr Habs].
  simpl in Hclr.
  destruct Hclr as [Httpp Htppt].
  rewrite leEq_imp_Min_is_lft in Httpp by
      (repeat (rewrite <- QT2T_Q2R);
       apply less_leEq;
       apply inj_Q_less; simpl; trivial).

  rewrite leEq_imp_Max_is_rht in Htppt by
      (repeat (rewrite <- QT2T_Q2R);
       apply less_leEq;
       apply inj_Q_less; simpl; trivial).
  
  pose proof Habs as HUB.
  rewrite AbsIR_minus in HUB.
  apply AbsIR_bnd in HUB.
  apply AbsIR_bnd in Habs.
  apply shift_minus_leEq in Habs.
  rename Habs into HLB.
  unfold Z2R in HLB, HUB.
  autorewrite with QSimpl in HLB, HUB.
  revert HLB. simplInjQ. intro HLB.
  revert HUB. simplInjQ. intro HUB.

  (** Applying IVT finished, we need to know that
     ([tpp] - [t]) > 8, because 9 sec is enough
     for corrective action to kick in in the motor.
    if 8 is not enough, change 95 to sth bigger *)

  rewrite  QT2T_Q2R in Htppt.
  pose proof (timeDiffLBPosVel _ _ _ _ HUB Hc Htppt) as Htlt.
  lapply Htlt;[clear Htlt; intros Htlt| UnfoldLRA].
  revert Htlt. unfold Z2R. simplInjQ.
  intros Htlt. simpl. 
  repeat (rewrite <- QT2T_Q2R in Htlt).
  autorewrite with QSimpl in Htlt.
  apply leEq_inj_Q in Htlt.
  unfold cg_minus in Htlt.
  simpl in Htlt.


    (* now invoking sensor's spec
      to get the event that it fired soon after [tivt] *)

  
  pose proof (corrNodes 
                eo 
                (PROXSENSOR right)) as Hnc.

  simpl in Hnc.
  apply proj1 in Hnc.
  specialize (Hnc tivt).
  unfold rEndPos, rboundary in Hnc.
  pose proof concreteValues as Hcon.

Open Scope nat_scope.
    AndProjN 0 Hcon as Hhw.
    AndProjN 1 Hcon as Hbb.
    AndProjN 2 Hcon as Hal.
    AndProjN 3 Hcon as Hmd.
    AndProjN 4 Hcon as Hrrrrr.
Close Scope nat_scope.

Check VelNegAfterLatestPos.
pose proof VelNegAfterLatestPos as Hvnalpb.
  subst.

  clear Hcon Hhw Hbb Hal Hmd. 
  unfold Z2R, inject_Z in Hnc.
  rewrite cag_commutes in Hnc.
  rewrite CAbGroups.minus_plus in Hnc.
  lapply Hnc;[clear Hnc;intro Hnc|
    apply minusSwapLe;
    eapply leEq_transitive; eauto;
    unfold Q2R;
    repeat (rewrite <- inj_Q_minus);
    apply inj_Q_leEq; unfold cg_minus; simpl;
        remember (eTime evMp); lra].
  destruct Hnc as [n Hnc].
  destruct Hnc as [ev Hnc].
  repnd.
  rename ev into Esens.
  (** got the event generated by the prox sensor.
      let's count the time towards the deadline *)
  unfold ProxPossibleTimeEvPair in Hncrr.
  repnd. simpl in Hncrrlr.
  rename Hncrrlr  into Htub.
  (** lets deliver the message to the s/w node *)


  pose proof (eventualDelivery eo _ Hncrl) as Hrec.
  destruct Hrec as [Er  Hrec].
  repnd.
  apply locEvtIndex in Hncl.
  pose proof (SensorOnlySendsToSw _ _ _ 
      Hncrl Hrecrr Hrecl (proj1 Hncl)) as Hsw.
  unfold PossibleSendRecvPair in Hrecl.
  pose proof (proj1 Hrecl) as Hmeq.
  repeat (apply proj2 in Hrecl).
  rewrite Hsw in Hrecl.
  rewrite (proj1 Hncl) in Hrecl.
  simpl in Hrecl.
  rename Er into Eswr.
  repnd. rewrite Hncrrr in Hmeq.

  (** got the msg received by sw. lets update the time bounds *)

  assert ((eTime Eswr) < tivt + (2 # 1))%Q  as Htubb by 
    (remember (eTime Eswr);  remember (eTime evMp); lra).

  clear Htub. rename Htubb into Htub.
  pose proof (globalCausal _ _ _ Hrecrl) as Hubb.
  assert (tivt < (eTime Eswr))%Q  as Htlb 
    by (remember (eTime Eswr); remember (eTime Esens);  
        remember (eTime evMp);lra).
  clear Hubb Hrecl Hncrrr Hncrl Hrecrl Hnclr Hncll Htppt
      Hncrrll Esens.

  (** lets process the message on the s/w node *)
   pose proof (corrNodes 
                eo 
                SWCONTROLLER 
                (eLocIndex Eswr)) as Hnc.
  apply snd in Hnc.
  pose proof (locEvtIndex SWCONTROLLER (eLocIndex Eswr) Eswr) as Hxx.
  rewrite (proj1 Hxx) in Hnc;[| split; auto; fail].
  simpl  in Hnc.
  specialize (Hnc Hrecrr (0%nat)).
  destruct Hnc as [m Hnc ]. 
    unfold procOutMsgs.
    apply proj1 in Hxx.
    rewrite Hxx; auto.
    simpl. unfold SwProcess. rewrite getNewProcLPure. simpl.
    unfold getDeqOutput2, getOutput. simpl.
    unfold liftToMesg, getPayload.
    rewrite <- Hmeq.
    simpl. omega.
  apply onlyNeededForOldProofs in Hnc.
  simpl in Hnc. 
  destruct Hnc as [es0 Hnc].
  destruct Hnc as [ed Hnc].
  exrepd. rewrite ((proj1 Hxx) (conj Hsw eq_refl)) in e.
  symmetry in e. inverts e.
  rename es0 into Esws.
  simpl in H1, Hmeq. rewrite <- Hmeq in H1.
  SensorMsgInvert H1. subst dmp.
  clear Hmeq.
  rename H2 into Hmot.
  simpl in Hmot.
  
  (** got the msg sent received by sw. 
      lets update the time bounds *)

  assert ((eTime Esws) < tivt + (3 # 1))%Q  as Htubb by 
    (remember (eTime Eswr); remember (eTime Esws);  
        remember (eTime evMp);lra).
  clear Htub. rename Htubb into Htub.
  assert (tivt < (eTime Esws))%Q  as Htlbb by 
    (remember (eTime Eswr); remember (eTime Esws);  
        remember (eTime evMp);lra).
  clear Htlb. rename Htlbb into Htlb.
  rename e0 into Hss.
  apply locEvtIndex in Hss.
  clear H0 H l Hrecrr Hxx Hsw a Eswr.

  rename a0 into HmotSend.

  (** let's receive the -speed message on the motor *)
  
  pose proof (eventualDelivery eo _ HmotSend) as Hmrec.
  destruct Hmrec as [Er  Hmrec].
  repnd. rename Er into Emr.
  pose proof (SwOnlySendsToMotor _ _ 
      HmotSend Hmrecrr Hmrecl Hssl) as HmotR.
  unfold PossibleSendRecvPair in Hmrecl.
  pose proof (proj1 Hmrecl) as Hmeq.
  repeat (apply proj2 in Hmrecl).
  rewrite HmotR in Hmrecl.
  rewrite Hssl in Hmrecl.
  simpl in Hmrecl.
  repnd. rewrite <- Hmot in Hmeq.
  
    (** got the msg received by sw. lets update the time bounds *)

  rewrite <- QT2T_Q2R in Httpp.
  apply leEq_inj_Q in Httpp.
  simpl in Httpp.
  pose proof (globalCausal _ _ _ Hmrecrl) as Hubb.
  assert (eTime evMp < eTime Emr)%Q as Hql by 
        (remember (eTime Emr); remember (eTime Esws);  
        remember (eTime evMp);lra).

  assert ((eTime Emr) < t)%Q as Hlt by 
    (remember (eTime Emr); remember (eTime Esws);  
        remember (eTime evMp);lra).
  assert (Qtadd (eTime Emr) (mkQTime 1 I)< tivt + (5 # 1))%Q  
    as Htubb by (unfold Qtadd; simpl; (remember (eTime Emr); remember (eTime Esws);  
        remember (eTime evMp);lra)).
  assert (tivt < Qtadd (eTime Emr) (mkQTime 1 I))%Q  
    as Htlbb by (unfold Qtadd; simpl; (remember (eTime Emr); remember (eTime Esws);  
        remember (eTime evMp);lra)).
  assert (Qtadd (eTime Emr) (mkQTime 1 I) < t)%Q  
    as Hltt by (unfold Qtadd; simpl; (remember (eTime Emr); remember (eTime Esws);  
        remember (eTime evMp);lra)).
  apply (centerPosUB _ _ _ _ (conj Htlbb Htubb)) in HUB.
  revert HUB. simplInjQ. intro HUB.
  pose proof (fun tl pm
      => Hvnalpb evMp Emr t tl pm Hlatb) as Hv.
  specialize (fun tl pm => Hv tl pm Hql).
  unfold priorMotorMesg, getRecdPayload, deqMesg in Hv.
  unfold isRecvEvt, isDeqEvt in Hmrecrr.
  destruct (eKind Emr); inversion Hmrecrr; [].
  Local Opaque Q2R.
  simpl in Hv, Hmeq. 
  simpl in Hv. unfold getPayload in Hv.
  simpl in Hv. rewrite <- Hmeq in Hv.
  clear Hql.
  specialize (fun tl => Hv tl (conj Hlt (conj eq_refl HmotR))).
  pose proof (QVelPosUB tstate _ _ (Qlt_le_weak _ _ Hltt) (inject_Z (-1))) 
      as Hvb.
  specialize ( Hvb Hv).
  clear Hv. unfold centerPosAtTime in HUB.
  remember ({tstate} (Qtadd (eTime Emr) (mkQTime 1 I))) as qta.
  unfold Qtadd in Hltt.
  simpl in Hltt.
  assert ({tstate} t[-]qta [<=] [0]) as HH0 by
     (eapply  leEq_transitive; eauto;
      rewrite <- inj_Q_Zero;
      apply inj_Q_leEq;
      simpl; unfold inject_Z; simpl; 
       remember (eTime Emr); remember (eTime Esws); remember (eTime evMp);
      lra).
  pose proof (plus_resp_leEq_both _ _ _ _ _ HH0 HUB) as Hf.
  rewrite <- cg_cancel_mixed in Hf.
  pose proof (leEq_transitive _ _ _ _ Hc Hf) as XX.
  rewrite <- inj_Q_Zero in XX.
  rewrite <- inj_Q_plus in XX.
  apply leEq_inj_Q in XX.
  simpl in XX. unfold inject_Z in XX.
  remember (eTime Emr); remember (eTime Esws); remember (eTime evMp).
  lra.
Qed.

Lemma LHSSafe : forall t: QTime, 
  -95 [<=] (centerPosAtTime tstate t).
Proof.
  intros. apply leEq_def. intros Hc.
  apply less_leEq in Hc.
  assert (centerPosAtTime tstate t[<=]Z2R (-1)) as Hle1 by
  (eapply leEq_transitive; eauto; unfold Z2R, inject_Z
    ;apply inj_Q_leEq; simpl;  lra).
  apply motorLastNegVel in Hle1.
  destruct Hle1 as [evMp Hlat].
  pose proof (Hlat) as Hlatb.
  unfold latestEvt, priorMotorMesg in Hlat. apply proj1 in Hlat.
  repnd. eapply negVelAtRHS in Hlatrl ; eauto.

  (** Applying IVT *)
  assert (Z2R (-95) [<] Z2R 78) as H99 by UnfoldLRA.
  assert (centerPosAtTime tstate t 
        [<] centerPosAtTime tstate (eTime evMp))
    as Hlt by eauto 4 with CoRN.
  clear H99. unfold centerPosAtTime in Hlatrl, Hc.
  assert (Z2R (-86) [<=] Z2R (78)) as H91 by UnfoldLRA.
  assert (Z2R (-95) [<=] Z2R (-86)) as H92 by UnfoldLRA.
  apply IVTTimeMinMax with (e:=[1]) (y:=Z2R (-86))  in Hlt; simpl; 
    try split; eauto 3 with CoRN;[].
  clear H91 H92.
  destruct Hlt as [tivt H99].
  destruct H99 as [Hclr Habs].
  simpl in Hclr.
  destruct Hclr as [Httpp Htppt].
  rewrite Min_comm in Httpp.
  rewrite leEq_imp_Min_is_lft in Httpp by
      (repeat (rewrite <- QT2T_Q2R);
       apply less_leEq;
       apply inj_Q_less; simpl; trivial).

  rewrite Max_comm in Htppt.
  rewrite leEq_imp_Max_is_rht in Htppt by
      (repeat (rewrite <- QT2T_Q2R);
       apply less_leEq;
       apply inj_Q_less; simpl; trivial).
  
  pose proof Habs as HUB.
  rewrite AbsIR_minus in HUB.
  apply AbsIR_bnd in HUB.
  apply AbsIR_bnd in Habs.
  apply shift_minus_leEq in Habs.
  rename Habs into HLB.
  unfold Z2R in HLB, HUB.
  autorewrite with QSimpl in HLB, HUB.
  revert HLB. simplInjQ. intro HLB.
  revert HUB. simplInjQ. intro HUB.

  (** Applying IVT finished, we need to know that
     ([tpp] - [t]) > 8, because 9 sec is enough
     for corrective action to kick in in the motor.
    if 8 is not enough, change 95 to sth bigger *)

  rewrite  QT2T_Q2R in Htppt.


  pose proof (timeDiffLBNegVel _ _ _ _ Hc HLB  Htppt) as Htlt.
  lapply Htlt;[clear Htlt; intros Htlt| UnfoldLRA].
  revert Htlt. unfold Z2R. simplInjQ.
  intros Htlt. simpl. 
  repeat (rewrite <- QT2T_Q2R in Htlt).
  autorewrite with QSimpl in Htlt.
  apply leEq_inj_Q in Htlt.
  unfold cg_minus in Htlt.
  simpl in Htlt.

    (* now invoking sensor's spec
      to get the event that it fired soon after [tivt] *)
  
  pose proof (corrNodes 
                eo 
                (PROXSENSOR left)) as Hnc.
  simpl in Hnc.
  apply proj1 in Hnc.
  specialize (Hnc tivt).
  unfold lEndPos, lboundary in Hnc.
  pose proof concreteValues as Hcon.
Open Scope nat_scope.
    AndProjN 0 Hcon as Hhw.
    AndProjN 1 Hcon as Hbb.
    AndProjN 2 Hcon as Hal.
    AndProjN 3 Hcon as Hmd.
    AndProjN 4 Hcon as Hrrrrr.
Close Scope nat_scope.
  subst.
  clear Hcon Hhw Hbb Hal Hmd. 
  unfold Z2R, inject_Z in Hnc.
  remember ({tstate} tivt) as tttt.
  (* wierd error: Error: build_signature: 
      no constraint can apply on a dependent argument*)

  rewrite <- inj_Q_Zero in Hnc.
  rewrite <- CAbGroups.minus_plus in Hnc.
  autorewrite with QSimpl in Hnc.
  revert Hnc. simplInjQ. intros Hnc.
  DestImp Hnc;[|
    apply shift_minus_leEq;
    eapply leEq_transitive; eauto;
    autorewrite with QSimpl;
    UnfoldLRA].
  destruct Hnc as [n Hnc].
  destruct Hnc as [ev Hnc].
  repnd.
  rename ev into Esens.
  (** got the event generated by the prox sensor.
      let's count the time towards the deadline *)
  unfold ProxPossibleTimeEvPair in Hncrr.
  repnd. simpl in Hncrrlr.
  rename Hncrrlr  into Htub.
  (** lets deliver the message to the s/w node *)

  pose proof (eventualDelivery eo  _ Hncrl) as Hrec.
  destruct Hrec as [Er  Hrec].
  repnd.
  apply locEvtIndex in Hncl.
  pose proof (SensorOnlySendsToSw _ _ _ 
      Hncrl Hrecrr Hrecl (proj1 Hncl)) as Hsw.
  unfold PossibleSendRecvPair in Hrecl.
  pose proof (proj1 Hrecl) as Hmeq.
  repeat (apply proj2 in Hrecl).
  rewrite Hsw in Hrecl.
  rewrite (proj1 Hncl) in Hrecl.
  simpl in Hrecl.
  rename Er into Eswr.
  repnd. rewrite Hncrrr in Hmeq.

  (** got the msg received by sw. lets update the time bounds *)

  assert ((eTime Eswr) < tivt + (2 # 1))%Q  as Htubb by lra.
  clear Htub. rename Htubb into Htub.
  pose proof (globalCausal _ _ _ Hrecrl) as Hubb.
  assert (tivt < (eTime Eswr))%Q  as Htlb by lra.
  clear Hubb Hrecl Hncrrr Hncrl Hrecrl Hnclr Hncll Htppt
      Hncrrll Esens.

  (** lets process the message on the s/w node *)
   pose proof (corrNodes 
                eo 
                SWCONTROLLER 
                (eLocIndex Eswr)) as Hnc.
  apply snd in Hnc.
  pose proof (locEvtIndex SWCONTROLLER (eLocIndex Eswr) Eswr) as Hxx.
  rewrite (proj1 Hxx) in Hnc;[| split; auto; fail].
  simpl  in Hnc.
  specialize (Hnc Hrecrr (0%nat)).
  destruct Hnc as [m Hnc ]. 
    unfold procOutMsgs.
    apply proj1 in Hxx.
    rewrite Hxx; auto.
    simpl. unfold SwProcess. rewrite getNewProcLPure. simpl.
    unfold getDeqOutput2, getOutput. simpl.
    unfold liftToMesg, getPayload.
    rewrite <- Hmeq.
    simpl. omega.
  apply onlyNeededForOldProofs in Hnc.
  simpl in Hnc. 
  destruct Hnc as [es0 Hnc].
  destruct Hnc as [ed Hnc].
  exrepd. rewrite ((proj1 Hxx) (conj Hsw eq_refl)) in e.
  symmetry in e. inverts e.
  rename es0 into Esws.
  simpl in Hmeq, H1. rewrite <- Hmeq in H1.
  SensorMsgInvert H1. subst dmp.
  clear Hmeq.
  rename H2 into Hmot.
  simpl in Hmot.
  
  (** got the msg sent received by sw. 
      lets update the time bounds *)

  assert ((eTime Esws) < tivt + (3 # 1))%Q  as Htubb by lra.
  clear Htub. rename Htubb into Htub.
  assert (tivt < (eTime Esws))%Q  as Htlbb by lra.
  clear Htlb. rename Htlbb into Htlb.
  rename e0 into Hss.
  apply locEvtIndex in Hss.
  clear H0 H a l Hrecrr Hxx Hsw Eswr.

  rename a0 into HmotSend.

  (** let's receive the -speed message on the motor *)
  
  pose proof (eventualDelivery eo  _ HmotSend) as Hmrec.
  destruct Hmrec as [Er  Hmrec].
  repnd. rename Er into Emr.
  pose proof (SwOnlySendsToMotor _ _ 
      HmotSend Hmrecrr Hmrecl Hssl) as HmotR.
  unfold PossibleSendRecvPair in Hmrecl.
  pose proof (proj1 Hmrecl) as Hmeq.
  repeat (apply proj2 in Hmrecl).
  rewrite HmotR in Hmrecl.
  rewrite Hssl in Hmrecl.
  simpl in Hmrecl.
  repnd. rewrite <- Hmot in Hmeq.
  
    (** got the msg received by sw. lets update the time bounds *)

  rewrite <- QT2T_Q2R in Httpp.
  apply leEq_inj_Q in Httpp.
  simpl in Httpp.
  pose proof (globalCausal _ _ _ Hmrecrl) as Hubb.
  assert (eTime evMp < eTime Emr)%Q as Hql by lra.
  assert ((eTime Emr) < t)%Q as Hlt by lra.
  assert (Qtadd (eTime Emr) (mkQTime 1 I)< tivt + (5 # 1))%Q  
    as Htubb by (unfold Qtadd; simpl; lra).
  assert (tivt < Qtadd (eTime Emr) (mkQTime 1 I))%Q  
    as Htlbb by (unfold Qtadd; simpl; lra).
  assert (Qtadd (eTime Emr) (mkQTime 1 I) < t)%Q  
    as Hltt by (unfold Qtadd; simpl; lra).
  clear dependent Esws.
  subst tttt.
  apply (centerPosLB _ _ _ _ (conj Htlbb Htubb)) in HLB.
  revert HLB. simplInjQ. intro HLB.
  pose proof (fun tl pm
      => VelPosAfterLatestNeg evMp Emr t tl pm Hlatb) as Hv.
  specialize (fun tl pm => Hv tl pm Hql).
  unfold priorMotorMesg, getRecdPayload, deqMesg in Hv.
  unfold isRecvEvt, isDeqEvt in Hmrecrr.
  destruct (eKind Emr); inversion Hmrecrr; [].
  simpl in Hv, Hmeq. unfold getPayload in Hv.
  simpl in Hv. simpl in Hmeq. 
  rewrite <- Hmeq in Hv.
  simpl in Hv.
  clear Hql.
  specialize (fun tl => Hv tl (conj Hlt (conj eq_refl HmotR))).
  pose proof (QVelPosLB tstate _ _ (Qlt_le_weak _ _ Hltt) 
                                (inject_Z (1))) 
      as Hvb.
  rewrite reactionTime1 in Hv.
  specialize ( Hvb Hv).
  clear Hv. unfold centerPosAtTime in HLB.
  remember ({tstate} (Qtadd (eTime Emr) (mkQTime 1 I))) as qta.
  unfold Qtadd in Hltt.
  simpl in Hltt.
  assert ( [0] [<=] {tstate} t[-]qta) as HH0 by
     (eapply  leEq_transitive; eauto;
      rewrite <- inj_Q_Zero;
      apply inj_Q_leEq;
      simpl; unfold inject_Z; simpl; lra).
  pose proof (plus_resp_leEq_both _ _ _ _ _ HH0 HLB) as Hf.
  rewrite <- cg_cancel_mixed in Hf.
  pose proof (leEq_transitive _ _ _ _ Hf Hc) as XX.
  rewrite <- inj_Q_Zero in XX.
  rewrite <- inj_Q_plus in XX.
  apply leEq_inj_Q in XX.
  simpl in XX. unfold inject_Z in XX.
  lra.
Qed.


Coercion Z2R : Z >-> st_car.

Lemma TrainSafe : 
    forall t: Time,  |(centerPosAtTime tstate t)| [<=] 95.
Proof.
  intros.
  apply AbsSmall_imp_AbsIR.
  split.
- apply TContRR2QLB. intro qt. unfold Z2R. rewrite <- inj_Q_inv.
  apply LHSSafe.
- apply TContRR2QUB.
  exact RHSSafe.
Qed.




End TrainProofs.