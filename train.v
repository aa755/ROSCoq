Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.

Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Instance stringdeceqdsjfklsajlk : DecEq string.
constructor. exact string_dec.
Defined.

Inductive Topic :=  MOTOR | PSENSOR.

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


Inductive Void :=.


(** When adding a nrew topic, add cases of this function *)
Definition topic2Type (t : Topic) : Type :=
match t with
| MOTOR => Q
| PSENSOR => bool
end.


Instance  ttttt : @RosTopicType Topic _.
  constructor. exact topic2Type.
Defined.

Definition left := false.
Definition right := false.

Inductive RosLoc := 
 BASEMOTOR | PROXSENSOR (b:bool) | SWCONTROLLER.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.

Open Scope Q_scope.

(** it is a pure function that repeatedly
   reads a message from the [PSENSOR] topic
   and publish on the [MOTOR] *)
Definition SwControllerProgram (speed : Q):
  SimplePureProcess PSENSOR MOTOR :=
fun side  => match side with
            | true => -speed
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
  QTime :=  (mkQTime 1 I).
 
Definition ControllerNode (speed : Q): RosSwNode :=
  Build_RosSwNode (SwProcess speed) (digiControllerTiming).

Variable initialVel : Q.
Variable initialPos : Q.

Record Train : Type := {
  posX :> TimeFun;
  velX : TimeFun;
  deriv : isDerivativeOf velX posX;
    (** this probably already implies continuity, which is now
        explicitly put in TimeFun *)
  initVel : {velX} (mkQTime 0 I)  = initialVel;
  initPos : {posX} (mkQTime 0 I)  = initialPos
}.


Lemma VelPosUB :forall (tst : Train)
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   (forall (t:Time), (clcr ta tb) t -> ({velX tst} t) [<=] c)
   -> ({posX tst} tb[-] {posX tst} ta)[<=]c[*](tb[-]ta).
Proof.
  intros. apply TDerivativeUB2 with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Lemma VelPosLB :forall (tst : Train)
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   (forall (t:Time), (clcr ta tb) t -> c [<=] ({velX tst} t))
   -> c[*](tb[-]ta)[<=] ({posX tst} tb[-] {posX tst} ta).
Proof.
  intros. apply TDerivativeLB2 with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Lemma QVelPosUB :forall (tst : Train)
   (ta tb : QTime) (Hab : ta<=tb) (c : Q),
   (forall (t:QTime), (ta <= t <= tb) -> ({velX tst} t) [<=] c)
   -> ({posX tst} tb[-] {posX tst} ta)[<=] c*(tb-ta).
Proof.
  intros. unfold Q2R.
  rewrite inj_Q_mult.
  rewrite inj_Q_minus.
  apply TDerivativeUBQ with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Lemma QVelPosLB :forall (tst : Train)
   (ta tb : QTime) (Hab : ta<=tb) (c : Q),
   (forall (t:QTime), (ta <= t <= tb) -> Q2R c [<=] ({velX tst} t))
   -> Q2R (c*(tb-ta))[<=] ({posX tst} tb[-] {posX tst} ta).
Proof.
  intros. unfold Q2R.
  rewrite inj_Q_mult.
  rewrite inj_Q_minus.
  apply TDerivativeLBQ with (F' := (velX tst)); auto.
  apply deriv.
Qed.

Definition getVelM (m : Message ) : option Q :=
  getPayLoad MOTOR m.

Definition getSensorSide (m : Message ) : option bool :=
  getPayLoad PSENSOR m.

Definition getProxSide (m : Message) : option bool :=
  getPayLoad PSENSOR m.

Section TrainProofs.

(** To define IO devices, we already need
    an Event type *)
Context  
  (minGap : Qpos)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


(** In some cases, the equations might invove transcendental 
  functions like sine, cos which can output 
  irrationals even on rational *)


Definition getVel (e : Event) : option Q :=
opBind getVelM (deqMesg e).


Definition getVelFromEv (oev : Event) : option Q  :=
opBind getVelM (deqMesg oev).

Definition getVelFromMsg : (option Event) ->  option Q  :=
opBind getVelFromEv.


Definition getVelAndTime (oev : option Event) 
    : option (Q * QTime)  :=
match oev with
| Some ev => match getVel ev with
             | Some vq => Some (vq, eTime ev)
             | None => None
             end
| None => None
end.

Definition ProxPossibleTimeEvPair 
  (maxDelay: QTime) (side : bool)
  (t: QTime) (ev: Event) 
  :=
   t < (eTime ev) < (t + maxDelay) 
  /\ (eMesg ev) = (mkMesg PSENSOR side)::nil.

(** [side] is just an identifier *)
Definition ProximitySensor (alertDist : Q) (maxDelay: QTime) (side : bool)
  : Device R :=
fun  (distanceAtTime : Time -> R)
     (evs : nat -> option Event) 
  =>
    (∀ t:QTime,
       (distanceAtTime t  [<] alertDist)
       -> ∃ n, opLiftF (ProxPossibleTimeEvPair maxDelay side t) (evs n))
    /\
    (∀ (n: nat), 
        isSendEvtOp (evs n)
        -> ∃ t : QTime,  Cast (distanceAtTime t  [<]  alertDist)
                /\ opLiftF (ProxPossibleTimeEvPair maxDelay side t) (evs n)).

Definition inIntervalDuring
  (interval: interval) (tStart tEnd : QTime)  (f : Time -> R) : Prop :=
  Cast (forall t : QTime, ( tStart <= t <= tEnd   -> (interval) (f t))).
  
Definition isEqualDuring
  (vel: Q) (tStart tEnd : QTime)  (f : Time -> R) : Prop :=
  (forall t : QTime, ( tStart <= t <= tEnd   -> (f t) [=] vel)).

Variable reactionTime : Q.
Variable velAccuracy : Q.
Variable transitionValues : interval.

(*
Notation "a <== b <== c" := ((a [<=] b) /\ (b [<=] c)) 
  (at level 201,left associativity).
*)

Definition between (b a c : IR) := ((a [<=] b) /\ (b [<=] c)) .

Definition correctVelDuring
  (lastVel : Q) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (velAtTime: Time -> R) :=

exists  (qt : QTime), 
  lastTime <= qt <= (lastTime + reactionTime)
  /\ ((forall t : QTime, (qt <= t <= uptoTime -> (velAtTime t) [=] lastVel)))
  /\ (forall t : QTime, (lastTime <= t <= qt)  
          -> (between (velAtTime t) (velAtTime lastTime) lastVel)).
  
Close Scope Q_scope.


(** all velocity messages whose index  < numPrevEvts .
    the second item is the time that messsage was dequed.
    last message, if any  is the outermost (head)
    Even though just the last message is needed,
    this list is handy for reasoning; it is a convenient
    thing to do induction over
 *)
Fixpoint velocityMessagesAux (evs : nat -> option Event) 
    (numPrevEvts : nat) : list (Q * QTime):=
match numPrevEvts with
| 0 => nil
| S numPrevEvts' => match getVelAndTime (evs numPrevEvts') with
          | Some pr => pr::(velocityMessagesAux evs numPrevEvts')
          | None => velocityMessagesAux evs numPrevEvts'
           end
end.
  
Definition velocityMessages
  (evs : nat -> option Event) (t : QTime) : list (Q * QTime):=
velocityMessagesAux evs (numPrevEvts evs t).

Definition lastVelAndTime (evs : nat -> option Event)
  (t : QTime) : (Q * QTime) :=
hd (initialVel,mkQTime 0 I) (velocityMessages evs t) .


Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime) 
  (velAtTime: Time -> R) :=
  let (lastVel, lastTime) := lastVelAndTime evs uptoTime in
  correctVelDuring lastVel lastTime uptoTime velAtTime.


Definition SlowMotorQ 
   : Device R :=
fun  (velAtTime: Time -> R) (evs : nat -> option Event) 
  => forall t: QTime, corrSinceLastVel evs t velAtTime.


Variable boundary : R.

Definition rboundary : R := (boundary).
Definition lboundary : R := ([0] [-] boundary).

Variable alertDist : Q.
Variable safeDist : R.
Variable maxDelay : QTime.
Variable hwidth : R. (* half of width *)
Definition speed : Q := 1.

Open Scope Q_scope.

Variable reactionTimeGap : reactionTime < minGap.
Definition lEndPos (ts : Train) (t : Time) : R :=
  (getF (posX ts) t [-]  hwidth).

Definition rEndPos (ts : Train) (t : Time) : R :=
  (getF (posX ts) t [+]  hwidth).

Definition velAtTime (ts : Train) (t : Time) : R :=
  (getF (velX ts) t).

Definition centerPosAtTime (ts : Train) (t : Time) : R :=
  (getF (posX ts) t).

Definition velBound : interval :=
  (nbdAround [0] (speed [+] velAccuracy)).

Definition transitionInterval : interval :=
  velBound.


Definition proxView (side :bool) :=
match side with
| true => (fun ts t => AbsIR ((rEndPos ts t) [-] rboundary))
| false => (fun ts t => AbsIR ((lEndPos ts t) [-] lboundary))
end.


Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| BASEMOTOR => DeviceSemantics (fun ts => getF (velX ts)) SlowMotorQ
| PROXSENSOR  side=> DeviceSemantics
                    (proxView side)
                    (ProximitySensor alertDist maxDelay side)
| SWCONTROLLER => RSwSemantics (ControllerNode speed)
end.


Definition locTopics (rl : RosLoc) : TopicInfo :=
match rl with
| BASEMOTOR => ((MOTOR::nil), nil)
| PROXSENSOR _ => (nil, (PSENSOR::nil))
| SWCONTROLLER => ((PSENSOR::nil), (MOTOR::nil))
end.

Instance rllllfjkfhsdakfsdakh : @RosLocType Train Topic Event  RosLoc _.
  apply Build_RosLocType.
  - exact locNode.
  - exact locTopics.
  - exact (fun srs dest => Some (mkQTime 1 I)).
Defined.


Open Scope R_scope.

Variable tstate : Train.
Variable eo : (@PossibleEventOrder _  tstate minGap _ _ _ _ _ _ _ _ _).

Definition  TrainSpec (t:Time) : Prop :=
    ((lEndPos tstate t) [-] safeDist [>=] lboundary )
    /\((rEndPos tstate t) [+] safeDist [<=] rboundary ).

Definition motorEvents : nat -> option Event 
   := localEvts BASEMOTOR.

Lemma QVelPosLe :forall (tst : Train)
   (ta tb : QTime) (Hab : ta<=tb),
   (forall (t:QTime), (ta <= t <= tb) -> ({velX tst} t) [<=] Q2R 0)
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

Lemma QVelPosLeIf :forall (tst : Train) (c : IR)
   (ta tb : QTime) (Hab : ta<=tb),
   (forall (t:QTime), (ta <= t <= tb) -> ({velX tst} t) [<=] Q2R 0)
   -> c [<=] {posX tst} tb
   -> c [<=] {posX tst} ta.
Proof.
  intros ? ? ? ? ? Hq Hc.
  apply QVelPosLe in Hq; auto.
  eauto using leEq_transitive.
Qed.

(*
Lemma motorOnlyReceives:
  forall n : nat,
  match motorEvents n with
  | Some ev => isRecvEvt ev
  | None => True
  end.
Proof.
  intros n.
  unfold motorEvents.
  pose proof (corrNodes eo BASEMOTOR) as Hnc.
  unfold NodeBehCorrect in Hnc.
  simpl in Hnc.
  unfold DeviceBehaviourCorrect in Hnc.
  unfold SlowMotorQ in Hnc.
*)  


(** need to force deque events to happen
    and also within acceptable time.
    right now, the motor can disregard
    all messages *)

Lemma DeqSendOncePair : forall ns nd sp,
  possibleDeqSendOncePair (ControllerNode sp) (localEvts SWCONTROLLER) nd ns
  -> {es : Event | {ed : Event | isDeqEvt ed ∧ isSendEvt es
          ∧ (nd < ns)%Q
            ∧ (∀ n : nat, (nd < n)%Q ∧ (n < ns)%Q → isEnqEvtOp (localEvts SWCONTROLLER n))
              ∧ (eTime ed < eTime es < eTime ed + digiControllerTiming)%Q
        ∧
        localEvts SWCONTROLLER nd = Some ed 
        ∧ localEvts SWCONTROLLER ns = Some es ∧ 
         exists (dmp : bool),  eMesg ed = ((mkMesg PSENSOR dmp)::nil)
                  ∧ (mkMesg MOTOR ((SwControllerProgram sp) dmp))::nil = (eMesg es) }}.
Proof.
  intros ? ? ? Hnc.
  apply PureProcDeqSendOncePair in Hnc.
  simpl in Hnc.
  destruct Hnc as [es Hnc].
  destruct Hnc as [ed Hnc].
  exists es. exists ed.  simpl.
  exrepd. 
  pose proof (noSpamRecv eo H) as Hvr.
  dands; trivial.

  clear H0 H1 H2 H3 H5.
  rename H4 into H0.
  rename H6 into H2.
  rewrite <- locEvtIndex in H0.
  TrimAndRHS H0. rewrite H0 in Hvr.
  simpl in Hvr. 
  specialize (H2 Hvr). clear Hvr. trivial.
Qed.

Lemma swControllerMessages : 
  forall es : Event,
  SWCONTROLLER = eLoc es
  -> sendEvt = eKind es
  -> (eMesg es) = (mkMesg MOTOR speed)::nil
      \/ (eMesg es) = (mkMesg MOTOR (-speed))::nil.
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
  unfold opApPure, isSendEvt in Hnc.
  rewrite <- Hsend in Hnc.
  specialize (Hnc eq_refl). destruct Hnc as [mDeq  Hnc].
  apply DeqSendOncePair in Hnc.
  simpl in Hnc. exrepd. 
  rewrite  H5 in Hiff. inversion Hiff as [Heq]. clear Hiff.
  subst.
  destruct dmp;[right | left];
  simpl in H8; inversion H8; reflexivity.
Qed.


(** this is a correct proof; only temporarily wrong *)
Lemma velMessages:
  forall n : nat,
     match getVelFromMsg (motorEvents n) with
     | Some v => v = speed \/ v = (-speed)
     | None => True
     end.
Proof.
  intros n.
  unfold motorEvents.
  unfold getVelFromMsg.
  unfold getVelFromEv.
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
  pose proof (recvSend eo Heqom) as Hrecv.
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
  specialize (Hrecvrl _ (or_introl eq_refl)).
  rewrite  RemoveOrFalse in Hrecvrl.
  unfold validSendMesg in Hrecvrrl.
  rewrite Hrecvl in Hrecvrrl.
  remember (eLoc es) as sloc.
  rewrite <- Hem in Hrecvrrl.
  specialize (Hrecvrrl _ (or_introl eq_refl)).
  rewrite <- Hrecvrl in Hrecvrrl.
  (** Only [SWCONTROLLER] sends on that topic *)
  destruct sloc; simpl in Hrecvrrl;
  try rewrite RemoveOrFalse in Hrecvrrl.
    try contradiction;
    try discriminate.

  discriminate.
  clear Hrecvrrl. unfold isSendEvt in Hsend.
  symmetry in Hsend.
  apply swControllerMessages in Hsend;
    [| trivial].
  rewrite Hrecvl in Hsend.
  rewrite <- Hem in Hsend.
  destruct Hsend as [Hsend | Hsend]; inverts Hsend; simpl; auto.
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
  rewrite <- Hsendll in XXl.
  rewrite <- XXl in Hsendlrrl.
  specialize (Hsendlrl _ (or_introl eq_refl)).
  rewrite Hl in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl.
  specialize (Hsendlrrl _ (or_introl eq_refl)).
  rewrite <- Hsendlrl in Hsendlrrl.
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
  rewrite <- Hsendll in XXl.
  rewrite <- XXl in Hsendlrrl.
  specialize (Hsendlrl _ (or_introl eq_refl)).
  rewrite Hl in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl.
  specialize (Hsendlrrl _ (or_introl eq_refl)).
  rewrite <- Hsendlrl in Hsendlrrl.
  destruct (eLoc Es); simpl in Hsendlrrl;
    try contradiction;
    try rewrite  RemoveOrFalse in Hsendlrrl; 
    try discriminate;
    try contradiction.
  exists b. reflexivity.
Qed.

(** Ideally, device specs should imply a bound like this.
    For a fine grained analysis, this might be less useful *)
Lemma velPos : forall (t : Time), 
  Q2R (-speed) [<=] ({velX tstate} t) /\ ({velX tstate} t) [<=] speed.
Admitted.


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

Add Ring IRisaRing: (CRing_Ring IR).
Add Ring RisaRing: (CRing_Ring R).
Require Import Psatz.
Require Import Setoid.


Lemma centerPosChangeQ : forall (ta tb : QTime),
  ta < tb
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



Open Scope Q_scope.
Lemma centerPosUB : forall (ts tf : QTime) (td : Q) (ps : R),
  ts < tf < ts + td
  -> centerPosAtTime tstate ts[<=] ps
  -> centerPosAtTime tstate tf[<=] (ps [+] td).
Proof.
  intros ? ? ? ? Hint Hcs.
  repnd.
  apply qSubLt in Hintr.
  rename Hintl into Htlt.
  apply centerPosChangeQ in Htlt.
  remember (centerPosAtTime tstate tf) as cpvt. clear Heqcpvt.
  remember (centerPosAtTime tstate ts) as cpst. clear Heqcpst.
  rename Hintr into Hqlt.
  apply inj_Q_less with (R1:=R)  in Hqlt.
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

Lemma minusInvQ : forall a b:Q, [--](a[-]b)[=](b[-]a).
Proof.
  intros. unfold cg_minus.
  simpl. ring.
Qed.

Lemma centerPosLB : forall (ts tf : QTime) (td : Q) (ps : R),
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

  
Lemma concreteValues : hwidth = Z2R 2 
                       /\ boundary = Z2R 100 
                       /\ alertDist =  1
                      /\ maxDelay = mkQTime 1 I
                      /\ reactionTime = 1
                      /\ initialVel = (-1%Z)
                      /\ initialPos = 0.
Admitted.

Definition posVelMeg : list Message :=
  (mkMesg MOTOR speed)::nil.

Definition MotorRecievesPositivVelAtLHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => 
            isDeqEvt ev
              -> (eMesg ev) = posVelMeg
              -> (centerPosAtTime tstate (eTime ev)) [<=]  Z2R (-91)
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt => 
                (eMesg ev) = posVelMeg
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-92)
            | deqEvt => 
                (eMesg ev) = (mkMesg PSENSOR false)::nil
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-93)
            | _ => True
            end
| _ => True
end.



Lemma  PosVelAtNegLHS : forall (ev : Event),
          MotorRecievesPositivVelAtLHS ev.
Proof.
  induction ev as [ev Hind] using 
    (@well_founded_induction_type Event (causedBy eo) (causalWf eo)) .
  unfold MotorRecievesPositivVelAtLHS.
  remember (eLoc ev) as evloc.
  destruct evloc; simpl; auto.

- intro Hdeqx. pose proof (recvSend eo Hdeqx) as Hsend.
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
  rewrite Hsendrr in Hsendrl.
  rewrite Hsendll in Hsendrl.
  parallelForall Hsendrl. clear x.
  remember (eTime ev) as evt. clear Heqevt.
  remember (eTime Es) as est. clear Heqest.
  simpl in Hsendrl.
  clear dependent Event.
  clear  reactionTimeGap
    transitionValues velAccuracy boundary alertDist
    safeDist maxDelay hwidth reactionTime
    minGap. repnd. clear Hsendlrrrl.
  eapply centerPosUB2; eauto.

- rename ev into es. remember (eKind es) as eks.
  destruct eks; [|auto|].
  + symmetry in Heqeks.
    pose proof (corrNodes 
                eo 
                SWCONTROLLER 
                (eLocIndex es)) as Hnc.

    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hxx.
    TrimAndRHS Hxx. rewrite Hxx in Hnc;[| split; auto; fail].
    simpl  in Hnc. TrimAndRHS Hnc. clear Hxx.
    specialize (Hnc Heqeks).
    destruct Hnc as [m Hnc].
    apply DeqSendOncePair in Hnc.
    simpl in Hnc. 
    destruct Hnc as [es0 Hnc].
    destruct Hnc as [ed Hnc].
    rewrite inBetweenFold in Hnc.
    exrepd. clear H2.
    pose proof (sameLocCausal eo _ _ _ H4 H5 H1) as Hcaus.
    clear H1.
    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hiff.
    TrimAndRHS Hiff.
    rewrite Hiff in H5; auto;[].
    inversion H5 as [Heqs].  clear H5.
    symmetry in Heqs. subst es0.
    rewrite <- H7. intro Heq. clear H7.
    inversion Heq as [Heqq]. clear Heq.
    apply (f_equal getVelM) in Heqq.
    simpl in Heqq. inversion Heqq as [Heq]. clear Heqq.
    unfold speed in Heq.
    destruct dmp; simpl in Heq;[inversion Heq; fail| clear Heq].
    specialize (Hind ed Hcaus). clear Hiff. clear Hcaus.
    unfold MotorRecievesPositivVelAtLHS in Hind.
    apply locEvtIndex in H4. repnd. subst m. 
    rewrite H4l in Hind. clear H4l. rewrite H in Hind.
    specialize (Hind H6). clear H6.
    unfold digiControllerTiming in H3.
    clear H0 H Heqeks Heqevloc eo reactionTimeGap transitionValues velAccuracy boundary 
      alertDist safeDist maxDelay hwidth reactionTime.
    eapply centerPosUB2; eauto.

  + clear Hind. symmetry in Heqeks. rename es into ed.
    pose proof (recvSend eo Heqeks) as Hsend.
    destruct Hsend as [Es Hsend].
    repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
    symmetry in Heqevloc.
    pose proof  (SwOnlyRecievesFromSensor _ _ 
      Hsendrr Heqeks Hsendl Heqevloc) as Hsw.
    exrepd.
    unfold PossibleSendRecvPair in Hsendl.
    repnd. clear Hsendlrrl Hsendlrl.
    rewrite Heqevloc in Hsendlrrr.
    rewrite side0 in Hsendlrrr. simpl in Hsendlrrr.
    rewrite <- Hsendll. intros Hmd.
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
    apply (f_equal (hd (mkMesg PSENSOR false))) in Hmd.
    simpl in Hmd.
    apply (f_equal getSensorSide) in Hmd.
    simpl in Hmd. 
    apply (f_equal (fun op => opExtract op false)) in Hmd.
    simpl in Hmd.
    inverts Hncl as Hncl.
    subst. unfold proxView in Hncl.
    apply less_leEq in Hncl.
    rewrite AbsIR_minus in Hncl.
    apply AbsIR_bnd in Hncl.
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
    clear tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime  alertDist minGap.
    apply shift_leEq_plus in Hncl.
    eapply leEq_transitive; eauto. clear dependent cpt.
    rewrite <- inj_Q_Zero.
    unfold Q2R, Z2R.
    rewrite <- inj_Q_minus.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_plus.
    apply inj_Q_leEq.
    simpl. unfold cg_minus. simpl.
    simpl.  unfold QT2Q.
    simpl. unfold inject_Z. simpl. lra.
Qed.

Definition negVelMeg : list Message :=
  (mkMesg MOTOR (-speed))::nil.

Definition MotorRecievesNegVelAtRHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => 
            isDeqEvt ev
              -> (eMesg ev) = negVelMeg
              -> Z2R (91) [<=]  (centerPosAtTime tstate (eTime ev))
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt => 
                (eMesg ev) = negVelMeg
                -> Z2R (92) [<=] (centerPosAtTime tstate (eTime ev))
            | deqEvt => 
                (eMesg ev) = (mkMesg PSENSOR true)::nil
                -> Z2R (93) [<=] (centerPosAtTime tstate (eTime ev))
            | _ => True
            end
| _ => True
end.

Lemma  NegVelAtNegRHS : forall (ev : Event),
          MotorRecievesNegVelAtRHS ev.
Proof.
  induction ev as [ev Hind] using 
    (@well_founded_induction_type Event (causedBy eo) (causalWf eo)).
  unfold MotorRecievesNegVelAtRHS.
  remember (eLoc ev) as evloc.
  destruct evloc; simpl; auto.


- intro Hdeqx. pose proof (recvSend eo Hdeqx) as Hsend.
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
  rewrite Hsendrr in Hsendrl.
  rewrite Hsendll in Hsendrl.
  parallelForall Hsendrl. clear x.
  remember (eTime ev) as evt. clear Heqevt.
  remember (eTime Es) as est. clear Heqest.
  simpl in Hsendrl.
  clear dependent Event.
  clear  reactionTimeGap
    transitionValues velAccuracy boundary alertDist
    safeDist maxDelay hwidth reactionTime
    minGap. repnd. clear Hsendlrrrl.
  eapply centerPosLB2; eauto.

- rename ev into es. remember (eKind es) as eks.
  destruct eks; [|auto|].
  + symmetry in Heqeks.
    pose proof (corrNodes 
                eo 
                SWCONTROLLER 
                (eLocIndex es)) as Hnc.

    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hxx.
    TrimAndRHS Hxx. rewrite Hxx in Hnc;[| split; auto; fail].
    simpl  in Hnc. TrimAndRHS Hnc. clear Hxx.
    specialize (Hnc Heqeks).
    destruct Hnc as [m Hnc].
    apply DeqSendOncePair in Hnc.
    simpl in Hnc. 
    destruct Hnc as [es0 Hnc].
    destruct Hnc as [ed Hnc].
    rewrite inBetweenFold in Hnc.
    exrepd. clear H2.
    pose proof (sameLocCausal eo _ _ _ H4 H5 H1) as Hcaus.
    clear H1.
    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hiff.
    TrimAndRHS Hiff.
    rewrite Hiff in H5; auto;[].
    inversion H5 as [Heqs].  clear H5.
    symmetry in Heqs. subst es0.
    rewrite <- H7. intro Heq. clear H7.
    inversion Heq as [Heqq]. clear Heq.
    apply (f_equal getVelM) in Heqq.
    simpl in Heqq. inversion Heqq as [Heq]. clear Heqq.
    unfold speed in Heq.
    destruct dmp; simpl in Heq;[clear Heq| inversion Heq; fail].
    specialize (Hind ed Hcaus). clear Hiff. clear Hcaus.
    unfold MotorRecievesNegVelAtRHS in Hind.
    apply locEvtIndex in H4. repnd. subst m. 
    rewrite H4l in Hind. clear H4l. rewrite H in Hind.
    specialize (Hind H6). clear H6.
    unfold digiControllerTiming in H3.
    clear H0 H Heqeks Heqevloc eo reactionTimeGap transitionValues velAccuracy boundary 
      alertDist safeDist maxDelay hwidth reactionTime.
    eapply centerPosLB2; eauto.

  + clear Hind. symmetry in Heqeks. rename es into ed.
    pose proof (recvSend eo Heqeks) as Hsend.
    destruct Hsend as [Es Hsend].
    repnd. pose proof (globalCausal _ _ _ Hsendrl) as Htlt.
    symmetry in Heqevloc.
    pose proof  (SwOnlyRecievesFromSensor _ _ 
      Hsendrr Heqeks Hsendl Heqevloc) as Hsw.
    exrepd.
    unfold PossibleSendRecvPair in Hsendl.
    repnd. clear Hsendlrrl Hsendlrl.
    rewrite Heqevloc in Hsendlrrr.
    rewrite side0 in Hsendlrrr. simpl in Hsendlrrr.
    rewrite <- Hsendll. intros Hmd.
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
    apply (f_equal (hd (mkMesg PSENSOR false))) in Hmd.
    simpl in Hmd.
    apply (f_equal getSensorSide) in Hmd.
    simpl in Hmd. 
    apply (f_equal (fun op => opExtract op false)) in Hmd.
    simpl in Hmd.
    inverts Hncl as Hncl.
    subst. unfold proxView in Hncl.
    apply less_leEq in Hncl.
    apply AbsIR_bnd in Hncl.
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
    clear tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime  alertDist minGap.
    rewrite <- plus_assoc_unfolded in Hncl.
    apply shift_minus_leEq in Hncl.
    eapply leEq_transitive; eauto. clear dependent cpt.
    unfold Z2R. unfold inject_Z.
    unfold Q2R, Z2R.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_minus.
    apply inj_Q_leEq.
    simpl. unfold cg_minus. simpl.
     lra.
Qed.



Definition latestEvt (P : Event -> Prop) (ev : Event) :=
  P ev /\ (forall ev':Event, P ev' -> (eTime ev) <= (eTime ev')).

Lemma velocityMessagesMsg: forall upto mt,
  member mt (velocityMessagesAux (localEvts BASEMOTOR) upto)
  -> {fst mt  = speed} + {fst mt = (-speed)}.
Proof.
  induction upto as [ | upt Hind]; simpl; intros mt Hmem;[contradiction|].
  pose proof (velMessages upt) as Hvm.
  unfold getVelAndTime, getVel in Hmem.
  unfold getVelFromMsg, getVelFromEv, motorEvents in Hvm.
  destruct (localEvts BASEMOTOR upt) as [ev|]; simpl in Hvm, Hmem;
    [| auto; fail].
  destruct (opBind getVelM (deqMesg ev)) as [vel|];
    [| auto; fail].
  simpl in Hmem.
  destruct Hmem as [Hmem| Hmem];[auto;fail| subst].
  simpl. 

Abort.


Lemma velocityMessagesMsg: forall m t,
  member m (velocityMessages (localEvts BASEMOTOR) t)
  -> {fst m  = speed} + {fst m = (-speed)}.
Proof.
  intros mt t. revert mt.
  unfold velocityMessages.
  
  
Admitted.

Lemma velocityMessagesEv : forall m t,
  member m (velocityMessages (localEvts BASEMOTOR) t)
  -> sig (fun ev=> (eMesg ev) = ((mkMesg MOTOR (fst m))::nil)
                /\ eTime ev < t
                /\ eTime ev = (snd m)
                /\ eLoc ev = BASEMOTOR
                /\ isDeqEvt ev).
Admitted.

Lemma latestEvtStr: forall  (PS P : Event -> Prop) (ev : Event),
   PS ev
   -> (forall ev, PS ev -> P ev)
   -> latestEvt P ev
   -> latestEvt PS ev.
Admitted.

Lemma velocityMessagesLatest : forall m lm  t,
   (m::lm = velocityMessages (localEvts BASEMOTOR) t)
  -> sig (fun ev=> (eMesg ev) = ((mkMesg MOTOR (fst m))::nil)
                /\ latestEvt (fun ev' => eTime ev' < t) ev
                /\ eTime ev = (snd m)
                /\ lm = velocityMessages (localEvts BASEMOTOR) (snd m)
                /\ eLoc ev = BASEMOTOR
                /\ isDeqEvt ev).
Admitted.


Lemma motorLastPosVel : forall (lm : list (Q * QTime)) (t : QTime),
  (Q2R 1) [<=] (centerPosAtTime tstate t)
  -> lm = velocityMessages (localEvts BASEMOTOR) t
  -> sig (latestEvt 
              (fun ev =>  eTime ev < t /\ (eMesg ev = posVelMeg) 
                          /\  eLoc ev = BASEMOTOR)).
Proof.
  intro.
  induction lm as [|hlm tlm Hind]; intros ? Hcent Heq.
- simpl. assert False;[| contradiction].
  pose proof (corrNodes 
                eo 
                BASEMOTOR t) as Hm.
  simpl in Hm.
  unfold corrSinceLastVel, lastVelAndTime, correctVelDuring in Hm.
  rewrite <- Heq in Hm. unfold last in Hm.
  pose proof concreteValues as Hinit.
Open Scope nat_scope.
  AndProjN 4 Hinit as Hrt.
  AndProjN 5 Hinit as Hv.
  AndProjN 6 Hinit as Hp.
Close Scope nat_scope.
  clear Hinit. 
  subst. clear Hrt Heq. unfold hd in Hm.
  rewrite (initVel tstate) in Hm.
  destruct Hm as [qtrans Hm]. repnd.
  
  eapply QVelPosLeIf with (ta:=(mkQTime 0 I)) in Hcent; auto;
    [|apply qtimePos|].
  + rewrite initPos in Hcent.
    rewrite Hp in Hcent.
    unfold Q2R in Hcent.
    apply leEq_inj_Q in Hcent.
    simpl in Hcent.
    lra.
  + intros qt H0t. 
    pose proof (Qlt_le_dec qt qtrans) as Hd.
    destruct Hd as [Hd|Hd];[clear Hmrl | clear Hmrr].
    apply Qlt_le_weak in Hd.
    * rewrite Hv in Hmrr. specialize (Hmrr qt (conj (proj1 H0t) Hd)).
      unfold between in Hmrr.
      apply proj2 in Hmrr.
      eapply leEq_transitive; eauto.
      apply inj_Q_leEq.
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
  rewrite <- Heq in Hm.
  match type of Heq with
  | ?h::_ = ?r => assert (member h r) as Hvm;
      [rewrite <- Heq; simpl; right; reflexivity|]
  end.
  apply velocityMessagesMsg in Hvm.
  pose proof Heq as Hlat.
  apply velocityMessagesLatest in Hlat.
  destruct Hlat as [ev Hlat].
  destruct Hvm as [Hvm | Hvm].
  + clear Hm Hind. 
    exists ev.
    rewrite Hvm in Hlat.
    fold (posVelMeg) in Hlat. repnd.
    apply latestEvtStr with (P:= (λ ev' : Event, eTime ev' < t));
      dands; auto;[|tauto].
    exact (proj1 Hlatrl).

  + unfold hd in Hm.
    destruct hlm as [hq ht].
    simpl in Hvm. simpl in Hlat.
    simpl in Hlat. repnd.
    specialize (fun gt => Hind ht gt Hlatrrrl).
    lapply Hind;[clear Hind; intros Hind|].
    * destruct Hind as [evInd Hind]. exists evInd.
      unfold latestEvt in Hlatrl, Hind. repnd.
      rewrite Hlatrrl in Hlatrll.
      split; [dands; auto; eauto using Qlt_trans|].
      (* use Heq and Hvm *) admit.


    * trivial. (* use Hvm and something like [PosVelAtNegPos] *)
      subst hq ht.
      pose proof (NegVelAtNegRHS ev) as Hev.
      unfold MotorRecievesNegVelAtRHS in Hev.
      rewrite Hlatrrrrl  in Hev.
      specialize (Hev Hlatrrrrr Hlatl).
      eapply leEq_transitive;[ | apply Hev].
      unfold Z2R, Q2R.
      apply inj_Q_leEq.
      unfold inject_Z. simpl.
      lra.
Qed.





Lemma RHSSafe : forall t: QTime,  (centerPosAtTime tstate t) [<=] Z2R 95.
Proof.
  intros. apply leEq_def. intros Hc.
Abort.
  
  



(*
Lemma  TrainVelBounded : forall (e : Event) (t: QTime),
    t <= (eTime e)
   -> velBound (velAtTime tstate t).
Proof.
  induction e using 
    (@well_founded_induction_type Event (causedBy eo) (causalWf eo)).

  pose proof (corrNodes 
                  eo 
                  BASEMOTOR t) as Hnc.
  unfold corrSinceLastVel in Hnc.
Abort.
*)  


Close Scope R_scope.
Close Scope Q_scope.
Add LoadPath "../../../nuprl/coq".
Require Import UsefulTypes.
(* Close Scope NupCoqScope. *)



Open Scope R_scope.
Close Scope Q_scope.




End TrainProofs.

(** To begin with, let the VelControl device control position
    make it exact if needed *)

(** need to add sequence numbers in timer messages and keep
    track of it in the controller sw *)

(** N2R commuted with addition *)
