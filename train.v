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
Definition right := true.

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

Definition getVelM  : Message -> option Q :=
  getPayLoad MOTOR.

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



Definition getVelEv (e : Event) : option Q  :=
  getPayloadFromEv MOTOR e.

Definition getVelOEv : (option Event) ->  option Q  :=
getPayloadFromEvOp MOTOR.


Definition getVelAndTime (oev : option Event) 
    : option (Q * Event)  :=
getPayloadAndEv MOTOR oev.


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
       (distanceAtTime t  [<=] alertDist)
       -> ∃ n, ∃ ev,
          evs n = Some ev /\ isSendEvt ev /\
            (ProxPossibleTimeEvPair maxDelay side t) ev)
    /\
    (∀ (n: nat), 
        isSendEvtOp (evs n)
        -> ∃ t : QTime,  Cast (distanceAtTime t  [<=]  alertDist)
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

Definition velocityMessages (t : QTime) :=
  (filterPayloadsUptoTime MOTOR (localEvts BASEMOTOR) t).

Definition lastVelAndTime (evs : nat -> option Event)
  (t : QTime) : (Q * QTime) :=
hd (initialVel,mkQTime 0 I) (map (fun p => (fst p, eTime (snd p)))
                                  (velocityMessages t)) .


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
| true => (fun ts t => (rboundary [-] (rEndPos ts t)))
| false => (fun ts t => ((lEndPos ts t) [-] lboundary))
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
  -> {es : Event | {ed : Event | isDeqEvt ed & isSendEvt es
          & (nd < ns)%Q
            & (∀ n : nat, (nd < n <  ns)%Q → isEnqEvtOp (localEvts SWCONTROLLER n))
              & (eTime ed < eTime es < eTime ed + digiControllerTiming)%Q
        &
        localEvts SWCONTROLLER nd = Some ed 
        & localEvts SWCONTROLLER ns = Some es &
         {dmp : bool|  eMesg ed = ((mkMesg PSENSOR dmp)::nil)
                  ∧ (mkMesg MOTOR ((SwControllerProgram sp) dmp))::nil = (eMesg es) }}}.
Proof.
  intros ? ? ? Hnc.
  apply PureProcDeqSendOncePair in Hnc.
  simpl in Hnc.
  destruct Hnc as [es Hnc].
  destruct Hnc as [ed Hnc].
  exists es. exists ed.  simpl.
  exrepd. 
  pose proof (noSpamRecv eo i) as Hvr.
  dands; trivial.
  rewrite <- locEvtIndex in e.
  TrimAndRHS e. rewrite e in Hvr.
  simpl in Hvr. 
  specialize (s Hvr). clear Hvr. trivial.
Qed.

Lemma swControllerMessages : 
  forall es : Event,
  SWCONTROLLER = eLoc es
  -> sendEvt = eKind es
  -> {(eMesg es) = (mkMesg MOTOR speed)::nil}
      + {(eMesg es) = (mkMesg MOTOR (-speed))::nil}.
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
  rewrite  e0 in Hiff. inversion Hiff as [Heq]. clear Hiff.
  subst.
  destruct dmp;[right | left];
  simpl in H2; inversion H2; reflexivity.
Qed.


(** this is a correct proof; only temporarily wrong *)
Lemma velMessages:
  forall n : nat,
     match getVelOEv (motorEvents n) with
     | Some v => {v = speed} + {v = (-speed)}
     | None => True
     end.
Proof.
  intros n.
  unfold motorEvents,getVelOEv, getPayloadFromEvOp, getPayloadFromEv.
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


Lemma centerPosChangeQAux : forall (ta tb : QTime),
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


(** this proof is not possible when [ta] and [tb] are
    rationals *)
Lemma centerPosChangeQ : forall (ta tb : QTime),
  ta <= tb
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
  rewrite QT2T_Q2R in Hlt.
  rewrite QT2T_Q2R in Hlt.
  apply getFTimeProper with (tf:= tstate)in Hlt.
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
  apply centerPosChangeQAux in Htlt.
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
                       /\ alertDist =  (inject_Z 16)
                      /\ maxDelay = mkQTime 1 I
                      /\ reactionTime = 1
                      /\ initialVel = (-1%Z)
                      /\ initialPos = 0.
Admitted.

Lemma reactionTimeLt : reactionTime < minGap.
Admitted.

Definition posVelMeg : list Message :=
  (mkMesg MOTOR speed)::nil.

Definition MotorRecievesPositivVelAtLHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => 
            isDeqEvt ev
              -> (eMesg ev) = posVelMeg
              -> (centerPosAtTime tstate (eTime ev)) [<=]  Z2R (-78)
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt => 
                (eMesg ev) = posVelMeg
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-79)
            | deqEvt => 
                (eMesg ev) = (mkMesg PSENSOR false)::nil
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-80)
            | _ => True
            end
| _ => True
end.

Ltac SensorMsgInvert Hmd :=
    (apply (f_equal (hd (mkMesg PSENSOR false))) in Hmd;
    simpl in Hmd;
    apply (f_equal getSensorSide) in Hmd;
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
    fold (inBetween (eTime ed) (eTime es0) (eTime ed + 1)) in Hnc.
    exrepd. rename e into H4. rename e0 into H5.
    pose proof (sameLocCausal eo _ _ _ H4 H5 q) as Hcaus.
    clear q.
    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hiff.
    TrimAndRHS Hiff.
    rewrite Hiff in H5; auto;[].
    inversion H5 as [Heqs].  clear H5.
    symmetry in Heqs. subst es0. rename H0 into H7.
    rewrite <- H7. intro Heq. clear H7.
    inversion Heq as [Heqq]. clear Heq.
    apply (f_equal getVelM) in Heqq.
    simpl in Heqq. inversion Heqq as [Heq]. clear Heqq.
    unfold speed in Heq.
    destruct dmp; simpl in Heq;[inversion Heq; fail| clear Heq].
    specialize (Hind ed Hcaus). clear Hiff. clear Hcaus.
    unfold MotorRecievesPositivVelAtLHS in Hind.
    apply locEvtIndex in H4. repnd. subst m. 
    rewrite H4l in Hind. clear H4l. rewrite i in Hind.
    rename H into H6.
    specialize (Hind H6). clear H6.
    unfold inBetween in i2.
    clear Heqeks Heqevloc eo reactionTimeGap transitionValues velAccuracy boundary 
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
    SensorMsgInvert Hmd.
    inverts Hncl as Hncl.
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
    clear tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime  alertDist minGap.
    apply shift_leEq_plus in Hncl.
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
              -> Z2R (78) [<=]  (centerPosAtTime tstate (eTime ev))
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt => 
                (eMesg ev) = negVelMeg
                -> Z2R (79) [<=] (centerPosAtTime tstate (eTime ev))
            | deqEvt => 
                (eMesg ev) = (mkMesg PSENSOR true)::nil
                -> Z2R (80) [<=] (centerPosAtTime tstate (eTime ev))
            | _ => True
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
    fold (inBetween (eTime ed) (eTime es0) (eTime ed + 1)) in Hnc.
    exrepd. rename e into H4. rename e0 into H5.
    pose proof (sameLocCausal eo _ _ _ H4 H5 q) as Hcaus.
    clear q.
    pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hiff.
    TrimAndRHS Hiff.
    rewrite Hiff in H5; auto;[].
    inversion H5 as [Heqs].  clear H5.
    symmetry in Heqs. subst es0. rename H0 into H7.
    rewrite <- H7. intro Heq. clear H7.
    inversion Heq as [Heqq]. clear Heq.
    apply (f_equal getVelM) in Heqq.
    simpl in Heqq. inversion Heqq as [Heq]. clear Heqq.
    unfold speed in Heq.
    destruct dmp; simpl in Heq;[clear Heq| inversion Heq; fail].
    specialize (Hind ed Hcaus). clear Hiff. clear Hcaus.
    unfold MotorRecievesNegVelAtRHS in Hind.
    apply locEvtIndex in H4. repnd. subst m. 
    rewrite H4l in Hind. clear H4l. rewrite i in Hind.
    rename H into H6.
    specialize (Hind H6). clear H6.
    unfold inBetween in i2.
    clear Heqeks Heqevloc eo reactionTimeGap transitionValues velAccuracy boundary 
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
    SensorMsgInvert Hmd.
    inverts Hncl as Hncl.
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
    clear tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime  alertDist minGap.
    rewrite CAbGroups.minus_plus in Hncl.
    apply shift_leEq_plus in Hncl.
    apply minusSwapLe in Hncl.
    eapply leEq_transitive; eauto. clear dependent cpt.
    unfold Z2R. unfold inject_Z.
    unfold Q2R, Z2R.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_minus.
    apply inj_Q_leEq.
    simpl. unfold cg_minus. simpl.
     lra.
Qed.




Lemma velocityMessagesAuxMsg: forall upto mt,
  member mt (filterPayloadsUptoIndex MOTOR (localEvts BASEMOTOR) upto)
  -> {fst mt  = speed} + {fst mt = (-speed)}.
Proof.
  induction upto as [ | upt Hind]; simpl; intros mt Hmem;[contradiction|].
  pose proof (velMessages upt) as Hvm.
  unfold getPayloadAndEv, getPayloadFromEv in Hmem.
  unfold getVelOEv, getPayloadFromEvOp, 
    getPayloadFromEv, motorEvents in Hvm. simpl in Hvm.
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

Lemma posVelAtLHS : forall evp,
  getPayloadFromEv MOTOR evp = Some speed
  -> eLoc evp = BASEMOTOR
  -> (centerPosAtTime tstate (eTime evp)) [<=]  Z2R (-78).
Proof.
  intros ? Hp Hl.
  pose proof (PosVelAtLHSAux evp) as Hev.
  unfold MotorRecievesPositivVelAtLHS in Hev.
  rewrite Hl in Hev.
  pose proof (getPayloadFromEvSpecMesg MOTOR) as Hd.
  simpl in Hd.
  specialize (Hd _ _ Hp). repnd.
  specialize (Hev Hdl Hdr).
  trivial.
Qed.
  
Lemma negVelAtRHS : forall evp,
  getPayloadFromEv MOTOR evp = Some (-speed)
  -> eLoc evp = BASEMOTOR
  -> Z2R (78) [<=] (centerPosAtTime tstate (eTime evp)) .
Proof.
  intros ? Hp Hl.
  pose proof (NegVelAtRHSAux evp) as Hev.
  unfold MotorRecievesNegVelAtRHS in Hev.
  rewrite Hl in Hev.
  pose proof (getPayloadFromEvSpecMesg MOTOR) as Hd.
  simpl in Hd.
  specialize (Hd _ _ Hp). repnd.
  specialize (Hev Hdl Hdr).
  trivial.
Qed.

Definition priorMotorMesg (vel: Q) (t : QTime):=
(λ ev : Event,
         eTime ev < t
         ∧ getPayloadFromEv MOTOR ev = Some vel 
          ∧ eLoc ev = BASEMOTOR).

Lemma motorLastPosVelAux : forall (lm : list (Q * Event)) (t : QTime),
  (Q2R 1) [<=] (centerPosAtTime tstate t)
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
      unfold Z2R, Q2R.
      apply inj_Q_leEq.
      unfold inject_Z. simpl.
      lra.
Qed.

(** in the aux version, lm was there only for induction.
    lets get rid of it*)
Lemma motorLastPosVel: forall (t : QTime),
  (Q2R 1) [<=] (centerPosAtTime tstate t)
  -> sig (latestEvt 
              (fun ev =>  eTime ev < t 
                    /\ getPayloadFromEv MOTOR ev = Some speed
                    /\  eLoc ev = BASEMOTOR)).
Proof.
  intros. eapply motorLastPosVelAux; eauto.
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
  rewrite <- Hsendll in XXl.
  rewrite <- XXl in Hsendlrrl.
  specialize (Hsendlrl _ (or_introl eq_refl)).
  specialize (Hsendlrrl _ (or_introl eq_refl)).
  rewrite Hl in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite RemoveOrFalse in Hsendlrrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite <- Hsendlrrl in Hsendlrl.
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
  rewrite <- Hsendll in XXl.
  rewrite <- XXl in Hsendlrrl.
  specialize (Hsendlrl _ (or_introl eq_refl)).
  specialize (Hsendlrrl _ (or_introl eq_refl)).
  rewrite Hl in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite RemoveOrFalse in Hsendlrrl.
  unfold validSendMesg in Hsendlrrl.
  simpl in Hsendlrrl.
  rewrite <- Hsendlrrl in Hsendlrl.
  destruct (eLoc Er); simpl in Hsendlrl;
    try rewrite RemoveOrFalse in Hsendlrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.

Lemma timeDiffLB : forall (ts te : Time) (ps pe : R),
  {tstate} ts [<=] ps
  -> pe [<=] {tstate} te
  -> ts [<=] te
  -> ps [<] pe
  -> (pe[-]ps) [<=] te [-] ts.
Proof.
  intros ? ? ? ? Htl Htr Hte Hplt.
  assert ({tstate} ts [<] {tstate} te) as Hlt by eauto 4 with CoRN.
  apply pfstrlt in Hlt; trivial;[].
  pose proof (minus_resp_leEq_both _ _ _ _ _ Htr Htl).
  eapply leEq_transitive; eauto.
  apply centerPosChange.
  trivial.
Qed.



Lemma latestPosAfterNegM : forall evMp evMn t (n:nat),
  priorMotorMesg (-speed) t evMn
  -> (latestEvt (priorMotorMesg speed t)) evMp
  -> (eTime evMp < eTime evMn)
  -> (S (eLocIndex evMn) <= n)%nat
  -> let lm := filterPayloadsUptoIndex MOTOR (localEvts BASEMOTOR) n in
     match lm with
     | hdp::tlp =>
          eTime (snd hdp) < t -> (fst hdp) = -speed
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
  destruct (getPayloadFromEv MOTOR ev); inverts Heqoplev.
  simpl in Hplt. simpl.
  intro Hcc. assert (eTime evMp < eTime ev);[| lra].
  clear Hcc.
  symmetry in Heqoev. apply locEvtIndex in Heqoev.
  repnd.
  fold (lt (eLocIndex evMn) np) in Hnp.
  rewrite <- Heqoevr  in Hnp.
  apply timeIndexConsistent in Hnp.
  lra.
Qed.


Lemma RHSSafe : forall t: QTime,  (centerPosAtTime tstate t) [<=] Z2R 95.
Proof.
  intros. apply leEq_def. intros Hc.
  apply less_leEq in Hc.
  assert (Z2R 1[<=]centerPosAtTime tstate t) as Hle1 by
  (eapply leEq_transitive; eauto; unfold Z2R, inject_Z
    ;apply inj_Q_leEq; simpl;  lra).
  apply motorLastPosVel in Hle1.
  destruct Hle1 as [evMp Hlat].
  pose proof (Hlat) as Hlatb.
  unfold latestEvt in Hlat. apply proj1 in Hlat.
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
  pose proof (timeDiffLB _ _ _ _ HUB Hc Htppt) as Htlt.
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
Close Scope nat_scope.
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
    apply inj_Q_leEq; unfold cg_minus; simpl; lra].
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

  pose proof (eventualDelivery eo  Hncrl) as Hrec.
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

  assert ((eTime Eswr) < tivt + (2 # 1))  as Htubb by lra.
  clear Htub. rename Htubb into Htub.
  assert (tivt < (eTime Eswr))  as Htlb by lra.
  clear Hreclr Hrecll Hncrrr Hncrl Hrecrl Hnclr Hncll Htppt
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
  specialize (Hnc Hrecrr).
  destruct Hnc as [m Hnc].
  apply DeqSendOncePair in Hnc.
  simpl in Hnc. 
  destruct Hnc as [es0 Hnc].
  destruct Hnc as [ed Hnc].
  exrepd. rewrite ((proj1 Hxx) (conj Hsw eq_refl)) in e.
  symmetry in e. inverts e.
  rename es0 into Esws.
  rewrite <- Hmeq in H1.
  SensorMsgInvert H1. subst.
  clear Hmeq.
  rename H2 into Hmot.
  simpl in Hmot.
  
  (** got the msg sent received by sw. 
      lets update the time bounds *)

  assert ((eTime Esws) < tivt + (3 # 1))  as Htubb by lra.
  clear Htub. rename Htubb into Htub.
  assert (tivt < (eTime Esws))  as Htlbb by lra.
  clear Htlb. rename Htlbb into Htlb.
  rename e0 into Hss.
  apply locEvtIndex in Hss.
  clear H0 H i i1 q Hrecrr Hxx Hsw Eswr.

  rename i0 into HmotSend.

  (** let's receive the -speed message on the motor *)
  
  pose proof (eventualDelivery eo  HmotSend) as Hmrec.
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

  assert ((eTime Emr) < tivt + (4 # 1))  as Htubb by lra.
  clear Htub. rename Htubb into Htub.
  assert (tivt < (eTime Emr))  as Htlbb by lra.
  clear Htlb. rename Htlbb into Htlb.
  clear dependent Esws.
  apply (centerPosUB _ _ _ _ (conj Htlb Htub)) in HUB.
  revert HUB. simplInjQ. intro HUB.
  assert ((eTime Emr) < t) as Hlt by lra.

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
