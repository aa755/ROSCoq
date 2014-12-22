Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Add LoadPath "../../../nuprl/coq".

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

Definition digiControllerTiming (speed : Q) : 
  QTime :=  (N2QTime 1).
 
Definition ControllerNode (speed : Q): RosSwNode :=
  Build_RosSwNode (SwProcess speed) (digiControllerTiming speed).

Record Train : Type := {
  posX : TimeFun;
  velX : TimeFun;
  deriv : isDerivativeOf velX posX
}.


Lemma VelPosUB :forall (tst : Train)
   (ta tb : Time) (Hab : ta[<]tb) (c : R),
   (forall (t:Time), (clcr ta tb) t -> ({velX tst} t) [<=] c)
   -> ({posX tst} tb[-] {posX tst} ta)[<=]c[*](tb[-]ta).
Proof.
  intros. apply TDerivativeUB2 with (F' := (velX tst)); auto.
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
       (distanceAtTime t  [<] Q2R alertDist)
       -> ∃ n, opLiftF (ProxPossibleTimeEvPair maxDelay side t) (evs n))
    /\
    (∀ (n: nat), 
        isSendEvtOp (evs n)
        -> ∃ t : QTime,  Cast (distanceAtTime t  [<]  Q2R alertDist)
                /\ opLiftF (ProxPossibleTimeEvPair maxDelay side t) (evs n)).

Definition inIntervalDuringInterval
  (interval intervalT: interval)  (f : Time -> R) : Prop
      :=
 Cast (forall t : Time, intervalT t  -> (interval) (f t)).
  

Variable reactionTime : Q.
Variable velAccuracy : R.
Variable initialVel : Q.
Variable initialPos : Q.
Variable transitionValues : interval.
Definition correctVelDuring
  (lastVel : Q) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (velAtTime: Time -> R) :=
    exists  qt : QTime, 
      lastTime <= qt <= (lastTime + reactionTime)
      /\(inIntervalDuringInterval 
                          transitionValues
                          (clcr (Q2R lastTime) (Q2R qt))
                          velAtTime)
      /\ (inIntervalDuringInterval 
                          (nbdAround (Q2R lastVel) velAccuracy) 
                          (clcr  (Q2R qt) (Q2R uptoTime))
                          velAtTime).

Close Scope Q_scope.


(** let k geatest m much that m < n 
   and (evs m) is a velocity message.
   this returns the vlocity and time of (evs k) *)
Fixpoint lastVelAndTimeAux (evs : nat -> option Event) 
    (n : nat) : (Q * QTime):=
match n with
| 0 => (initialVel,N2QTime 0)
| S n' => match getVelAndTime (evs n') with
          | Some pr => pr
          | None => lastVelAndTimeAux evs n'
           end
end.
  

Definition lastVelAndTime (evs : nat -> option Event)
  (t : QTime) : (Q * QTime) :=
lastVelAndTimeAux evs (lastEvtIndex evs t) .


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
  (nbdAround [0] (Q2R speed [+] velAccuracy)).

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
  - exact (fun srs dest => Some (N2QTime 1)).
Defined.


Open Scope R_scope.

Variable tstate : Train.
Variable eo : (@PossibleEventOrder _  tstate minGap _ _ _ _ _ _ _ _ _).

Definition  TrainSpec (t:Time) : Prop :=
    ((lEndPos tstate t) [-] safeDist [>=] lboundary )
    /\((rEndPos tstate t) [+] safeDist [<=] rboundary ).

Definition motorEvents : nat -> option Event 
   := localEvts BASEMOTOR.

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
              ∧ (eTime ed < eTime es < eTime ed + digiControllerTiming sp)%Q
        ∧
        localEvts SWCONTROLLER nd = Some ed 
        ∧ localEvts SWCONTROLLER ns = Some es ∧ 
         exists dmp : bool,  eMesg ed = ((mkMesg PSENSOR dmp)::nil)
                  ∧ (mkMesg MOTOR ((SwControllerProgram sp) dmp))::nil = (eMesg es) }}.
Proof.
  intros ? ? ? Hnc.
  apply PureProcDeqSendOncePair in Hnc.
  simpl in Hnc.
  destruct Hnc as [es Hnc].
  destruct Hnc as [ed Hnc].
  exists es. exists ed.
  remember (eTime ed < eTime es
               ∧ eTime es < eTime ed + digiControllerTiming sp) as dontSPlit.
  exrepd.
  pose proof (noSpamRecv eo H) as Hvr.
  split;[ trivial |].
  split;[ trivial |].
  split;[ trivial |].
  split;[ trivial |].
  split;[ trivial |].
  split;[ trivial |].
  split;[ trivial |]. clear H0 H1 H2 H3 H5.
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
  (** someone must have sent this message
      which is contained in the receive (enque)
      event evEnq. let the sent message
      be [sm] and the corresponding event be [es] *)
(* 
  pose proof (recvSend eo ev) as Hrecv.
  repnd.
  destruct Hrecv as [es Hrecv];
    [ apply (deqIsRecvEvt  _ Heqom) |].
  TrimAndRHS Hrecv.
  unfold PossibleSendRecvPair in Hrecv.
  rewrite (deqMesgSome _ Heqom ) in Hrecv.
  remember (eKind es) as eks.
  destruct eks; try contradiction;[].
  simpl in Hrecv.
  repnd. clear Hrecvrrr.
  (** since [BASEMOTOR] only receives on [MOTOR]
      topic, the message [sm] must have that topic *)
  unfold validRecvMesg in Hrecvrl.
  simpl in Hrecvrl.
  unfold validSendMesg in Hrecvrrl.
  rewrite Hrecvl in Hrecvrrl.
 remember (eLoc es) as sloc.
  (** Only [SWCONTROLLER] sends on that topic *)
  destruct sloc; simpl in Hrecvrrl;
    try contradiction;
    inversion Hrecvrrl; 
    try discriminate;
    try contradiction.
  clear H Hrecvrrl.
  apply swControllerMessages in Heqeks;
    [| trivial].
  rewrite <- Hrecvl. trivial.
Qed.
*)

Abort.

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

Definition MotorRecievesPositivVelAtLHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => 
            isDeqEvt ev
              -> (eMesg ev) = (mkMesg MOTOR speed)::nil
              -> (centerPosAtTime tstate (eTime ev)) [<=] [0]
| SWCONTROLLER => 
            match eKind ev with
            | sendEvt => 
                (eMesg ev) = (mkMesg MOTOR speed)::nil
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-1)
            | deqEvt => 
                (eMesg ev) = (mkMesg PSENSOR false)::nil
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-2)
            | _ => True
            end
| _ => True
end.

(** Ideally, device specs should imply a bound like this.
    For a fine grained analysis, this might be less useful *)
Lemma velPos : forall (t : Time), 
  ({velX tstate} t) [<=] Q2R speed.
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

Lemma centerPosChangeQ : forall (ta tb : QTime),
  ta < tb
  -> (centerPosAtTime tstate tb [-] centerPosAtTime tstate ta) [<=] Q2R (tb -ta).
Proof.
  intros.
Admitted.

Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring IRisaRing: (CRing_Ring IR).
Add Ring RisaRing: (CRing_Ring R).
Require Import Psatz.



Open Scope Q_scope.
Lemma centerPosUB : forall (ts tf td : QTime) (ps : R),
  ts < tf < ts + td
  -> centerPosAtTime tstate ts[<=] ps
  -> centerPosAtTime tstate tf[<=] (ps [+] Q2R td).
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

Lemma centerPosUB2 : forall (ts tf td : QTime) (pf: Q),
  (ts < tf < (ts + td))
  -> centerPosAtTime tstate ts[<=] (Q2R (pf-td))
  -> centerPosAtTime tstate tf[<=] (Q2R pf).
Proof.
  intros ? ? ? ?  Hint Hcs.
  apply centerPosUB with (td:= (td)) (tf:=tf) in Hcs; [| trivial; fail].
  eapply leEq_transitive; eauto. clear Hcs Hint.
  unfold Q2R. rewrite <- inj_Q_plus.
  apply inj_Q_leEq.
  simpl. lra.
Qed.

(*
Lemma centerPosUB3 : forall (ts tf td : QTime) (pf: R),
  (ts < tf < (ts + td))
  -> centerPosAtTime tstate ts[<=] (pf [-] Q2R (td))
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

Definition inBetween (l m r: Q) := l < m < r.

Lemma inBetweenFold : forall (l m r: Q),
   l < m < r <-> (inBetween l m r).
Proof. intros. reflexivity.
Qed.

  
Lemma concreteValues : hwidth = Z2R 2 
                       /\ boundary = Z2R 100 
                       /\ alertDist =  1
                      /\ maxDelay = N2QTime 1.
Admitted.

Lemma  PosVelAtNegPos : forall (ev : Event),
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
    safeDist maxDelay hwidth reactionTime initialVel
    initialPos minGap. repnd. clear Hsendlrrrl.
  rewrite <- inj_Q_Zero.
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
    remember (eTime ed < eTime es0
               ∧ eTime es0 < eTime ed + digiControllerTiming speed) as dontSplit.

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
      alertDist safeDist maxDelay hwidth reactionTime initialVel initialPos.
    subst dontSplit.
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
Require Export Coq.Program.Tactics.
Require Export LibTactics.
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
    repnd. subst.
    unfold centerPosAtTime.
    remember ({posX tstate} t) as cpt.
    clear dependent t.
    clear dependent Event.
    clear Hconrrr Hconrrl Hconrl Hconl tstate reactionTimeGap 
        maxDelay transitionValues velAccuracy boundary safeDist 
        hwidth  reactionTime initialVel initialPos alertDist minGap.
    apply shift_leEq_plus in Hncl.
    eapply leEq_transitive; eauto. clear dependent cpt.
    rewrite <- inj_Q_Zero.
    unfold Q2R, Z2R.
    rewrite <- inj_Q_minus.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_plus.
    apply inj_Q_leEq.
    simpl. unfold cg_minus. simpl.
    simpl. unfold N2QTime. unfold QT2Q.
    simpl. unfold inject_Z. simpl. lra.
Qed.

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
