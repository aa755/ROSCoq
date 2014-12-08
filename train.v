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

Inductive RosLoc := 
 BASEMOTOR | LEFTPSENSOR | RIGHTPSENSOR | SWCONTROLLER.

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
  (maxDelay: R) (side : bool)
  (t: Time) (ev: Event) 
  :=
  Cast ((olcr t (t [+] maxDelay)) (Q2R (eTime ev)))
  /\ (eMesg ev) = (mkMesg PSENSOR side)::nil.

(** [side] is just an identifier *)
Definition ProximitySensor (alertDist maxDelay: R) (side : bool)
  : Device R :=
fun  (distanceAtTime : Time -> R)
     (evs : nat -> option Event) 
  =>
    (∀ t:Time,
       (distanceAtTime t  [>]  alertDist)
       -> ∃ n, opLiftF (ProxPossibleTimeEvPair maxDelay side t) (evs n))
    /\
    (∀ (n: nat), 
        isSendEvtOp (evs n)
        -> ∃ t : Time,  Cast (distanceAtTime t  [>]  alertDist)
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

Variable alertDist : R.
Variable safeDist : R.
Variable maxDelay : R.
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



Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| BASEMOTOR => DeviceSemantics (fun ts => getF (velX ts)) SlowMotorQ
| LEFTPSENSOR => DeviceSemantics
                    (fun ts t => AbsIR ((lEndPos ts t) [-] lboundary))
                    (ProximitySensor alertDist maxDelay true)
| RIGHTPSENSOR => DeviceSemantics
                    (fun ts t => AbsIR ((rEndPos ts t) [-] rboundary))
                    (ProximitySensor alertDist maxDelay false)
| SWCONTROLLER => RSwSemantics (ControllerNode speed)
end.

Definition locTopics (rl : RosLoc) : TopicInfo :=
match rl with
| BASEMOTOR => ((MOTOR::nil), nil)
| LEFTPSENSOR => (nil, (PSENSOR::nil))
| RIGHTPSENSOR => (nil, (PSENSOR::nil))
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
  unfold possibleDeqSendOncePair in Hnc.
  rewrite Hiff in Hnc.
  remember (localEvts SWCONTROLLER mDeq) as oevD.
  destruct oevD as [evD |]; [| contradiction].
  destruct Hnc as [Hdeq  Hnc].
  repeat(TrimAndLHS Hnc).
  pose proof (noSpamRecv eo Hdeq) as Hvr.
  symmetry in HeqoevD.
  rewrite <- locEvtIndex in HeqoevD.
  TrimAndRHS HeqoevD.
  rewrite HeqoevD in Hvr.
  simpl in Hvr. unfold validRecvMesg in Hvr.
  unfold ControllerNode, SwProcess in Hnc.
  simpl in Hnc.
  rewrite getNewProcLPure in Hnc.
  pose proof (deqSingleMessage _ Hdeq) as Hmm.
  destruct Hmm as [mm Hmm]. repnd.
  rewrite <- Hmml in Hvr.
  simpl in Hvr. specialize (Hvr _ (or_introl  eq_refl)).
  unfold getDeqOutput in Hnc.
  simpl in Hnc. rewrite Hmmr in Hnc.
  simpl in Hnc.
  rewrite RemoveOrFalse in Hvr.
  unfold liftToMesg, getPayLoad in Hnc.
  destruct mm as [mt mp].
  simpl in Hvr. destruct mt; inversion Hvr.
  simpl in Hnc. simpl in mp.
  destruct mp;[right | left];
  simpl in Hnc; inversion Hnc; reflexivity.
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
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-2)
            | deqEvt => 
                (eMesg ev) = (mkMesg PSENSOR false)::nil
                -> (centerPosAtTime tstate (eTime ev)) [<=] Z2R (-4)
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
    apply qSubLt in Hsendlrrrr.
    rename Hsendlrrrr into Hqlt.
    apply centerPosChangeQ in Htlt.
    remember (centerPosAtTime tstate evt) as cpvt. clear Heqcpvt.
    remember (centerPosAtTime tstate est) as cpst. clear Heqcpst.
    apply inj_Q_less with (R1:=R)  in Hqlt.
    unfold Q2R in Htlt.
    apply (leEq_less_trans _ _ _ _ Htlt) in Hqlt ; eauto.
    clear Htlt est evt.
    unfold Z2R in Hsendrl.
    apply less_leEq in Hqlt.
    eapply (plus_resp_leEq_both _ _ _ _ _ Hsendrl) in Hqlt; eauto.
    clear Hsendrl. rename Hqlt into hh.
    rewrite realCancel in hh.
    eapply leEq_transitive; eauto. clear hh.
    rewrite <- inj_Q_plus.
    rewrite <- inj_Q_Zero.
    apply inj_Q_leEq.
    simpl. unfold Qplus. simpl.
    lra.

  - rename ev into es. remember (eKind es) as eks.
    destruct eks; [|auto|].
    + symmetry in Heqeks.
      pose proof (corrNodes 
                  eo 
                  SWCONTROLLER 
                  (eLocIndex es)) as Hnc.
      
      pose proof (locEvtIndex SWCONTROLLER (eLocIndex es) es) as Hxx.
      TrimAndRHS Hxx. rewrite Hxx in Hnc;[| split; auto; fail].
      simpl  in Hnc. TrimAndRHS Hnc.
      specialize (Hnc Heqeks).
      destruct Hnc as [m Hnc].
      unfold possibleDeqSendOncePair in Hnc.
      rewrite Hxx in Hnc;[| split; auto; fail].
      clear Hxx. remember (localEvts SWCONTROLLER m) as oed.
      destruct oed as [ed |];[| contradiction].
      simpl in Hnc. unfold digiControllerTiming in Hnc.
      repnd. admit.
      

    + admit.
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
