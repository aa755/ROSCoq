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


(** it is a pure function that repeatedly
   reads a message from the [PSENSOR] topic
   and publish on the [MOTOR] *)
Definition SwControllerProgram (speed : Q):
  SimplePureProcess PSENSOR MOTOR :=
fun side  => match side with
            | true => 0 - speed
            | false => speed
            end.

Definition SwProcess (speed : Q):= 
  mkPureProcess (liftToMesg (SwControllerProgram speed)).

Definition digiControllerTiming (speed : Q) : 
  ProcessTiming (SwProcess speed) :=
 fun m => (N2QTime 1).

Definition ControllerNodeAux (speed : Q): RosSwNode :=
  Build_RosSwNode (digiControllerTiming speed).


 

Record Train := mkSt {
  posX : TimeFun;
  velX : TimeFun;
  deriv : isDerivativeOf velX posX
}.


Definition getVelM (m : Message ) : option Q :=
getPayLoad MOTOR m.


Section TrainProofs.

(** To define IO devices, we already need
    an Event type *)
Context  
  (minGap : Qpos)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


Definition ControllerNode (speed : Q):  @RosNode _ _ _ Event.
  constructor.
  - exact (Build_TopicInfo (PSENSOR::nil) (MOTOR::nil)).
  - left. exact (ControllerNodeAux speed).
Defined.

(** In some cases, the equations might invove transcendental 
  functions like sine, cos which can output 
  irrationals even on rational *)


Definition getVel (e : Event) : option Q :=
match (eKind e) with
| deqEvt => getVelM (eMesg e)
| _ => None
end.


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


(** [side] is just an identifier *)
Definition ProximitySensor (alertDist maxDelay: R) (side : bool)
  : @Device Event R :=
fun  (distanceAtTime : Time -> R)  
     (evs : nat -> option Event) 
    =>
      (forall t:Time,
         (distanceAtTime t  [>]  alertDist)
         -> exists n,
              match (evs n) with
            | Some ev => Cast ((olcr t (t [+] maxDelay)) (Q2R (eTime ev)))
                  /\ isSendOnTopic PSENSOR (fun b => b = side) ev
            | None => False
            end)
      /\
      (forall (n: nat),
            match (evs n) with
            | Some ev => isSendOnTopic PSENSOR (fun b => b = side) ev
                         /\ exists (t : QTime),
                              Cast ((olcr (Q2R t) ((Q2R t) [+] maxDelay)) (Q2R (eTime ev)))
                         /\ Cast (distanceAtTime t  [>]  alertDist)
            | None => False
            end).


Definition inIntervalDuringInterval
  (interval intervalT: interval)  (f : Time -> R) : Prop
      :=
 Cast (forall t : Time, intervalT t  -> (interval) (f t)).
  
Require Export Coq.Unicode.Utf8.

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
   : @Device Event R :=
fun  (velAtTime: Time -> R) (evs : nat -> option Event) 
  => forall t: QTime, corrSinceLastVel evs t velAtTime.


Variable boundary : R.

Definition rboundary : R := (boundary).
Definition lboundary : R := ([0] [-] boundary).

Variable alertDist : R.
Variable safeDist : R.
Variable maxDelay : R.
Variable hwidth : R. (* half of width *)
Variable speed : Q.

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



Definition locNode (rl : RosLoc) : RosNode :=
match rl with
| BASEMOTOR =>
     {| topicInf:=
        (Build_TopicInfo (MOTOR::nil) nil);
        rnode := (inr  (existT  _ _ 
                (SlowMotorQ))) |}
| LEFTPSENSOR => 
     {| topicInf:=
          (Build_TopicInfo nil (PSENSOR::nil));
           rnode := (inr  (existT  _ _ 
               (ProximitySensor alertDist maxDelay true)))|}
| RIGHTPSENSOR => 
     {| topicInf:=
          (Build_TopicInfo nil (PSENSOR::nil));
           rnode := (inr  (existT  _ _ 
               (ProximitySensor alertDist maxDelay false)))|}

| SWCONTROLLER => ControllerNode speed
end.

Instance rllllfjkfhsdakfsdakh : 
   @RosLocType _ _ _ Event Train RosLoc _.
apply (Build_RosLocType _ _ _ 
         locNode (fun srs dest => Some (N2QTime 1))).
 intros ts rl. remember rl as rll. destruct rll; simpl; try (exact tt);
  unfold TimeValuedPhysQType; simpl.
  - exact (getF (velX ts)).
  - intro t. exact (AbsIR ((lEndPos ts t) [-] lboundary)).
  - intro t. exact (AbsIR ((rEndPos ts t) [-] rboundary)).
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


Ltac TrimAndRHS Hyp :=
let H99 := fresh "H99" in 
destruct Hyp as [Hyp H99]; clear H99.

Ltac TrimAndLHS Hyp :=
let H99 := fresh "H99" in 
destruct Hyp as [H99 Hyp]; clear H99.

Ltac repnd :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] =>
            let lname := fresh H "l" in 
            let rname := fresh H "r" in 
              destruct H as [lname rname]
         end.

(** need to force deque events to happen
    and also within acceptable time.
    right now, the motor can disregard
    all messages *)

Lemma swControllerMessages : 
  forall es : Event,
  SWCONTROLLER = eLoc es
  -> sendEvt = eKind es
  -> match getVelM (eMesg es) with
     | Some v => v = speed \/ v = (0-speed)
     | None => True
     end.
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
  rewrite <- Hsend in Hnc.
  remember 
    (prevProcessedEvents 
        (S (eLocIndex es)) 
        (localEvts SWCONTROLLER)) 
    as prevProcs.
  destruct prevProcs as [|last procEvts];
  simpl in Hnc; [contradiction|].
  unfold SwProcess in Hnc.
  rewrite getLastOutputPure in Hnc.
  TrimAndRHS Hnc.
  unfold SwControllerProgram in Hnc.
  unfold liftToMesg in Hnc.
  destruct (getPayLoad PSENSOR (eMesg last));
    simpl in Hnc;[| contradiction].
  destruct Hnc as [Hnc | ?]; [| contradiction].
  rewrite <- Hnc.
  simpl. destruct t;[right| left]; reflexivity.
Qed.


(** this is a correct proof; only temporarily wrong *)
Lemma velMessages:
  forall n : nat,
     match getVelFromMsg (motorEvents n) with
     | Some v => v = speed \/ v = (0-speed)
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
(*  remember (eLoc es) as sloc.
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

Definition MotorRecievesPositivVelAtLHS (ev : Event)  :=
match (eLoc  ev) with
| BASEMOTOR => match getVelFromEv ev with
               | Some v => v = speed
                  -> (centerPosAtTime tstate (eTime ev)) [<] [0]
               | None => True
               end
| SWCONTROLLER => match getVelM (eMesg ev) with
                  | Some v => v = speed
                              ->
                              match eKind ev with
                              | sendEvt => 
                                  (centerPosAtTime tstate (eTime ev)) [<] Z2R (0-2)
                              | deqEvt => 
                                  (centerPosAtTime tstate (eTime ev)) [<] Z2R (0-4)
                              | _ => True
                              end
                  | None => True
                  end
| _ => True
end.

Lemma RemoveOrFalse : forall A , A \/ False <-> A.
Proof.
  tauto.
Qed.


Lemma MotorOnlyReceivesFromSw :   forall Es Er,
  PossibleSendRecvPair Es Er
  -> eLoc Er = BASEMOTOR
  -> eLoc Es = SWCONTROLLER.
Proof.
  intros ? ? Hsendl Hl.
  unfold PossibleSendRecvPair in Hsendl.
  remember (eKind Es) as eKs.
  destruct eKs; try contradiction;[].
  destruct (eKind Er); try contradiction;[].
  repnd.
  rewrite  Hl in Hsendlrl.
  simpl in Hsendlrl.
  unfold validRecvMesg in Hsendlrl.
  simpl in Hsendlrl.
  rewrite RemoveOrFalse in Hsendlrl.
  unfold validSendMesg in Hsendlrrl.
  rewrite Hsendll in Hsendlrrl.
  rewrite <- Hsendlrl in Hsendlrrl.
  destruct (eLoc Es); simpl in Hsendlrrl;
    try contradiction;
    inversion Hsendlrrl; 
    try discriminate;
    try contradiction.
  reflexivity.
Qed.


Lemma  PosVelAtNegPos : forall (ev : Event),
          MotorRecievesPositivVelAtLHS ev.
Proof.
  induction ev as [ev Hind] using 
    (@well_founded_induction_type Event (causedBy eo) (causalWf eo)) .
  unfold MotorRecievesPositivVelAtLHS.
  remember (eLoc ev) as evloc.
  destruct evloc; simpl; auto.
  - unfold getVelFromEv. unfold deqMesg.
    remember (eKind ev) as eks.
    destruct eks; simpl; auto.
    pose proof (recvSend eo ev) as Hsend.
    unfold isRecvEvt in Hsend.
    rewrite <- Heqeks in Hsend.
    specialize (Hsend I).
    destruct Hsend as [Es Hsend].
    repnd.
    apply Hind in Hsendr. clear Hind.
    (** topic subscrions and topology say that [Es] must have
        happened at [SWCONTROLLER] *)
    symmetry in Heqevloc.
    pose proof  (MotorOnlyReceivesFromSw _ _ Hsendl Heqevloc) as Hsw.
    unfold PossibleSendRecvPair in Hsendl.
    rewrite <- Heqeks in Hsendl.
    remember (eKind Es) as eKs.
    destruct eKs; try contradiction;[].
    repnd. clear Hsendlrrl Hsendlrl.
    rewrite Heqevloc in Hsendlrrr.
    rewrite Hsw in Hsendlrrr.
    simpl in Hsendlrrr.
    (** Now, lets unpack the induction hypothesis *)
    unfold MotorRecievesPositivVelAtLHS in Hsendr.
    rewrite Hsw in Hsendr.
    rewrite <- HeqeKs  in Hsendr.
    rewrite Hsendll in Hsendr.
    destruct (getVelM (eMesg ev)) as [qv| ];[| auto].
    parallelForall Hsendr.
    

    
    
    


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
