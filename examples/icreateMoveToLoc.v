Require Import robots.icreate.
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
(** printing θErrTurn $\theta ErrTurn$ #θErrTurn# *)
(** remove printing * *)
(** printing θErrTrans $\theta ErrTrans$ #θErrTrans# *)
(** printing polarθSign $polar \theta Sign$ #polarθSign# *)
(** printing idealθ $ideal \theta$ #idealθ# *)

(** printing ' $ $ #'# *)

Require Import canonical_names.


Require Import Vector.
Require Import CPS.
Require Import CPSUtils.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import CartCR.

Instance ProjectionFst_instance_sig 
   (A : Type) (P: A → Prop):  
    ProjectionFst (sig P) A := (@proj1_sig A P) .

Instance ProjectionFst_instance_sigT 
   (A : Type) (P: A → Type):  
    ProjectionFst (sigT P) A := (@projT1 A P) .

(**

* Overview

In this chapter (file), we explain how to use ROSCoq to program
an iRobot Create. 
Our program receives requests to navigate to specific positions and
computes appropriate commands for the robot.
This programs forms will be a software agent in a distributed system
consisting of 3 agents, as shown in the figure:


#<img src="icreateMoveToLoc.svg"/>#

The hardware agent represents the iRobot create hardware and its ROS drivers.
It was defined in the previous chapter.
The request to navigate comes from the external agent.

In the next chapter, we will prove upper bounds on how close the robot
will end up to the requested position.
To do this proof, we use the axiomatization of the hardware agent.

If you have an iRobot Create, you will
be able to run the program on the robot.
The Coq program can be extracted to Haskell and linked with a shim
that actually handles the sending and receiving of messages.

Coq guarantees that the program will behave as proved, unless
our axiomatization of the robot was incorrect.

Before getting into the details of the specification of the entire
distributed system in ROSCoq, let us first
look at the core of the navigation program.
*)

Section RobotProgam.

(** To move to the target position, the robot first turns towards it and then
moves forward. Because a robot may not be able to physical achieve
any arbitrary angular linear speed, we let the user specify the desired 
speeds. By adjusting the duration of rotation and linear motion, we can
make the robot go anywhere. 
The two variable respectively denote the user specified rotational(angular) and linear speed.*)

Variable  rotspeed  : Qpos.
Variable  linspeed  : Qpos.

(** 
To control the duration of rotation, the program inserts a delay between
the command to start turning and the command to stop turning.
The shim in Haskell can only support a finite resolution for the time requests.
The variable below is used to specify the resolution of the timer.
Formally, 1/[delRes] is the resolution of the timer.
The current Haskell shim is based on the 
#<a href="https://hackage.haskell.org/package/base-4.8.1.0/docs/Control-Concurrent.html##v:threadDelay">threadDelay</a>#
function of Haskell, whose resolution is 1 microseconds.
Hence delRes will be instantiated with 1000000.
However, we choose to make our program and proofs generic over that value.
*)

Variable delRes : Z⁺.

(** The meaning of the 2 parameters below will be explained while explaining 
the program. *)

Variable  delEps  : Qpos.
Variable  delay  : Qpos.
Definition R2QPrec : Qpos := simpleApproximateErr delRes delEps.

Close Scope Q_scope.

(** Here is the program. For a detailed explanation, please
refer to Section 4.2 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#
*)

Definition robotPureProgam (target : Cart2D Q) : list (Q × Polar2D Q) :=
  let polarTarget : Polar2D CR := Cart2Polar target in
  let rotDuration : CR :=  ((| θ polarTarget |) * '(/ rotspeed)%Q) in
  let translDuration : CR :=  (rad polarTarget) * '(/ linspeed)%Q in
  [ (0,{|rad:= 0 ; θ := (polarθSign target) * rotspeed |}) 
      ; (tapprox rotDuration  delRes delEps , {|rad:= 0 ; θ := 0 |}) 
      ; ('delay , {|rad:=  'linspeed ; θ := 0 |}) 
      ; (tapprox translDuration delRes delEps , {|rad:= 0 ; θ := 0 |}) ].


(** 

* Specifying the whole cyber-physical system system.

The above program sends 4 commands to the iRobot create
device driver. The behaviour of the robot on the receipt
of such commands is specified in the axiomatization of the robot.
To be able to prove that the robot will end up at a place
close to the position requested by the external agent, 
we have to specify the whole cyber-physical system
that it is a part of, or at least its relevant parts.
For example, we have to specify the agents of the distributed system,
and the fact that the messages sent by the software agent are received
by the robot device driver.


** Topics

Like the Robot Operating System (ROS), ROSCoq uses a publish-subscribe
approach to communication between agents of a distributed system.
Agents can publish messages to named topics without knowing about who
are receiving them.
Similarly, agents can subsctibe to topics without knowing who is publishing them.
As explained in the previous chapter, the icreate driver
subscribes to a designated topic, and acts on the messages
specifying the linear and angular velocities for the robot.

To specify a Cyber-physical System (CpS) in ROSCoq, one
specifies a type denoting the collection of topics used for communication.
This type must be an instance of the [TopicClass] typeclass.

*)

Inductive Topic :=  VELOCITY | TARGETPOS.

(** 
In this application, we use 2 topics. The [VELOCITY] topic is used
the software agent to send the linear and angular velocity commands
to the robot hardware agent.

The [TARGETPOS] topic is used by
the external agent (see Fig. in Sec. 1)
to send the cartesian coordinates of
the target position (relative to the
robot’s current position) to the software
agent.

*)


Scheme Equality for Topic.

(** [TopicClass] the type to have decidable equality*)

Global Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


(** The [TopicClass] also needs the payload type for eqch topic.*)

Definition topic2Type (t : Topic) : Type :=
match t with
| VELOCITY => Polar2D Q
| TARGETPOS => Cart2D Q 
end.


Global Instance  ttttt : @TopicClass Topic _.
  constructor. exact topic2Type.
Defined.

(**
The type [Topic] will serve as an implicit parameter of the type [Message].
A message is just a dependent pair of a topic and its payload type.
Here is an example usage. 
*)
Definition mkTargetMsg  (q: Cart2D Q) : Message :=
  mkImmMesg TARGETPOS q.

(** 
** Collection of Agents.
To be able to holistically reason about a CpS, we have to specify the collection
of agents and the physical model of the cyber-physical system.
One has to then specify the behavior of each agent in a mutually independent way.
All of this is achieved by specifying an instance of [CPS].
We will see how to build one for our example.
First, we need a type to denote the collection of agents.
Each member of the type below denotes an agent (vertical downward arrow) in the message
sequence diagram near the top of this page.
Also, below they appear in the same order as they appear in the figure above.
*)

Inductive RosLoc :=  MOVABLEBASE | SWNODE |  EXTERNALCMD .


(**  Decidable equality is a requirement of the [CPS] typeclass *)
Scheme Equality for RosLoc.

Global Instance rldeqdsjfklsajlk : DecEq RosLoc.
  constructor. exact RosLoc_eq_dec.
Defined.

(** 
The typeclass [CPS] also needs a function that
specifies the list of topics subscribed and published by each agent.
A [TopicInfo] is a pair of lists. The first member is the list of subscribed
topics. The second member is the list of published topics.
This list cannot be changed at runtime.
When actually running  a software agent, the Haskell shim
uses the ROS (Robot Operating System) API to subscribe to each topic
in the first member of [TopicInfo].
The software agent will then be invoked on any ROS message received on
the subscribed topics.
 *)
Definition locTopics (rl : RosLoc) : TopicInfo :=
match rl with
| MOVABLEBASE => ((VELOCITY::nil), nil)
| SWNODE => ((TARGETPOS::nil), (VELOCITY::nil))
| EXTERNALCMD => (nil, (TARGETPOS::nil))
end.

(** 
** Physical Model
Now that we have defined the the collection of agents, we have to
specify the behvior of each agent in a mutually independent way.
However, the behavior of hardware devices such as sensors and actuators
cannot be specified without modeling the evolution of the relevant physical
quantities (e.g. the ones they measure or influence).
The first argument of [CPS], which is implicit, a a type denoting
the physical model of the cyber-physical system.
As described in Sec. 2 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#,
A physical model is a type that specifies how each relevant physical
quantities evolved over time, and the physical laws governing that evolution.
In this example, there is only one robot (iRobot Create), and the physical quantities
are the physical quantities relevant to that robot where specified in the type
[iCreate].
So that type will serve as our physical model.
If there were, say 2 robots, the physical model could be the type [iCreate * iCreate]
*)


Notation PhysicalModel := iCreate.

(**
** Semantics of Agents

Now we specify the behavior of each agent.
Recall from section 4 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#
that each agent is specified as a relation between how the physical quantities
evolved over time and how the sequence of events at the agent.
In the above message sequence diagram, events are denoted by either a start
or an end of a slanted arrow. Such slanted arrows denote flight of messages.
*)

Context (minGap : Q).
 (* `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}. *)

(**
Using the [Context] keyword, we assumed the type [Event] which denotes
the collection of all events.
We also assumed that the type [Event] is an instance of the [EventType] typeclass.
This typeclass enables us to use many functions events.
For example, we can use [eLoc] to get the location of an event.
For more details, please see the definition of the type [EventType] (just clicking it
should take it to its definition), or see Sec. 3 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#
*)


(**
*** Hardware Agent
*)
Variable reacTime : QTime.
(** It is more sensible to change the type to [QNonNeg]
    as the value certainly does not represent time.
    However, the coercion QT2Q does not work then *)
Variable motorPrec : Polar2D Q → Polar2D QTime.

Hypothesis motorPrec0 : motorPrec {| rad :=0 ; θ :=0 |} ≡ {| rad :=0 ; θ :=0 |}.

Definition HwAgent : Device PhysicalModel := HwAgent VELOCITY eq_refl reacTime motorPrec minGap.


(**
*** Software Agent
*)
Definition PureSwProgram: PureProcWDelay TARGETPOS VELOCITY:=
  robotPureProgam.

Definition SwProcess : Process Message (list Message):= 
  mkPureProcess (delayedLift2Mesg (PureSwProgram)).

Variable procTime : QTime.
Variable sendTimeAcc : Qpos.
Require Export CoRN.model.metric2.Qmetric.


Definition ControllerNode : RosSwNode :=
  Build_RosSwNode (SwProcess) (procTime, sendTimeAcc).


(**
*** External Agent
*)
Variable target : Cart2D Q.


Definition externalCmdSemantics
 : @NodeSemantics PhysicalModel Topic _ _:=
  λ Event edeq etype _ evs,
              isSendEvtOp (evs 0)
              ∧ ∀ n : nat, (evs (S n)) ≡ None
  ∧ (getRecdPayloadOp TARGETPOS (evs 0) ≡ Some target).


(**
*** Putting it all together. *)

Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| MOVABLEBASE => DeviceSemantics (λ ts,  ts) HwAgent
| SWNODE => SwSemantics ControllerNode
| EXTERNALCMD  => externalCmdSemantics
end.

Variable expectedDelivDelay : Qpos.
Variable delivDelayVar : Qpos.


Global Instance rllllfjkfhsdakfsdakh : @CPS PhysicalModel Topic _ _ RosLoc _.
  apply Build_CPS.
  - exact locNode.
  - exact locTopics.
  - exact (λ _ _ t , ball delivDelayVar t (QposAsQ expectedDelivDelay)).
Defined.


(** 
* Proving the correctness property. 

We need to prove that in ALL POSSIBLE EXECUTIONS
of this cyber-physical system, the robot will end up to some place
close where it is asked to go by the esternal agent.
So, we consider an arbitrary execution, and prove the desired property about it.
*)
Variable cpsExec:(CPSExecution minGap).

Variable ic : iCreate.
Variable eo : (@CPSExecution _  ic minGap _ _ _ _ _ _ _ _ _).


Lemma derivXNoMC : ∀ icr, isDerivativeOf (transVel icr[*] (CFCos (theta icr))) (X (position icr)).
  exact derivX.
Qed.

Lemma derivYNoMC : ∀ icr, isDerivativeOf (transVel icr[*] (CFSine (theta icr))) (Y (position icr)).
  exact derivY.
Qed.

Definition posAtTime (t: Time) : Cart2D IR :=
  {| X:= {X (position ic)} t ; Y := {Y (position ic)} t |}.

Definition targetR : Cart2D IR := ' target.


Require Export Coq.Lists.List.
Hint Resolve (fun a b x => proj1 (locEvtIndex a b x)) : ROSCOQ.

Ltac contra :=
  match goal with
  | [H: ~(assert true) |- _ ] => provefalse; apply H; reflexivity
  end.

(* No Change at All from the train proof.
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

(* No Change at All from the train proof *)

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
  -> (getPayload TARGETPOS (eMesg ev) ≡ Some target
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
       (getRecdPayload TARGETPOS ev ≡ Some target) 
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
  let resp := PureSwProgram target in
  ∀ n: nat, 
      n < 4
      → {ev : Event | eLocIndex ev ≡ S n ∧ eLoc ev ≡ SWNODE
            ∧ (isSendEvt ev) 
            ∧ Some (eMesg ev) 
               ≡ nth_error
                    (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) resp) n
            ∧ ball sendTimeAcc
                (eTime (proj1_sig SwEvents0)
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
  apply DelayedPureProcDeqSendPair with (nd:=0) (pl:=target) (n:=n)
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
  unfold mkPureProcess, getDeqOutput2, getOutput in Hexrrl.
  unfold delayedLift2Mesg in Hexrrl.
  simpl in Hexrrl.
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


Lemma MotorEvents:
  let resp := PureSwProgram target in
  ∀ n: nat, 
      n < 4
      → {ev : Event | (isRecvEvt ev)  ∧ eLoc ev ≡ MOVABLEBASE
            ∧ eLocIndex ev ≡ n
            ∧ Some (π₁ (eMesg ev))
               ≡ nth_error
                    (map (λ p, existT topicType VELOCITY (π₂ p)) resp) n
            ∧ ball (sendTimeAcc+delivDelayVar)
                ( eTime (proj1_sig SwEvents0) + expectedDelivDelay
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
  let resp := PureSwProgram target in
  ∀ n: nat, 
      (n < 4)
      → {ev : Event |  
           (isRecvEvt ev)  ∧ eLoc ev ≡ MOVABLEBASE
            ∧ eLocIndex ev ≡ n
            ∧  getPayloadAndEv VELOCITY (Some ev)  
                ≡ opBind (λ pl, Some (π₂ pl, ev))
                       (nth_error resp n)
            ∧ ball (sendTimeAcc+delivDelayVar)
                ( eTime (proj1_sig SwEvents0) + expectedDelivDelay
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

Lemma MotorEventsNthTimeSInc:
  ∀ (n1 n2 : nat) p1 p2,
  (n1 < n2)%nat
   -> (MotorEventsNthTime n1 p1 
      < MotorEventsNthTime n2 p2)%Q.
Proof.
  unfold MotorEventsNthTime, MotorEventsNth.
  intros.
  destruct (MotorEvents2 n1 p1) as [ev1  H1e].
  destruct (MotorEvents2 n2 p2)  as [ev2  H2e].
  simpl. repnd.
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

Definition correctVelDuring := correctVelDuring reacTime motorPrec.

Lemma correctVelTill0:
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
    correctVelDuring initialVel (mkQTime 0 I) t0 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, HwAgent in Hc.
  apply proj1 in Hc.

  unfold MotorEventsNthTime, MotorEventsNth in t0.
let x := constr:(decAuto (0<4)%nat I) in
  destruct (MotorEvents2 O x) as [evStartTurn  H0m].
  simpl in t0.
  unfold minDelayForIndex, message.delay, Basics.compose in H0m.
  Local Opaque getPayloadAndEv.
  simpl in H0m.
  unfold corrSinceLastVel in Hc.
  unfold latestVelPayloadAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
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
  Local Opaque decAuto.
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
  split; [apply Hd0; auto|].
  unfold posAtTime.
Local Opaque getF mkQTime.
  simpl.
  split.
Local Transparent mkQTime.
- apply TDerivativeEqQ0 with 
    (F':=(transVel ic[*]CFCos (theta ic)));
    eauto with ICR.
  intros tq Hbw. simpl in Hbw.
  rewrite IContRMultAp, Hd0;[| lra].
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
  let requestedVel : Polar2D Q :=
    {|
       rad := 0;
       θ := polarθSign target * rotspeed |} in
  correctVelDuring requestedVel mt0 mt1 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, HwAgent in Hc.
  apply proj1 in Hc.
  unfold mt0, mt1.
  unfold MotorEventsNthTime, MotorEventsNth.
  let x := constr:(decAuto (0<4)%nat I) in
  destruct (MotorEvents2 O x) as [evStartTurn  H0m].
  let x := constr:(decAuto (1<4)%nat I) in
  destruct (MotorEvents2 1 x) as [evStopTurn  H1m].
  unfold minDelayForIndex, message.delay, Basics.compose in H1m.
  Local Opaque getPayloadAndEv.
  autounfold with π₁ in H1m.
  simpl in H1m.
  unfold corrSinceLastVel in Hc.
  unfold latestVelPayloadAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
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
  CRasIR (polarTheta target).

Definition idealθ : IR :=
  CRasIR (θ (Cart2Polar target)).

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
  unfold minDelayForIndex, message.delay, Basics.compose.
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
  let resp := PureSwProgram target in
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
  Local Opaque Qball.
  repeat (apply proj2 in H1m).
  repeat (apply proj2 in H0m).
  Local Transparent Qball.
  autounfold with π₁ in H0m, H1m.
  remember (map (λ p : Q ** topicType VELOCITY, mkDelayedMesg (fst p) (π₂ p))
              (PureSwProgram target)) as ddd.
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
  clear. ring.
Qed.


Close Scope nat_scope.

Definition rotDuration : CR :=  ((| polarTheta target |) * '(/ rotspeed)%Q).



Lemma MotorEv01Gap :
   (|QT2Q mt1 - QT2Q mt0 -  simpleApproximate rotDuration  delRes delEps|)
  ≤ 2 * (sendTimeAcc + delivDelayVar)%Q.
Proof.
  apply MotorEvGap.
Qed.

Definition thetaAbs : CR := (| polarTheta target |).

Definition E2EDelVar : Q := 
  (2 * (sendTimeAcc + delivDelayVar))%Q.


Lemma  QabsNewOmega :  (Qabs.Qabs ((polarθSign target) * rotspeed)%mc 
        ==
        rotspeed)%Q.
Proof.
  unfold mult, stdlib_rationals.Q_mult.
  rewrite Qabs.Qabs_Qmult.
  unfold polarθSign.
  rewrite QAbsQSign.
  unfold CanonicalNotations.norm, NormSpace_instance_Q.
  simpl Qabs.Qabs.
  ring_simplify.
  rewrite QabsQpos.
  reflexivity.
Qed.

Lemma  AbsIRNewOmega : 
      AbsIR ((polarθSign target) * rotspeed)%mc [=]
        rotspeed.
Proof.
  rewrite AbsIR_Qabs, QabsNewOmega.
  reflexivity.
Qed.


Definition w :=  (polarθSign target) * rotspeed.
  
Lemma MotorEv01Gap2 :
    (Qabs.Qabs
        ((mt1 - mt0) * w - (simpleApproximate rotDuration  delRes delEps)*w) <=
      (2) * (sendTimeAcc + delivDelayVar) * rotspeed)%Q.
Proof.
  pose proof MotorEv01Gap as Hg.
  apply Qmult_le_compat_r with (z:= Qabs.Qabs w) in Hg;
      [|apply Qabs.Qabs_nonneg].
  rewrite <- Qabs.Qabs_Qmult in Hg.
  revert Hg.
  unfoldMC.
  intros Hg.
  rewrite foldQminus in Hg.
  rewrite  QmultOverQminusR in Hg.
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
Abort.

Definition motorTurnOmegaPrec (w : Q) : QTime := θ (motorPrec {| rad :=(0%Q) ; θ := w |}).

(* Delete!! *)
Lemma multRAbsSmallIR:
  ∀  (y x e : IR),
  AbsSmall e x → AbsSmall (e[*]AbsIR y) (x[*]y).
Proof.
  intros.
  apply mult_AbsSmall;[assumption|].
  apply AbsIR_imp_AbsSmall.
  apply leEq_reflexive.
Qed.

Require Export MathClasses.interfaces.abstract_algebra.
Require Export  MathClasses.theory.rings.
Lemma OptimalAngleEq : CRasIR rotDuration[*]inj_Q ℝ w = optimalTurnAngle.
Proof.
  unfold rotDuration, optimalTurnAngle, w. 
  apply (injective IRasCR).
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  rewrite CRasIRasCR_id.
  rewrite multMiddle.
  rewrite <- CRmult_Qmult.
  fold (@mult CR _).
  rewrite sr_mult_associative.
  rewrite polarθSignCorr1.
  rewrite mult_comm.
  rewrite sr_mult_associative.
  rewrite multMiddle.
  autorewrite with MoveInjQCROut.
  destruct rotspeed.
  simpl.
  assert ((/ x * x) ==1)%Q as Heq by (field; lra).
  rewrite Heq.
  prepareForCRRing.
  ring.
Qed.

Local Opaque approximate CRmult.


Lemma simpleApproximateAbsSmallIR: ∀ (r:CR) (res : Z⁺) (eps : Qpos),
    AbsSmall (simpleApproximateErr res eps) 
      (CRasIR r [-] (simpleApproximate r res eps)).
  intros ? ? ?.
  pose proof (simpleApproximateSpec r res eps) as Hball.
  apply CRAbsSmall_ball in Hball.
  fold (inject_Q_CR) in Hball.
  apply CR_AbsSmall_as_IR in Hball.
  rewrite CR_minus_asIR2 in Hball.
  rewrite <- IR_inj_Q_as_CR in Hball.
  rewrite <- IR_inj_Q_as_CR in Hball.
  rewrite IRasCRasIR_id in Hball.
  rewrite IRasCRasIR_id in Hball.
  exact Hball.
Qed.

Lemma ThetaAtEV1 :
     (|{theta ic} mt1 - optimalTurnAngle|) ≤ 
          Q2R (rotspeed * (R2QPrec+ 2 * (sendTimeAcc + delivDelayVar) 
                  + reacTime) 
              + (motorTurnOmegaPrec w) * (mt1 - mt0))%Q.
Proof.
  pose proof correctVel0to1 as Hc.
  simpl in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc. simpl θ in Hc.
  fold (w) in Hc.
  match type of Hc with
  context[changesTo _ _ _ (Q2R ?nv) _ (QT2Q ?om)]
    => remember om as opr
  end.
  assert ((mt0 < mt1)%Q) 
    as Hassumption by (apply MotorEventsNthTimeSInc; omega).
  pose proof (qtimePos reacTime) as H99.
  pose proof (OmegaThetaAtEV0 mt0 QTimeLeRefl) as Ht0.
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
  fold (w) in Hadd.

  unfold Q2R in Hadd. ring_simplify in Hadd.
  unfold cg_minus in Hadd. ring_simplify in Hadd.
  clear Hg Hc.
  revert Hadd.
  unfoldMC. intro Hadd. unfold QT2R in Hadd.
  unfold Q2R in Hadd.
  Local Opaque inj_Q.
  autorewrite with QSimpl in Hadd. simpl in Hadd.
  match type of Hadd with 
  AbsSmall (inj_Q _ ?r%Q) _ => assert (r == rotspeed * (2 * (sendTimeAcc + delivDelayVar) + reacTime) + opr * (mt1 - mt0))%Q
                                    as Heqq by (unfoldMC ;ring); rewrite Heqq in Hadd; clear Heqq
  end.
  pose proof (simpleApproximateAbsSmallIR rotDuration delRes delEps) as Hball.
  apply AbsSmall_minus in Hball.
  apply (multRAbsSmallIR w) in Hball.
  rewrite AbsIRNewOmega, IRDistMinus in Hball.
  rewrite <- inj_Q_mult in Hball.
  rewrite <- inj_Q_mult in Hball.
  simpl in Hball.
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
  autounfold with IRMC.

  rewrite OptimalAngleEq in Hadd.
  eapply leEq_transitive;[apply Hadd|].
  apply eqImpliesLeEq.
  apply inj_Q_wd.
  simpl. unfoldMC.
  fold (motorTurnOmegaPrec w). ring.
Qed.

Require Export Coq.QArith.Qabs.

Definition timeErr : Q := 
  (R2QPrec + 2 * (sendTimeAcc + delivDelayVar))%Q.

Lemma MotorEv01Gap3 :
   AbsIR ((Q2R (QT2Q mt1 - QT2Q mt0)) - 'rotDuration)
  [<=] Q2R timeErr.
Proof.
  pose proof  MotorEv01Gap  as Hg. unfold timeErr.
  apply (inj_Q_leEq IR) in Hg.
  rewrite <- AbsIR_Qabs in Hg.
  rewrite cgminus_Qminus, inj_Q_minus in Hg.
  pose proof (simpleApproximateAbsSmallIR  rotDuration delRes delEps) as Hball.
  apply AbsIR_imp_AbsSmall in Hg.
  apply AbsSmall_minus in Hball.
  unfold Q2R in Hball.
Local Opaque CRabs.
  simpl in Hball.
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
- apply inj_Q_wd. simpl. unfold timeErr. ring.
- unfold Q2R, Qminus, cg_minus. reflexivity.
Qed.

Definition Ev01TimeGapUB : IR := 'rotDuration + Q2R timeErr.

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
  rewrite plus_comm.
  exact Hp.
Qed.

Hint Resolve qtimePosIR : ROQCOQ.
Lemma ThetaAtEV1_2 :
     (|{theta ic} mt1 - optimalTurnAngle|) ≤ 
          Q2R (rotspeed * (timeErr + reacTime))
            + (Q2R (motorTurnOmegaPrec w) * Ev01TimeGapUB).
Proof.
  intros. pose proof ThetaAtEV1 as Hom.
  Local Opaque Qabs.Qabs Q2R.
  simpl in Hom.
  Local Transparent Q2R.
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

Definition eeev  a b : Q  :=
 (rad (motorPrec {|rad:= a; θ:= b|})).

Definition eeew  a b : Q :=
 (θ (motorPrec {|rad:= a; θ:= b|})).

Lemma ThetaAtEV1_3 :
  let omPrec : Q :=  (eeew 0%Q w) in 
 |{theta ic} mt1 - optimalTurnAngle| ≤ 
   Q2R(rotspeed * (timeErr + reacTime) +
    omPrec * timeErr)
    + Q2R (omPrec / rotspeed)%Q * ('(CRabs (polarTheta target))).
Proof.
  Local Opaque Q2R.
  simpl.
  pose proof ThetaAtEV1_2 as Hev.
  simpl in Hev.
  eapply leEq_transitive;[apply Hev|].
  Local Transparent Q2R.
  unfold Q2R.
  rewrite inj_Q_plus.
  autounfold with IRMC.
  rewrite <- plus_assoc_unfolded.
  apply plus_resp_leEq_lft.
  apply eq_imp_leEq.
  unfold Ev01TimeGapUB.
  fold E2EDelVar.
  unfold eeew, motorTurnOmegaPrec.
  remember (θ (motorPrec {| rad := 0%Q; θ := w |}) ) as ew.
  unfold cast, Cart_CR_IR.
  unfold rotDuration, CanonicalNotations.norm,
  NormSpace_instance_0.
  unfoldMC.
  autounfold with IRMC.
  Local Opaque Q2R.
  simpl.
  rewrite CR_mult_asIR.
  remember (CRasIR (CRabs (polarTheta target))) as crabs.
  autorewrite with QSimpl.
  unfold Qdiv.
  autorewrite with CRtoIR.
  autorewrite with InjQDown.
  Local Transparent Q2R.
  unfold Q2R.
  ring.
Qed.


Local Transparent Q2R.

Lemma OmegaAtEv1 :
    AbsSmall (Q2R (rotspeed + motorTurnOmegaPrec w)) ({omega ic} mt1).
Proof.
  pose proof correctVel0to1 as H0c.
  simpl in H0c.
  apply proj2 in H0c.
  destruct H0c as [qtrans H0c].
  simpl in H0c.
  repnd.
  rename H0clr into Ht.
  destruct (Qlt_le_dec mt1 qtrans) as [Hd | Hd].
- clear H0crl.
  pose proof (λ t p, (betweenLAbs _ _ _ _ 
        (qtimePosIR (motorTurnOmegaPrec w)) (H0crr t p)))
     as Hqt. clear H0crr.
  specialize (Hqt mt1).
  DestImp Hqt; [|split; [apply MotorEventsNthTimeIncSn |lra]].
  destruct (OmegaThetaAtEV0 mt0) as [Hom Htt];[apply QTimeLeRefl|].
  clear Htt.
  rewrite Hom, IR_inv_Qzero in Hqt.
  rewrite AbsIR_minus, IR_inv_Qzero in Hqt.
  rewrite AbsIRNewOmega in Hqt.
  apply AbsIR_imp_AbsSmall in Hqt.
  unfold QT2R, Q2R in Hqt.
  autorewrite with QSimpl in Hqt.
  exact Hqt.
- rename H0crl into H0c.
  specialize (H0c mt1).
  DestImp H0c;
  [|  split;[assumption | reflexivity]].
  pose proof (AbsIRNewOmega) as Habs.
  apply eq_imp_leEq in Habs.
  pose proof (AbsIR_plus _ _ _ _ Habs H0c) as Hadd.
  unfold cg_minus in Hadd.
  apply AbsIR_imp_AbsSmall in Hadd.
  ring_simplify in Hadd.
  fold (w) in Hadd.
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
  unfold DeviceSemantics, HwAgent in Hc.
  apply proj1 in Hc.

  unfold MotorEventsNthTime, MotorEventsNth in t1, t2.
  let x := constr:(decAuto (1<4)%nat I) in
  destruct (MotorEvents2 1 x) as [evStartTurn  H0m].
  simpl in t1.
  let x := constr:(decAuto (2<4)%nat I) in
  destruct (MotorEvents2 2 x) as [evStopTurn  H1m].
  simpl in t2.
  unfold minDelayForIndex, message.delay, Basics.compose in H1m.
  Local Opaque getPayloadAndEv.
  autounfold with π₁ in H1m.
  simpl in H1m.
  unfold corrSinceLastVel in Hc.
  unfold latestVelPayloadAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
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
Q2R(rotspeed * (timeErr + 2* reacTime) +
    (eeew 0%Q w) * (timeErr + reacTime))
    + Q2R ((eeew 0%Q w) / rotspeed)%Q * ('(|polarTheta target|)).

Lemma ThetaAtEV2 :
 (|{theta ic} mt2 - optimalTurnAngle|) ≤ θErrTurn.
Proof.
  unfold θErrTurn.
  pose proof correctVel1to2 as Hc.
  simpl in Hc. fold mt1 mt0 in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc. simpl θ in Hc.
  rewrite motorPrec0 in Hc.
  assert (mt1 < mt2)%Q 
    as Hassumption 
    by (apply MotorEventsNthTimeSInc; omega).
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
  remember (θ (motorPrec {| rad := 0%Q; θ := w |})) as ew.
  simpl.
  unfold rotDuration, CanonicalNotations.norm,
  NormSpace_instance_0.
  ring.
Qed.


Lemma ThetaAtEV2P : (|{theta ic} mt2 - idealθ|) ≤  θErrTurn.
Proof.
  apply ThetaAtEV2.
Qed.

Local Opaque Q2R.

Lemma MotorEv12Gap :
   ((|QT2Q mt2 - QT2Q mt1 -  delay |)
   ≤ 2 * (sendTimeAcc + delivDelayVar))%Q.
Proof.
  apply MotorEvGap.
Qed.

Variable delayLargeEnough :
  (reacTime + 2 * (sendTimeAcc + delivDelayVar) < delay)%Q.

Lemma MotorEventsNthTimeReacLt12:
   (mt1 + reacTime
      < mt2)%Q.
Proof.
  pose proof MotorEv12Gap as Hp.
  Local Opaque Q2R.
  simpl in Hp.
  apply AbsSmall_Qabs in Hp.
  apply proj1 in Hp.
  simpl in Hp.
  revert Hp. unfoldMC.
  intro Hp. unfold cg_minus in Hp.
  simpl in Hp.
  assert ( (1+1)%Q=2) as H by reflexivity.
  rewrite H in Hp.
  lra.
Qed.
  
Lemma MotorEventsNthTimeReacLe12:
   (mt1 + reacTime
      <= mt2)%Q.
Proof.
  pose proof MotorEventsNthTimeReacLt12.
  lra.
Qed.

Lemma OmegaAtEv2 : {omega ic} mt2 = 0.
Proof.
  pose proof correctVel1to2 as H0c.
  simpl in H0c.
  apply proj2 in H0c.
  destruct H0c as [qtrans H0c].
  simpl in H0c.
  pose proof (proj2 (proj1 H0c)) as Ht.
  apply proj2 in H0c.
  apply proj1 in H0c.
  fold mt2 in H0c.
  fold mt1 in Ht.
  specialize (H0c mt2).
  DestImp H0c;
  [|  split;[| reflexivity];
      eapply Qle_trans;[apply Ht|];
      apply MotorEventsNthTimeReacLe12; omega].
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
      subst t2; apply MotorEventsNthTimeReacLe12; omega].
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
  let requestedVel : Polar2D Q := {|rad:= QposAsQ linspeed ; θ := 0 |} in
  correctVelDuring requestedVel t1 t2 ic.
Proof.
  intros. pose proof (corrNodes eo MOVABLEBASE) as Hc.
  simpl in Hc.
  unfold DeviceSemantics, HwAgent in Hc.
  apply proj1 in Hc.

  unfold MotorEventsNthTime, MotorEventsNth in t1, t2.
   let x := constr:(decAuto (2<4)%nat I) in
  destruct (MotorEvents2 2 x) as [evStartTurn  H0m].
  simpl in t1.
  let x := constr:(decAuto (3<4)%nat I) in
  destruct (MotorEvents2 3 x) as [evStopTurn  H1m].
  simpl in t2.
  unfold minDelayForIndex, message.delay, Basics.compose in H1m.
  Local Opaque getPayloadAndEv.
  autounfold with π₁ in H1m.
  simpl in H1m.
  unfold corrSinceLastVel in Hc.
  unfold latestVelPayloadAndTime, lastPayloadAndTime, filterPayloadsUptoTime in Hc.
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
:= (θ (motorPrec {| rad := QposAsQ linspeed; θ := 0 |})).


Lemma ThetaEv2To3 :
  ∀ (t : QTime),  mt2 ≤ t ≤ mt3
      → AbsIR ({theta ic} t[-]θ2)
      [<=]inj_Q ℝ (rotErrTrans * (mt3 - mt2))%Q.
Proof.
  intros ? Hle.
  pose proof (qtimePos t) as Hq.
  pose proof correctVel2to3 as Hc.
  simpl in Hc.
  unfold correctVelDuring in Hc.
  apply proj2 in Hc.
  fold mt2 mt3 in Hc.
  fold rotErrTrans in Hc.
  simpl θ in Hc.
  unfold zero, stdlib_rationals.Q_0 in Hc.
  eapply changesToDerivSameEpsIntegWeaken in Hc; 
    eauto using
    derivRot;
   [|apply MotorEventsNthTimeInc; omega|apply OmegaAtEv2].
  unfold Q2R in Hc. 
  autorewrite with CoRN in Hc.
  fold (θ2) in Hc.
  unfold QT2R in Hc.
  autorewrite with QSimpl in Hc.
  simpl in Hc.
  assumption.
Qed.

Definition transDuration : CR :=  ((| target |) * '(/linspeed)%Q).


Lemma MotorEv23Gap :
   (|QT2Q mt3 - QT2Q mt2 -  simpleApproximate transDuration  delRes delEps|)
   ≤ 2 * (sendTimeAcc + delivDelayVar)%Q.
Proof.
  apply MotorEvGap.
Qed.

Definition Ev23TimeGapUB : IR := 'transDuration + Q2R timeErr.


Definition θErrTrans : IR := (QT2R rotErrTrans) * Ev23TimeGapUB.


Lemma MotorEv23Gap3 :
   AbsIR ((Q2R (QT2Q mt3 - QT2Q mt2)) - 'transDuration) 
  [<=] timeErr.
Proof.
  pose proof  MotorEv23Gap  as Hg. unfold timeErr.
  apply (inj_Q_leEq IR) in Hg.
  rewrite <- AbsIR_Qabs in Hg.
  rewrite cgminus_Qminus, inj_Q_minus in Hg.
  pose proof (simpleApproximateAbsSmallIR  transDuration delRes delEps) as Hball.
  apply AbsIR_imp_AbsSmall in Hg.
  apply AbsSmall_minus in Hball.
  unfold Q2R in Hball.
Local Opaque CRabs.
  simpl in Hball.
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
- apply inj_Q_wd. simpl. unfold timeErr. ring.
- unfold Q2R, Qminus, cg_minus. reflexivity.
Qed.

Lemma MotorEv23Gap4 :
   Q2R (QT2Q mt3 - QT2Q mt2) ≤ Ev23TimeGapUB.
Proof.
  pose proof MotorEv23Gap3 as Hp.
  Local Opaque Q2R.
  simpl in Hp.
  apply AbsIR_imp_AbsSmall in Hp.
  unfold AbsSmall in Hp.
  apply proj2 in Hp.
  apply shift_leEq_plus in Hp.
  unfold Ev23TimeGapUB.
  rewrite plus_comm.
  exact Hp.
Qed.


Definition Ev23TimeGapLB : IR := 'transDuration - Q2R timeErr.

Lemma MotorEv23GapLB : Ev23TimeGapLB  ≤  Q2R (mt3 - mt2).
Proof.
  pose proof MotorEv23Gap3 as Hp.
  Local Opaque Q2R.
  simpl in Hp.
  apply AbsIR_imp_AbsSmall in Hp.
  unfold AbsSmall in Hp.
  apply proj1 in Hp.
  apply shift_plus_leEq in Hp.
  unfold Ev23TimeGapLB.
  eapply leEq_transitive;[|apply Hp].
  unfoldMC.
  autounfold with IRMC.
  apply eqImpliesLeEq. unfold cast, Cart_CR_IR.
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
  apply MotorEv23Gap4.
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
  → |{theta ic} t - idealθ| ≤ θErrTrans + θErrTurn.
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

Variable nztp : ([0] [<] normIR (' target)).

Definition rotOrigininPos : Cart2D TContR:=
  rotateOriginTowardsF (' target) nztp (position ic).


Definition Y'Deriv : TContR :=
(transVel ic) * (FSin (theta ic - FConst optimalTurnAngle)).

Definition X'Deriv : TContR :=
(transVel ic) * (FCos (theta ic - FConst optimalTurnAngle)).

Lemma DerivRotOriginTowardsTargetPos : 
  (isDerivativeOf X'Deriv (X rotOrigininPos)
   × isDerivativeOf Y'Deriv (Y rotOrigininPos)).
Proof.
  unfold Y'Deriv, X'Deriv.
  apply DerivativerotateOriginTowards2; eauto with ICR.
Qed.

Hint Resolve (fst DerivRotOriginTowardsTargetPos) 
             (snd DerivRotOriginTowardsTargetPos) : ICR.

Hint Unfold Mult_instance_TContR Plus_instance_TContR
  Negate_instance_TContR : TContR.

Lemma YDerivAtTime : ∀ (t: Time),
  {Y'Deriv} t 
  = {transVel ic} t[*]Sin ({theta ic} t[-]optimalTurnAngle).
Proof.
  intros ?.
  unfold Y'Deriv.
  unfoldMC.
  autounfold with TContR.
  autorewrite with IContRApDown.
  reflexivity.
Qed.

Lemma XDerivAtTime : ∀ (t: Time),
  {X'Deriv} t 
  = {transVel ic} t[*]Cos ({theta ic} t[-]optimalTurnAngle).
Proof.
  intros ?.
  unfold X'Deriv.
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
:= (rad (motorPrec {| rad := 0 ; θ := w |})).


Hint Resolve MotorEventsNthTimeIncSn : ICR.

Definition rotDerivAtTime (t : Time) : Cart2D IR:=
  {|X:= {X'Deriv} t; Y:= {Y'Deriv} t|}.

 
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
  fold w transErrRot in H01.
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
    as Hassumption by (apply MotorEventsNthTimeReacLt12; omega).
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
:= (rad (motorPrec {| rad := QposAsQ linspeed; θ := 0 |})).

Require Export core.
Lemma SpeedUbEv2To3 : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  -> AbsIR ({transVel ic} t)[<=](linspeed + transErrTrans)%Q.
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
  setoid_rewrite (AbsIRQpos linspeed) in Hmrl.
  setoid_rewrite (AbsIRQpos linspeed) in Hqt.
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
  
Close Scope Q_scope.
(** prepping for [TDerivativeAbsQ] *)
Lemma YDerivEv2To3 : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  → AbsIR ({Y'Deriv} t) 
      ≤   (Sin (θErrTrans + θErrTurn)) * (linspeed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  unfold Y'Deriv.
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
  → AbsIR ({Y'Deriv} t [-] [0]) 
      ≤   (Sin (θErrTrans + θErrTurn)) * (linspeed + transErrTrans)%Q.
Proof.
  intros.
  rewrite cg_inv_zero.
  eapply YDerivEv2To3; eauto.
Qed.



Lemma YChangeEv2To3 :
  AbsIR ({Y rotOrigininPos} mt3 [-] {Y rotOrigininPos} mt2) 
      ≤   Q2R (mt3 - mt2)%Q * ((Sin (θErrTrans + θErrTurn))
                       * (linspeed + transErrTrans)%Q).
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

(** While this spec is totally in terms of the parameters,
    it does not clarify how ttanslation speed matters, because 
    [Ev23TimeGapUB] has terms that depend on speed.
    So does [θErrTrans]. 
    One can unfold Ev23TimeGapUB and cancel out some terms. *)
Lemma YChangeEv2To3_2 :
  AbsIR ({Y rotOrigininPos} mt3 [-] {Y rotOrigininPos} mt2) 
      ≤  Ev23TimeGapUB  * ((Sin (θErrTrans + θErrTurn))
                       * (linspeed + transErrTrans)%Q).
Proof.
  intros.
  pose proof (YChangeEv2To3) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  clear Hyd.
  apply mult_resp_leEq_rht;[apply MotorEv23Gap4; fail|].
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


Lemma Dist23RW: Ev23TimeGapUB * (linspeed + transErrTrans)%Q 
[=] (('(|target |)) 
          + Ev23TimeGapUB * QT2R transErrTrans
          + Q2R linspeed * timeErr).
Proof.
  unfold Ev23TimeGapUB, transDuration.
  unfoldMC. autounfold with IRMC.
  unfold QT2R, Q2R.
  rewrite inj_Q_plus.
  ring_simplify.
  unfold cast, Cart_CR_IR.
  rewrite CR_mult_asIR.
  rewrite CRasIRInj.
  rewrite mult_commut_unfolded, <- mult_assoc_unfolded.
  rewrite mult_assoc_unfolded.
  rewrite qpCancel.
  ring_simplify.
  autorewrite with InjQDown.
  apply plus_resp_eq.
  reflexivity.
Qed.

Lemma YChangeEv2To3_3 :
  AbsIR ({Y rotOrigininPos} mt3 [-] {Y rotOrigininPos} mt2) 
      ≤ (Sin (θErrTrans + θErrTurn) * 
        (('(|target |)) 
          + Ev23TimeGapUB * QT2R transErrTrans
          + Q2R linspeed * timeErr)).
Proof.
  intros.
  pose proof (YChangeEv2To3_2) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  clear Hyd.
  apply eqImpliesLeEq.
  unfoldMC. autounfold with IRMC.
  rewrite mult_commut_unfolded, <- mult_assoc_unfolded.
  apply mult_wdr.
  rewrite <- Dist23RW.
  unfoldMC. autounfold with IRMC. ring.
Qed.


Lemma transErrRotEq :
  (eeev 0 w) = transErrRot.
reflexivity.
Qed.

Lemma transErrTransEq :
  (eeev linspeed 0) = transErrTrans.
reflexivity.
Qed.


Definition ErrY': IR :=  '(eeev 0 w) * (QT2R reacTime + Ev01TimeGapUB)
+ (Sin (θErrTrans + θErrTurn)) * ('(|target |) + Ev23TimeGapUB * '(eeev linspeed 0) + (Q2R linspeed) * timeErr).

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

Variable speedTransErrTrans : (0 <= linspeed - transErrTrans)%Q.

  
Lemma XDerivEv2To3UBAux : ∀ (t:QTime), 
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  t2 ≤ t ≤ t3 
  → AbsIR ({X'Deriv} t) ≤ (linspeed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  unfold X'Deriv.
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
  → ({X'Deriv} t) ≤ (linspeed + transErrTrans)%Q.
Proof.
  intros ? ? ? Hb.
  eapply leEq_transitive;[| apply (XDerivEv2To3UBAux t); assumption].
  apply leEq_AbsIR.
Qed.

Lemma XChangeUBEv2To3 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
   ({X rotOrigininPos} t3 [-] {X rotOrigininPos} t2) 
      ≤  ((t3 - t2) * (linspeed + transErrTrans))%Q.
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
   ({X rotOrigininPos} mt3 [-] {X rotOrigininPos} mt2) 
      ≤  (Ev23TimeGapUB * (linspeed + transErrTrans)%Q).
Proof.
  intros.
  pose proof (XChangeUBEv2To3) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  fold mt2 mt3. clear Hyd.
  unfold Q2R. rewrite inj_Q_mult.
  apply mult_resp_leEq_rht;[apply MotorEv23Gap4; fail|].
  eauto 2 with CoRN ROSCOQ.
Qed.


Definition X'DiffUB: IR :=  '(eeev 0 w) * (QT2R reacTime + Ev01TimeGapUB)
+ Ev23TimeGapUB * '(eeev linspeed 0) + (Q2R linspeed) * timeErr.

Definition idealX' :IR := '(|target |).


Lemma Ev3X'DiffUb : {X rotOrigininPos} mt3  ≤ idealX' + X'DiffUB.
Proof.
  pose proof XChangeUBEv2To3_2 as Ha.
  rewrite Dist23RW in Ha.
  pose proof PosRotAxisAtEV2 as Hb.
  apply proj1 in Hb.
  unfold XYAbs in Hb.
  Local Opaque rotOrigininPos.
  simpl in Hb.
  apply AbsIR_imp_AbsSmall in Hb.
  apply proj2 in Hb.
  pose proof (plus_resp_leEq_both _ _ _ _ _ Ha Hb) as Hadd.
  clear Ha Hb.
  autounfold with IRMC in Hadd.
  Local Opaque Q2R.
  simpl in Hadd.
  unfold cg_minus in Hadd. ring_simplify in Hadd.
  eapply leEq_transitive;[apply Hadd|].
  apply eqImpliesLeEq.
  unfold idealX', X'DiffUB.
  clear. autounfold with IRMC.
  rewrite transErrTransEq.
  rewrite transErrRotEq.
  unfold cast.
  unfold Cast_instace_Q_IR.
  Local Transparent Q2R QT2R.
  unfold QT2R. unfold Q2R.
  autorewrite with QSimpl.
  ring_simplify.
  autorewrite with QSimpl.
  unfold Q2R.
  simpl.
  autorewrite with QSimpl.
  simpl.
  ring.
Qed.


Lemma SpeedLbEv2To3 :
  ∃ qtrans : QTime, (mt2 <= qtrans <= mt2 + reacTime)%Q ∧
  (∀ t:QTime, mt2 ≤ t ≤ qtrans →  0 ≤ ({transVel ic} t))
  ∧ (∀ t:QTime, qtrans ≤ t ≤ mt3 →
        Q2R (linspeed - transErrTrans)%Q [<=] ({transVel ic} t)).
Proof.
  pose proof correctVel2to3 as Hc.
  fold mt2 mt3 in Hc.
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

Require Export Coq.QArith.Qminmax.
Lemma XDerivLBEv2To3 : 
  ∃ qtrans : Q, (mt2 <= qtrans <= mt2 + reacTime)%Q ∧
  (∀ t:QTime, (mt2 <= t <= Qmin qtrans mt3)%Q →  0 ≤ ({X'Deriv} t))
  ∧ (∀ t:QTime, qtrans ≤ t ≤ mt3 →
        (Cos (θErrTrans + θErrTurn)) * (linspeed - transErrTrans)%Q 
          [<=] (({X'Deriv} t))).
Proof.
  pose proof SpeedLbEv2To3 as Hs.
  fold mt2 mt3 in Hs.
  cbv zeta in Hs. destruct Hs as [qtrans Hs].
  unfold le, Le_instance_QTime in Hs.
  exists qtrans.
  repnd.
  pose proof (Q.le_min_l qtrans mt3).
  assert ((mt2 <= Qmin qtrans mt3)%Q) as Hbc by
    (apply Q.min_glb_iff;
    split; try lra; apply MotorEventsNthTimeIncSn).
  split;[split;try lra|].
  unfold X'Deriv.
  autounfold with IRMC TContRMC.
  unfold Le_instance_QTime, stdlib_rationals.Q_0.
  fold (theta ic[-](ConstTContR optimalTurnAngle)).
  split;[clear Hsrr |]; intros t Hb.
- rewrite XDerivAtTime.
  pose proof Hb as Hbb.
  specialize (Hsrl t).
  autounfold with IRMC in Hsrl.
  DestImp Hsrl;[|lra].
  rewrite inj_Q_Zero.
  autounfold with IRMC in Hb.
  rewrite inj_Q_Zero in Hsrl.
  apply mult_resp_nonneg;[assumption|].
  apply Cos_nonnegAbs.
  eapply leEq_transitive;
      [ | apply ThetaErrLe90IR].
  apply ThetaEv2To3_3.
  unfold le, Le_instance_QTime.
  repnd. split; try lra.
  unfoldMC. unfold Plus_instance_QTime.
  simpl.   pose proof (Q.le_min_r qtrans mt3).
  lra. 
- rewrite XDerivAtTime.
  unfold stdlib_rationals.Q_le in Hb.
  repnd.  
  assert ((mt2 <= t <= mt3)%Q) as Hbb by
    (split; try lra).
  rewrite mult_commut_unfolded.
  apply ThetaEv2To3_3 in Hbb.
  apply mult_resp_leEq_both; trivial;
    [eauto 2 with CoRN; fail| apply CosThetaErrGe0|  |].
  + eapply leEq_transitive;[| apply Hsrr;split; lra].
    apply inj_Q_leEq. simpl. reflexivity.
  + setoid_rewrite CosEven2 at 2;
      [|eapply leEq_transitive;[apply Hbb| apply ThetaErrLe90IR]].
    apply TrigMon.Cos_resp_leEq;
        trivial;[apply AbsIR_nonneg| apply ThetaErrLe1180].
Qed.

Lemma XChangeLBEv2To3 :
  ∃ qtrans : QTime,  (mt2 <= qtrans <= mt2 + reacTime)%Q
  ∧ (Cos (θErrTrans + θErrTurn) 
        * (linspeed - transErrTrans)%Q 
        * (Qmax 0 (mt3 - qtrans))%Q)
      ≤  ({X rotOrigininPos} mt3 [-] {X rotOrigininPos} mt2).
Proof.
  pose proof XDerivLBEv2To3 as H.
  cbv zeta in H.
  destruct H as [qtrans H]. 
  repnd.
  remember (mkQTime1 _ _ Hll) as qtranst.
  exists qtranst.
  split;[split;subst qtranst; assumption|].
  match goal with
  [|- ?l ≤ _] => assert (l [=] l [+] [0] [*] (Q2R(qtranst -mt2)%Q))
        as Heq by ring
  end.
  rewrite <- inj_Q_Zero in Heq.
  rewrite Heq. clear Heq.
  destruct (Qlt_le_dec qtrans mt3) as [Ht | Ht].
- assert ({X rotOrigininPos} mt3[-]{X rotOrigininPos} mt2
          [=]
          ({X rotOrigininPos} mt3[-]{X rotOrigininPos} qtranst)
          [+]({X rotOrigininPos} qtranst [-]{X rotOrigininPos} mt2))
     as Heq by (unfold cg_minus; ring).
  rewrite Heq. clear Heq.
  pose proof (proj2 (Q.min_l_iff qtrans mt3)) as XX.
  DestImp XX; [| lra].
  setoid_rewrite XX in Hrl.
  apply plus_resp_leEq_both;
    [|eapply TDerivativeLBQ; subst qtranst; simpl; eauto 2 with ICR; try lra].
  unfold le, lt, stdlib_rationals.Q_lt, Le_instance_QTime in Hrr.
  Local Opaque Cos Q2R.
  rewrite (λ a b, proj2 (Q.max_r_iff a b));
    [|subst qtranst; simpl; lra].
  eapply TDerivativeLBQ; subst qtranst; simpl; eauto 2 with ICR; try lra.
- clear Hrr.
  rewrite (λ a b, proj2 (Q.max_l_iff a b));
    [|subst qtranst; simpl; lra].
  Local Transparent Q2R.
  unfold Q2R.
  rewrite inj_Q_Zero.
  rewrite inj_Q_Zero.
  autounfold with IRMC.
  match goal with
  [ |- ?l [<=] _ ] =>
    assert (l [=] [0]) as Heq by ring
  end.
  rewrite Heq.
  clear Heq.
  assert ([0][=][0][*](Q2R (mt3-mt2))) as Heq by ring.
  rewrite Heq at 1. clear Heq.
  rewrite <- inj_Q_Zero at 1.
  eapply TDerivativeLBQ; eauto 1 with ICR;
    [apply MotorEventsNthTimeIncSn|].
  intros ? Hb.
  apply Hrl. clear Hrl.
  repnd.
  split; try lra.
  rewrite (λ a b, proj2 (Q.min_r_iff a b)); try lra.
Qed.

Lemma XChangeLBEv2To3_2 :
  (Cos (θErrTrans + θErrTurn) 
      * (linspeed - transErrTrans)%Q 
      * (Ev23TimeGapLB - QT2Q reacTime))
  ≤  ({X rotOrigininPos} mt3 [-] {X rotOrigininPos} mt2).
Proof.
  destruct XChangeLBEv2To3 as [qtrans Hd].
  repnd.
  eapply leEq_transitive;[|apply Hdr].
  apply mult_resp_leEq_lft.
- assert (mt3-mt2-reacTime <=(mt3 - qtrans))%Q as Hle by lra.
  apply (inj_Q_leEq IR) in Hle.
  eapply leEq_transitive;[| apply inj_Q_leEq; apply Q.le_max_r].
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

Lemma XChangeLBEv2To3_3 :
  (Cos (θErrTrans + θErrTurn)) 
      * (idealX' - Ev23TimeGapLB*(QT2Q transErrTrans)
          + (transErrTrans* reacTime - linspeed*reacTime -timeErr*linspeed)%Q) 
  ≤  ({X rotOrigininPos} mt3 [-] {X rotOrigininPos} mt2).
Proof.
  pose proof (XChangeLBEv2To3_2) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[|apply Hyd].
  clear Hyd.
  apply eqImpliesLeEq.
  unfoldMC. autounfold with IRMC.
  rewrite  <- mult_assoc_unfolded.
  apply mult_wdr.
  unfold Ev23TimeGapLB, transDuration.
  unfoldMC. autounfold with IRMC.
  unfold QT2R, Q2R.
  rewrite inj_Q_minus.
  rewrite inj_Q_minus.
  rewrite inj_Q_minus.
  ring_simplify.
  unfold cast, Cart_CR_IR.
  rewrite CR_mult_asIR.
  rewrite CRasIRInj.
  rewrite mult_commut_unfolded, <- mult_assoc_unfolded.
  rewrite mult_assoc_unfolded.
  rewrite ring_distr1.
  autorewrite with QSimpl.
  simpl.
  assert (/ linspeed * linspeed == 1)%Q as Heq
    by (field; destruct linspeed; simpl; lra).
  rewrite Heq.
  clear Heq.
  unfold idealX'.
  unfold cast, Cart_CR_IR.
  unfold CanonicalNotations.norm.
  unfold CR.
  unfold Complete.
  simpl.
  remember  (CRasIR
    (NormSpace_instance_Cart2D Q (RegularFunction Q_as_MetricSpace) target))
    as crt.
  clear Heqcrt.
  unfold cg_minus.
  autorewrite with InjQDown.
  simpl. ring.
Qed.

Definition X'DiffLB: IR :=  '(eeev 0 w) * (QT2R reacTime + Ev01TimeGapUB)
+ idealX' * (1 - Cos (θErrTrans + θErrTurn))
+ (Cos (θErrTrans + θErrTurn)) 
      * (Ev23TimeGapLB*(eeev linspeed 0)
          + (linspeed*reacTime + timeErr*linspeed -(eeev linspeed 0)* reacTime)%Q).


Lemma Ev3X'DiffLb : idealX' - X'DiffLB ≤ {X rotOrigininPos} mt3.
Proof.
  pose proof XChangeLBEv2To3_3 as Ha.
  pose proof PosRotAxisAtEV2 as Hb.
  apply proj1 in Hb.
  unfold XYAbs in Hb.
  Local Opaque rotOrigininPos.
  simpl in Hb.
  apply AbsIR_imp_AbsSmall in Hb.
  apply proj1 in Hb.
  pose proof (plus_resp_leEq_both _ _ _ _ _ Ha Hb) as Hadd.
  clear Ha Hb.
  autounfold with IRMC in Hadd.
  Local Opaque Q2R.
  simpl in Hadd.
  unfold cg_minus in Hadd. ring_simplify in Hadd.
  eapply leEq_transitive;[|apply Hadd].
  apply eqImpliesLeEq.
  unfold  X'DiffLB, idealX'.
  clear. autounfold with IRMC.
  unfold One_instance_IR.
  rewrite transErrTransEq.
  rewrite transErrRotEq.
  unfold cast, Cart_CR_IR, Cast_instace_Q_IR.
  Local Transparent Q2R QT2R.
  unfold QT2R. unfold Q2R.
  unfold cg_minus.
  remember (CRasIR (|target |)) as crt.
  clear Heqcrt.
  autounfold with IRMC.
  autorewrite with InjQDown.
  remember (Cos (θErrTrans[+]θErrTurn)) as cc.
  clear Heqcc. 
  unfold cg_minus.
  ring_simplify.
  reflexivity.
Qed.

End RobotProgam.
