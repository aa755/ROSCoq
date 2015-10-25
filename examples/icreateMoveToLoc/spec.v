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

Set Implicit Arguments.

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

Context {rotspeed  : Qpos}.
Context  {linspeed  : Qpos}.

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

Context {delRes : Z⁺}.

(** The meaning of the 2 parameters below will be explained while explaining 
the program. *)

Context { delEps  : Qpos}.
Context { delay  : Qpos}.
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

Global Instance tdeq : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


(** The [TopicClass] also needs the payload type for eqch topic.*)

Definition topic2Type (t : Topic) : Type :=
match t with
| VELOCITY => Polar2D Q
| TARGETPOS => Cart2D Q 
end.


Global Instance  rtopic : @TopicClass Topic _.
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

Global Instance ldeq : DecEq RosLoc.
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
Context {reacTime : QTime}.
(** It is more sensible to change the type to [QNonNeg]
    as the value certainly does not represent time.
    However, the coercion QT2Q does not work then *)
Context {motorPrec : Polar2D Q → Polar2D QTime}.

Hypothesis motorPrec0 : motorPrec {| rad :=0 ; θ :=0 |} ≡ {| rad :=0 ; θ :=0 |}.

Definition HwAgent : Device PhysicalModel := HwAgent VELOCITY eq_refl reacTime motorPrec.


(**
*** Software Agent
*)
Definition PureSwProgram: PureProcWDelay TARGETPOS VELOCITY:=
  robotPureProgam.

Definition SwProcess : Process Message (list Message):= 
  mkPureProcess (delayedLift2Mesg (PureSwProgram)).

Context {procTime : QTime}.
Context {sendTimeAcc : Qpos}.
Require Export CoRN.model.metric2.Qmetric.


Definition ControllerNode : RosSwNode :=
  Build_RosSwNode (SwProcess) (procTime, sendTimeAcc).


(**
*** External Agent
*)
Context {target : Cart2D Q}.


Definition externalCmdSemantics
 : @NodeSemantics PhysicalModel Topic _ _:=
  λ Event edeq etype _ evs,
              isSendEvtOp (evs 0)
  ∧ (getSentPayloadOp TARGETPOS (evs 0) ≡ Some target)
              ∧ ∀ n : nat, (evs (S n)) ≡ None.

(**
*** The network model.
To specify a CPS, we need to specify its network model
In this example, we assume that the network reliably delivers messages.
*)

Context {expectedDelivDelay : Qpos}.
Context {delivDelayVar : Qpos}.

(* TODO : move the definition of locTopics to here *)
(* making this instance global is of no use because there are arguments in the context
which need to be instantiated *)
Instance lcon : @Connectivity Topic RosLoc.
constructor.
- exact locTopics.
- exact (λ _ _ t , ball delivDelayVar t (QposAsQ expectedDelivDelay)).
Defined.

Definition networkModel : NetworkModel RosLoc :=
fun Event  _ _ _ => @EOReliableDelivery  Topic Event RosLoc _ _ _ _ _ _. 

(**
*** Putting it all together. *)

Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| MOVABLEBASE => DeviceSemantics (λ ts,  ts) HwAgent
| SWNODE => SwSemantics ControllerNode
| EXTERNALCMD  => externalCmdSemantics
end.



Global Instance icreateMoveToLoc : @CPS PhysicalModel Topic _ _ RosLoc ldeq _ :=
Build_CPS _ _ _ locNode networkModel.



End RobotProgam.
