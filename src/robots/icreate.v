Require Export Coq.Program.Tactics.
Require Export LibTactics.
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

Require Import Vector.
Require Import CPS.
Require Import CPSUtils.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import CartCR.

Definition initialVel : (Polar2D Q) := {|rad:=0; θ:=0|}.

Require Export CartIR.


Notation FConst := ConstTContR.
Notation FSin:= CFSine.
Notation FCos:= CFCos.


(**
* Specifying robots.
*)

(**
A cyber-physical system (CpS) typicall consistes of one or more robots (broadly interpreted), and 
one or more software agents (controllers).

We want to be able to specify a CpS by composing the specifications 
of its robots and other software components.
As explained in the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#,
a specification CpS involved a specification of its physical
specification of its physical model and mutually independent specifications of each of its agents. 
Our goal here is to specify the physical model of the robot and its hardware agents which represent
its device-drivers. We do this in a general way so that it can be instantiated in the specification
of various CpSes.
*)

(**
* The physical model of iRobot Create
*)

(**
As described in Sec. 2 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#,
a physical model is a type that specifies how each relevant physical
quantities evolved over time, and the physical laws governing that evolution.
Hence, a physical model of a CpS would typically be a product of the physical models 
of each component robots.

Below is the specification of the physical model of the iCreate robot.
This specification is explained as an example in
Sec. 2 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#

*)
Record iCreate : Type := {
  position :> Cart2D TContR;          (* x, y co-ordinates*)
  theta : TContR;                       (* orientation *)
  transVel : TContR;             (* translation vel (along [theta]) *)
  omega : TContR;

  (** differential equations *)
  derivRot : isDerivativeOf omega theta;
  derivX : isDerivativeOf (transVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (transVel * (FSin theta)) (Y position);

  (** Initial (at time:=0) Conditions *)  

  initPos:  ({X position} 0) ≡ 0 ∧ ({Y position} 0) ≡ 0;
  initTheta:  ({theta} 0) ≡ 0;
  initTransVel : ({transVel} 0) ≡ (rad initialVel);
  initOmega : ({omega} 0) ≡ (θ initialVel)
}.



Section HardwareAgents.

(**
* Specifying the hardware agents (device-drivers)
*)

(**
The Robot Operating System (ROS) typically provides drivers 
for robots. These are typically represented as agents (nodes) of a distributed system.
These nodes communicate on designated topics,
e.g. to subscribe to actuation commands, or to publish sensed values.
To reason about such robots, one can specify them as ROSCoq hardware agents.
We want the specification to be general enough so that these agents can be used
in a wide range of CpSes. So we parametrize the specification with an arbitrary
type for topics, and arbitrary members denoting the designated topics.

Below, we illustrate this method with a specification of the driver of an iCreate robot,
as explained in Sec. 4.1 of the 
#<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/ROSCOQ.pdf">ROSCoq paper</a>#

We assume an arbitrary type for topics.
*)


Context 
  `{rtopic : TopicClass RosTopic} 
  `{dteq : Deq RosTopic}.

(**
We assume a designated topic which the driver subscribes to, to receive velocity commands
*)

Variable VELOCITY : RosTopic.

(**
We assume that the payload type of the above topic is [Polar2D Q].
Members of [Polar2D Q] are pairs of rationals. For example, for rationals
[a] and [b], [{| rad :=a ; θ :=b |}] is a member of [Polar2D Q].
The [rad] component denotes the requested linear velocity, and the
[θ] component denotes the requested angular velocity.
*)

Hypothesis VelTOPICType : (topicType VELOCITY ≡ Polar2D Q).

(**
A bound on the time the robot takes to nearly achieve a requested velocity.
This can be understood as a bound on the width of the vertical green
rectangle below.
*)

Variable reacTime : QTime.

(* It is more sensible to change the type to [QNonNeg]
    as the value certainly does not represent time.
    However, the coercion QT2Q does not work then *)

Local Notation QNonNegative := QTime.

(**
Bound on actuation error for given liner and angular velocities.
This is related to the height of the horizontal rectangle in the figure below.
*)

Variable motorPrec : Polar2D Q → Polar2D QNonNegative.

(**
The robot eventually comes to a complete stop when requested to do so.
*)

Hypothesis motorPrec0 : motorPrec {| rad :=0 ; θ :=0 |} ≡ {| rad :=0 ; θ :=0 |}.
  
Close Scope Q_scope.

(**
The definition below is the key ingredient of the specification of the device driver.
Suppose the driver receives a payload [cmd] of type [Polar2D Q] at time [tm].
Consider some later time instant [t] such that no other messages were received between
[tm] and [t].
[correctVelDuring] specified how the robot's linear and angular velocity must have
evolved from time [tm] to [t].
The first conjunct specifies the evolution of the linear velocity, and the second one
which is similar,  specifies the evolution of the angular velocity.
To understand a conjunct, we hanve to understand the definition of [changesTo]
(click it to jump to its definition).

The figure below illustrates it pictorially.
#<img src="icreateHwAgentSpec.svg"/>#
*)

Definition correctVelDuring
  (cmd : (Polar2D Q)) 
  (tm: QTime)
  (t : QTime) 
  (ic: iCreate) :=

  changesTo 
    (transVel ic) 
    tm
    t 
    (rad cmd) 
    reacTime 
    (rad  (motorPrec cmd))
  ∧ 
  changesTo 
    (omega ic) 
    tm 
    t 
    (θ cmd) 
    reacTime 
    (θ (motorPrec cmd)).

Section LastVelocityMessage.

Context `{etype : @EventType _ _ _ Event  tdeq}.


Typeclasses eauto :=2.

(**
Given [evs], the  sequence of events that happened at the hardware agent,
and any time [t],
the function below computes the latest velocity message received before time [t],
and the time when it was received.
*)

Definition latestVelPayloadAndTime
  (evs : nat -> option Event) (t : QTime) : ((Polar2D Q) × QTime) :=
(@transport _ _ _ (λ t, t -> t ** QTime) VelTOPICType 
   (lastPayloadAndTime VELOCITY evs t)) initialVel.

(**
Now we just consider any time instant [t] and enforce that the velocity
evolved correctly, as explained above, from the time instant the latest message
before [t] was received and till [t].
*)

Definition corrSinceLastVel
  (evs : nat -> option Event)
  (t : QTime)
  (ic: iCreate) :=
let (cmd, tm) := latestVelPayloadAndTime evs t in
correctVelDuring cmd tm t ic.

End LastVelocityMessage.

(**
The final specification of the hardware agent just enforces the above for all 
(rational) time instants. Ideally, one might want to enforce it for even the irrational
time instants. However, because velocity is assumed to be a continuous function,
the specification at rational time instants is sufficient. 
*)

Definition HwAgent  : Device iCreate :=
λ (Event:Type) 
(tdeq : DecEq Event) (_ : EventType Event) (robot: iCreate) (evs : nat -> option Event) ,
  (∀ t: QTime, corrSinceLastVel evs t robot)
  ∧ ∀ n:nat, isDeqEvtOp (evs n).

(**
See #<a href="http://www.cs.cornell.edu/~aa755/ROSCoq/coqdocnew/ICreateMoveToLoc.spec.html">examples/icreateMoveToLoc/spec.v</a># 
for an example of using  the definitions
in this file while specifiying a CpS.
*)

(* partial simplified definition shown in the paper : 
Definition eeev  a b : Q  :=
 (rad (motorPrec {|rad:= a; θ:= b|})).

Definition eeew  a b : Q :=
 (θ (motorPrec {|rad:= a; θ:= b|})).

Definition HwAgentP (ic: iCreate) (evs : nat -> option Event): Prop :=
onlyRecvEvts evs ∧ ∀ t: QTime,
  let (lastCmd, tm ) := latestVelPayloadAndTime evs t in 
  let a : Q := rad (lastCmd) in
  let b : Q := θ (lastCmd) in
  ∃ tr : QTime, (tm ≤ tr ≤ tm + reacTime)
    ∧ (∀ t' : QTime, (tm ≤ t' ≤ tr) 
        → (Min ({transVel ic} tm) (a - eeev a b) 
            ≤ {transVel ic} t' ≤ Max ({transVel ic} tm) (a+ eeev a b)))
    ∧ (∀ t' : QTime, (tr ≤ t' ≤ t) → |{transVel ic} t' - a | ≤ Q2R (eeev a b)).

Lemma HwAgentPCorr1 :
  ∀ icr evs,
  HwAgent icr evs ->  HwAgentP icr evs.
Proof.
  intros ? ? H.
  destruct H as [Hr H].
  split; [assumption|]. clear H.
  intros t.
  specialize (Hr t).
  unfold corrSinceLastVel in Hr.
  destruct (latestVelPayloadAndTime evs t) as [lc lt].
  apply proj1 in Hr.
  destruct Hr as [qtrans Hr].
  exists qtrans.
  unfold le, Le_instance_QTime.
  autounfold with IRMC. unfold Plus_instance_QTime.
  unfoldMC. repnd.
  split; auto.
  unfold eeev.
  destruct lc.
  simpl Vector.rad.
  simpl Vector.rad in Hrrl, Hrrr.
  unfold Q2R. setoid_rewrite inj_Q_inv.
  split; auto.
  unfold between, Q2R in Hrrr.
  intros ? H.
  apply Hrrr in H.
  autorewrite with QSimpl in H.
  exact H.
Qed.
*)

End HardwareAgents.
