Require Import spec.



(** 
* Instantiating the parameters
*)

(**
So far, our definitions and proofs were parametric over
details like our choice of linear and angular speed,
accuracy of the timer used to delay sending of messages,
and the desired accuracy for approximating the delay values.
To actually run our program, we need to instantiate those parameters:
*)

(**
We chose some reasonable speed values that the hardware is capable of achieving.
Our proofs derive a bound of the error in the final position w.r.t the
actuation error.
*)

Definition rotSpeedRadPerSec : Qpos := QposMake 1 2.

Definition linSpeedMetresPerSec : Qpos := QposMake 1 10.

Require Import RoshaskMsg.

(**
[RoshaskMsg.delayResolutionSecInv] denotes the timing resolution of our Haskell shim,
which is currently 1 microsecond.
*)
Definition  delResSecInv :  positive := RoshaskMsg.delayResolutionSecInv.

Definition delEpsSec : Qpos := QposMake 1  delResSecInv.

Definition initDelayLin : Qpos := QposMake 1 1.

Require Import message.

Definition SwProcessInstance : Process Message (list Message):=
  @SwProcess
          rotSpeedRadPerSec 
          linSpeedMetresPerSec
          delResSecInv
          delEpsSec
          initDelayLin.

(** 
* Providing an instance of [RosHaskImplementable]
*)

(**
Now that we have the concrete Coq program [Process] for the software agent,
we are almost ready to extract it to Haskell.

Before that, we need to provide some implementation details specific to the
Robot Operating System.
This is accomplished by showing that the [Topic] type we used in specification ([spec])
is an instance of [RosHaskImplementable].
 
One has to map the topics used so far to actual topics in the Robot Operating System.
Recall that followinng ROS, agents publish and subscribe to topics, and don't directly
communicate with other agents.
Also, for each topic, we need to map its payload type to a message type recognized by
the Robot Operating System. Note that the agents receiving our messages 
may be written in other langaues such as C, as is often the case foe hardware agents.

The driver for our iRobot Create received messages of type
Ros.Geometry_msgs.Vector3. 
See: <a href="http://docs.ros.org/api/geometry_msgs/html/msg/Vector3.html">
http://docs.ros.org/api/geometry_msgs/html/msg/Vector3.html</a>
We have already generated the Coq type for this message : [Ros.Geometry_msgs.Vector3]
See the ROSCoq wiki to find out how to generate Coq message types for types used by the
Robot Operating System.

Even though the type of linear and angular velocities were rational numbers
fr convenience in reasoning, the driver receives a [Ros.Geometry_msgs.Vector3]
which is a triple of floats. We provide functions to interconvert between Coq rationals and machine floats.
This does not make our proofs useless. Firstly, we get to choose the desired linear
and angular velocity. Above, we chose rationals which have exact representations as floats.
Also, our specification already allow for actuation errors.
*)

Extraction Language Haskell. 
Require Import ExtrHaskellBasic.


Require Import RoshaskImpl.
Require Import RoshaskTypes.

Require Import Vector.
Require Import Ros.Geometry_msgs.Vector3.

Definition toVector3  (x:Q) (y:Q) : Vector3 :=
  {| _x := toRoshaskFloat x ; _y := toRoshaskFloat y; _z:= toRoshaskFloat 0|}.
  
Definition CQtoVector3  (pq :Cart2D Q) : Vector3 :=
          toVector3 (X pq) (Y pq).

Definition PQtoVector3  (pq :Polar2D Q) : Vector3 :=
          toVector3 (rad pq) (θ pq).

Definition fromVector3 (v: Vector3) : Q × Q :=
  (fromRoshaskFloat (_x v), fromRoshaskFloat (_y v)).

(** 
Interconvert between the payload types of ROSCoq topics and
the low level types used by the robot operating system.
These types can be the same (ideally). Then interconversion functions will be identities.
*)
Definition CQfromVector3 (v: Vector3) : Cart2D Q :=
  let (x,y) := fromVector3 v in
  {| X := x; Y:= y|}.

Definition PQfromVector3 (v: Vector3) : Polar2D Q :=
  let (x,y) := fromVector3 v in
  {| rad := x; θ := y|}.

Require Import String.

(** Finally, here is the instance *)

Instance TopicRosHaskImplementable : RosHaskImplementable Topic:=
  {|

(** 
All payload types map to [Vector3] of the Robot Operating System.
We say that [Vector3] is the implementation type of topics
*)

topicImplType := λ _ : Topic, Vector3;

(** 
Implementation types must be an instance of [ROSMsgType].
These instances are automatically generated when a Coq type is generated for a 
message type of the Robot Operating System.
*)

topicImplTypeCorrect := λ _ : Topic, Vector3.ROSMsgInstance;

(**
Interconvert between the payload types and implementation types. 
These are used by the shim when sending and receiving messages.
*)

toImpl := λ t : Topic,
          match t as t0 return (topicType t0 → Vector3) with
          | VELOCITY => PQtoVector3
          | TARGETPOS => CQtoVector3
          end;

fromImpl := λ t : Topic,
            match t as t0 return (Vector3 → topicType t0) with
            | VELOCITY => PQfromVector3
            | TARGETPOS => CQfromVector3
            end;

(**
In the Robot Operating System, each topic is identified by a string.
We have to provided such strings for each of the ROSCoq topics
*)
rosQualName := λ t : Topic,
               match t with
               | VELOCITY => "/icreate_cmd_vel"%string
               | TARGETPOS => "/targetpos"%string
               end |}.
(* Ltac used to create the bove instance:
apply Build_RosHaskImplementable with  (topicImplType := fun _:Topic => ROS_Geometry_Vector3);
  [eauto with *| | |].
- intro t. destruct t; [exact PQtoVector3| exact CQtoVector3].
- intro t. destruct t; [exact PQfromVector3| exact CQfromVector3].
  Open Scope string_scope.
- intro t. destruct t; [exact "/icreate_cmd_vel" | exact "/targetpos"].
  Close Scope string_scope.
Defined.
 *)

(** 
* Composing a ROSCoq software agent with the ROSCoq shim
*)

(**
The function [runSwNode] represents the ROSCoq shim which can be used to run ROSCoq software
agents ([Process]) on actual robots using the Robot Operating System.
[runSwNode] extracts to a Haskell function which uses roshask, the Haskell bindings for the
Robot Operating System. It requires that the [Topic] type of messages used by the program
be a instance of [RosHaskImplementable]
*)

Require Import MCInstances.
Require Import RoshaskNodeMonad.
Definition icreateRoshaskSwNode : Node unit :=
  let prf := decAuto (0 < Datatypes.length (fst (locTopics SWNODE)))%nat I in
  runSwNode Topic SwProcessInstance (locTopics SWNODE) prf.

(** 
* Generating the Haskell file
*)

Extraction "icreateMoveToLoc.hs" icreateRoshaskSwNode.
