
Require Export iCreateMoveToLoc.

Definition rotSpeedRadPerSec : Qpos := QposMake 1 2.

Definition speedMetresPerSec : Qpos := QposMake 1 10.

Require Import RoshaskMsg.

Definition  delResSecInv :  positive := delayResolutionSecInv.

Definition delEpsSec : Qpos := QposMake 1  delResSecInv.

Definition initDelayLin : Qpos := QposMake 1 1.

Definition robotProgramInstance (delayLinSec : Qpos) :  PureProcWDelay TARGETPOS VELOCITY :=
  robotPureProgam 
          rotSpeedRadPerSec 
          speedMetresPerSec
          delayLinSec
          delEpsSec
          delResSecInv.


Definition SwProcessInstance : Process Message (list Message):=
{|
State := Q;
curState := initDelayLin;
handler := λ (ins : Q) (inm : Message),
           (ins * 2,
           delayedLift2Mesg (robotProgramInstance (QabsQpos ins)) inm) |}.

Extraction Language Haskell. 
Require Import ExtrHaskellBasic.


Require Import RoshaskImpl.
Require Import RoshaskTypes.

Require Import Ros.Geometry_msgs.Vector3.


Definition toVector3  (x:Q) (y:Q) : Vector3 :=
  {| _x := toRoshaskFloat x ; _y := toRoshaskFloat y; _z:= toRoshaskFloat 0|}.
  
Definition CQtoVector3  (pq :Cart2D Q) : Vector3 :=
          toVector3 (X pq) (Y pq).

Definition PQtoVector3  (pq :Polar2D Q) : Vector3 :=
          toVector3 (rad pq) (θ pq).

Definition fromVector3 (v: Vector3) : Q × Q :=
  (fromRoshaskFloat (_x v), fromRoshaskFloat (_y v)).

Definition CQfromVector3 (v: Vector3) : Cart2D Q :=
  let (x,y) := fromVector3 v in
  {| X := x; Y:= y|}.

Definition PQfromVector3 (v: Vector3) : Polar2D Q :=
  let (x,y) := fromVector3 v in
  {| rad := x; θ := y|}.

  Require Import String.
Instance TopicRosHaskImplementable : RosHaskImplementable Topic:=
  {|
topicImplType := λ _ : Topic, Vector3;
topicImplTypeCorrect := λ _ : Topic, Vector3.ROSMsgInstance;
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

Require Import RoshaskNodeMonad.
Definition icreateRoshaskSwNode : Node unit :=
  let prf := decAuto (0 < Datatypes.length (fst (locTopics SWNODE)))%nat I in
  runSwNode Topic SwProcessInstance (locTopics SWNODE) prf.

Extraction "src/examples/icreateMoveToLoc.hs" icreateRoshaskSwNode.
