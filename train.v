
Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export ROSCyberPhysicalSystem.
Require Export String.
Require Export trainDevs.

Instance stringdeceqdsjfklsajlk : DecEq string.
constructor. exact string_dec.
Defined.

Open Scope string_scope.

Inductive Void :=.

(** When adding a nrew topic, add cases of this function *)
Definition stringTopic2Type (s : string) : Type :=
if (eqdec s "motorRecv") then Q else
if (eqdec s "timerSend") then unit else Void.


Instance  ttttt : @RosTopicType string _.
constructor. exact stringTopic2Type.
Defined.

Inductive RosLoc := baseMotor | timerNode | digiController.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.

CoFixpoint digiControllerProgram (state : bool): Process Message (list Message).
  constructor. intro m.
  destruct m as [topicName payLoad].
  case (eqdec topicName "timerSend"); intro Hc; subst.
  - split. 
    + exact (digiControllerProgram (negb state)).
    + apply cons;[ | exact nil]. exists "motorRecv".
      simpl. unfold stringTopic2Type. simpl.
      destruct state ;[exact 1 | exact (0-1)].
  - exact (digiControllerProgram state,nil).
Defined.

Definition t1 : Time.
exists [1]. unfold iprop.
eauto with *.
Defined.

Definition digiControllerTiming : ProcessTiming (digiControllerProgram true) :=
 fun m => t1.


Definition ControllerNode : RosSwNode :=
Build_RosSwNode ("timerSend"::nil) ("motorRecv"::nil) digiControllerTiming.

Definition TimerNode : RosInpDevNode unit:=
Build_RosInpDevNode "timerSend" (Timer 1).

Definition BaseMotorNode : RosOutDevNode R :=
(Build_RosOutDevNode "motorRecv" VelOutDevice).

Definition locNode (rl : RosLoc) : RosNode :=
match rl with
| baseMotor => ControllerNode
| timerNode => TimerNode
| digiController => BaseMotorNode
end.

Instance rllllfjkfhsdakfsdakh : RosLocType TrainState RosLoc.
apply (Build_RosLocType _ _ _ locNode (fun srs dest => Some t1)).
 intros ts rl. destruct rl; simpl; try (exact tt).
  - exact (fun t => tt).
  - exact (fun t => vX (ts t)).
Defined.

Section Train.
Context  
  (physics : Time -> TrainState)
 `{etype : @EventType _ _ _ Event RosLoc tdeq }.

Open Scope R_scope.

Definition  TrainSpec : Prop :=
  forall (eo : PossibleEventOrder physics) (t:Time), ([0]  <= (posX (physics t)) <= [1]).

(** To begin with, let the VelControl device control position
    make it exact if needed *)


