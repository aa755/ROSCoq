
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

CoFixpoint tranControllerProgram (state : bool): Process Message (list Message).
  constructor. intro m.
  destruct m as [topicName payLoad].
  case (eqdec topicName "timerSend"); intro Hc; subst.
  - split. 
    + exact (tranControllerProgram (negb state)).
    + apply cons;[ | exact nil]. exists "motorRecv".
      simpl. unfold stringTopic2Type. simpl.
      destruct state ;[exact 1 | exact (0-1)].
  - exact (tranControllerProgram state,nil).
Defined.


(*
Definition locNode (rl : RosLoc) : RosNode :=
match rl with
| baseMotor =>
| timerNode =>
| digiController =>
end.
*)

Instance rllllfjkfhsdakfsdakh : RosLocType TrainState RosLoc.

