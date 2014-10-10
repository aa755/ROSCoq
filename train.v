
Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export ROSCyberPhysicalSystem.
Require Export String.

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



Instance rllllfjkfhsdakfsdakh : RosLocType RosLoc.
(* we can't define the [timeValuedEnv]  component because
   it is only function of the RosLoc, which does not have enough information.
   One could add (Time -> R) to some nodes in RosLoc, but that
   will give us infinitely many nodes, and also make equality undecidable.
   [timeValuedEnv] is also a function of environment
 *)


