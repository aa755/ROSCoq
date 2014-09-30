Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export roscore.

Set Implicit Arguments.

Record ROSCyberPhysSystem := {
   nodes: list RosNode
  (* a proof that nodes have unique names and locations *)
}.

Record Event (cp : ROSCyberPhysSystem) := {    
    location : RosNode;
    time : Time;
    mesg : Message;
    locValid : In location (nodes cp)
}.


