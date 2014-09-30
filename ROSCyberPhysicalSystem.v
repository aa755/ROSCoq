Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export roscore.

Set Implicit Arguments.

Record ROSCyberPhysSystem := {
   NodeIndex : Set;
   nodes: NodeIndex -> RosNode
  (* a proof that nodes have unique names and locations *)
}.

Record Event (cp : ROSCyberPhysSystem) := {    
    time : Time;
    recdMesg : Message
}.


Record EventOrdering (cp : ROSCyberPhysSystem) :=
{
    events : (NodeIndex cp) -> list (Event cp);
    causedBy : 
    
}.




(** we need to axiomatize a mailbox in event ordering *)

