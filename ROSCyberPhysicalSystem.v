Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export roscore.

Set Implicit Arguments.

Record ROSCyberPhysSystem := {
   NodeIndex : Set;
   nodes: NodeIndex -> RosNode
  (* a proof that nodes have unique names and locations *)
}.


Class DecEq (T : Type) :=
{
    eqdec : forall (a b :T), {a=b} + {a<>b}
}.

(** In any run, there will only be a finitely
    many events. So the collection of events
    in the entire system can be represented
    as a list. [Event] is a type
    representing all events in the system *)

Class EventType (T: Type) 
      {cp : ROSCyberPhysSystem} 
      {deq: DecEq T}
    := {    
    eTime : T -> Time;
    eLoc : T ->  (NodeIndex cp);
    eLocIndex : T -> nat;
    recdMesg : T -> Message    
}.

Require Export Coq.Init.Wf.

(** Both send and receives are messages *)


Record SystemOrder (E :Type)  
    {cp : ROSCyberPhysSystem} 
    {et : @EventType E cp}
:=
{
    causedBy : E -> E -> Prop
    localCausal : forall (e1 e2 : E),
        (eLoc e1) = (eLoc e2)
        -> causedBy e1 e2
        -> 
    causalWf : 
}.




(** we need to axiomatize a mailbox in event ordering *)

