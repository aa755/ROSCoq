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

(** received messages are enqued in a mailbox
    and the dequed *)
Inductive EventKind := sendEvt | enqEvt | deqEvt.


(** In any run, there will only be a finitely
    many events. So the collection of events
    in the entire system can be represented
    as a list. [Event] is a type
    representing all events in the system *)

Class EventType (T: Type) 
      {cp : ROSCyberPhysSystem} 
      {deq: DecEq T}
    := {
    eLoc : T ->  (NodeIndex cp);
    recdMesg : T -> Message;
    eKind : T -> EventKind;
    eTime : T -> Time;
    timeDistinct : forall (a b : T), 
      eTime a = eTime b
      -> a = b;
    eLocIndex : T -> nat;
    indexDistinct : forall (a b : T), 
      eLoc a = eLoc b
      -> eLocIndex a = eLocIndex b
      -> a = b;
    timeIndexConsistent : forall (a b : T),
      eLocIndex a < eLocIndex b
      -> eTime a [<] eTime b;

    processedEvts : forall loc n,
      { l :list T | forall e, 
              eLoc e =loc 
              -> eKind e = deqEvt
              -> (In e l <-> eLocIndex e < n) };

    causedByNode : forall e,
    eKind e = sendEvt
    ->
      match (rev (proj1_sig (processedEvts (eLoc e) (eLocIndex e)))) with
      | nil => False
      | h :: tl => True 
        (** after consming tl, when the local node gets h,
            it outputs the message in e*)
      end

    (** FIFO queue axiomatization *)
    (** *)
        
  }.

Require Export Coq.Init.Wf.

(** Both send and receives are events *)

Record PossibleEventOrder (E :Type)  
    {cp : ROSCyberPhysSystem} 
    {deq : DecEq E} 
    {et : @EventType E cp deq}
:=
{
    causedBy : E -> E -> Prop;
    localCausal : forall (e1 e2 : E),
        (eLoc e1) = (eLoc e2)
        -> causedBy e1 e2
        -> eLocIndex e1 < eLocIndex e1;

    localTotal : forall (e1 e2 : E),
        (eLoc e1) = (eLoc e2)
        -> {causedBy e1 e2} + {causedBy e2 e1};

    globalCausal : forall (e1 e2 : E),
        causedBy e1 e2
        -> eLocIndex e1 < eLocIndex e1;

    (** the stuff below can probably be
      derived from the stuff above *)

    causalWf : well_founded causedBy
    
}.




(** we need to axiomatize a mailbox in event ordering *)

