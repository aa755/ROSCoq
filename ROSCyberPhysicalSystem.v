Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export roscore.

Set Implicit Arguments.

Record ROSCyberPhysSystem := {
   NodeIndex : Set;
   node: NodeIndex -> RosNode
  (* a proof that nodes have unique names and locations *)
}.


Class DecEq (T : Type) :=
{
    eqdec : forall (a b :T), {a=b} + {a<>b}
}.

(** received messages are enqued in a mailbox
    and the dequed *)
Inductive EventKind := sendEvt | enqEvt | deqEvt.

Definition boolToProp (b : bool) : Prop :=
match b with
| true => True
| false => False
end.

Add LoadPath "../../../nuprl/coq".

Fixpoint decreasing (ln : list nat) : Prop :=
match ln with
| nil => True
| h :: tl => True
end.

Fixpoint increasing (ln : list nat) : Prop :=
match ln with
| nil => True
| h :: tl => True
end.

(** In any run, there will only be a finitely
    many events. So the collection of events
    in the entire system can be represented
    as a list. [Event] is a type
    representing all events in the system *)

Class EventType (T: Type) 
      {Loc : Type} 
      {deq: DecEq T} := {
  eLoc : T ->  Loc;
  eMesg : T -> Message;
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

  localEvts : Loc -> (nat -> option T);

  locEvtIndex : forall (l: Loc) n t,
    ((eLoc t) = l /\ (eLocIndex t) = n)
    <-> localEvts l n = Some t;

  localIndexDense : forall (l: Loc) n t m,
    ((eLoc t) = l /\ (eLocIndex t) = n)
    -> m <n 
    -> {tm : T | ((eLoc tm) = l /\ (eLocIndex tm) = m)}    
 }.

Require Export Coq.Init.Wf.

(** Both send and receives are events *)

Record PossibleEventOrder (E :Type)  
    {cp : ROSCyberPhysSystem} 
    {deq : DecEq E} 
    {et : @EventType E (NodeIndex cp) deq} := {
    causedBy : E -> E -> Prop;
    localCausal : forall (e1 e2 : E),
        (eLoc e1) = (eLoc e2)
        -> (causedBy e1 e2 <-> eLocIndex e1 < eLocIndex e1);

    globalCausal : forall (e1 e2 : E),
        causedBy e1 e2
        -> eTime e1 [<] eTime e1;

    (** the stuff below can probably be
      derived from the stuff above *)

    causalWf : well_founded causedBy
    
}.

Fixpoint prevProcessedEvents  {E L :Type}
    {deq : DecEq E}
  {et : @EventType E L deq} (m : nat)
  (locEvents : nat -> option E) : list E :=
  match m with
  | 0 => nil
  | S m' => (match locEvents m' with
              | Some ev => match (eKind ev) with
                            | deqEvt => (ev)::nil
                            | _ => nil
                            end
              | None => nil (* this will never happen *)
             end
            )++ (prevProcessedEvents m' locEvents)
  end.


Fixpoint futureSends  {E L :Type}
    {deq : DecEq E}
  {et : @EventType E L deq} (start : nat) (len : nat)
  (locEvents : nat -> option E) : list Message :=
  match len with
  | 0 => nil
  | S len' => 
      match locEvents (start + len') with
      | Some ev => 
          match (eKind ev) with
          | sendEvt => (eMesg ev) :: (futureSends (S start) len' locEvents)
          | deqEvt => nil (* event processing is atomic, as of now*)
          | enqEvt => (futureSends (S start) len' locEvents)
          end
      | None => nil (* this will never happen *)
       end
  end.

Definition sendsInRange  {E L :Type}
    {deq : DecEq E}
  {et : @EventType E L deq} (startIncl : nat) (endIncl : nat)
  (locEvents : nat -> option E) : list Message :=
  futureSends startIncl (endIncl + 1 - startIncl) locEvents.

Definition CorrectSWNodeBehaviour (E L :Type)  
    {deq : DecEq E}
    {et : @EventType E L deq}
    (swNode : RosSwNode)
    (locEvts: nat -> option E) : Prop :=
  forall n: nat,
  match (locEvts n) with
  | None  => True
  | Some ev => 
      let procEvts := prevProcessedEvents (S (eLocIndex ev))locEvts in
      let procMsgs := map eMesg procEvts in
      let lastOutMsgs := getLastOutputL (process swNode) procMsgs in
      let evIndex := eLocIndex ev in

      match (eKind ev) with
      | deqEvt =>  
          exists len, futureSends (eLocIndex ev) len locEvts = lastOutMsgs

      | sendEvt => 
        match procEvts with
        | nil => False
        | last :: _ => 
            length (sendsInRange (eLocIndex last)  evIndex locEvts)
               <= length lastOutMsgs 
        end

      | enqEvt => True (* messages are always welcome. When modelling a finite sized mailbox,this may no longer be true *)
      end
  end.



    (** FIFO queue axiomatization *)




(** we need to axiomatize a mailbox in event ordering *)

