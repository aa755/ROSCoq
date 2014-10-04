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
  mesg : T -> Message;
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

  localIndexDense : forall (l: Loc) n t,
    ((eLoc t) = l /\ (eLocIndex t) = n)
    -> forall m, m <n ->  
        {tm : T | ((eLoc tm) = l /\ (eLocIndex tm) = m)}
    
 }.

    prevProcessedEvts : forall loc evt,
      { l :list T | decreasing (map eLocIndex l) /\
              forall e, 
              (In e l <-> 
                    (eLoc e =loc
                    /\ eKind e = deqEvt
                    /\ eLocIndex e < (eLocIndex evt))) };

    futureSends : forall loc evt,
      { l :list T | decreasing (map eLocIndex l) /\
              forall e, 
              (In e l <-> 
                    (eLoc e =loc
                    /\ eKind e = deqEvt
                    /\ eLocIndex e < (eLocIndex evt))) };

    (** FIFO queue axiomatization *)

    correctBehaviour : forall e,
    let procEvts := (proj1_sig (prevProcessedEvts (eLoc e) e)) in
    let procMsgs := map mesg procEvts in
    match ((node cp) (eLoc e)) with
    | rsw swnd =>
       match eKind e with
       | sendEvt => 
            match procMsgs with
            | nil => False
            | last :: rest => 
                In (mesg e) (getOutputL (process swnd) rest last)
            end
       | deqEvt => 
          let ourM := (getOutputL (process swnd) procMsgs (mesg e))
          in True
       | enqEvt => True 
    (* messages are always welcome. 
        when modelling a finite sized mailbox, 
      this may no longer be true *)
       end
    | rhi _ _ => True
    | rho _ _ => True
    end
  }.

Require Export Coq.Init.Wf.

(** Both send and receives are events *)

Record PossibleEventOrder (E :Type)  
    {cp : ROSCyberPhysSystem} 
    {deq : DecEq E} 
    {et : @EventType E cp deq} := {
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

