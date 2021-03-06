
Require Export message.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.
Require Import Psatz.


Record SendEvtInfo := mkSendEvtInfo  {
(** 
Currently, every send event is in response to a received message.
As a response to every received message, a list messages (say [la]) can be sent,
possibly at different times.
Every send event sends a list of messages (say [ls]).
This field for a send event denotes the index of the head of [ls] in [la].
*)
    startIndex : nat
}.

(* 
In future, received messages will enqued in a mailbox
and then dequeued when its turn comes. There could be different queuing disciplines.
Currently, a [deqEvt] denotes the start of processing of a received event.
Queuing time at the destination is included in message delivery time of a message

TODO : rename deqEvt to recvEvt
*)
Inductive EventKind : Set := 
  | sendEvt (inf : SendEvtInfo) 
  | deqEvt.


Section Event.
Context  `{rtopic : TopicClass RosTopic}.

Close Scope Q_scope.


(** [Event] could just be a record type. However, over the time, we might need to
   extend it with more information. Hence, using a typeclass. *)
Class EventType (Event: Type) 
      (* minimum time diff between events *)
      {tdeq: DecEq Event}  := {
  eMesg : Event -> Message;
  eKind : Event -> EventKind;
  eTime : Event -> QTime;
  timeDistinct : forall (a b : Event), 
    eTime a = eTime b
    -> a = b;
(** 
Even some basic functionality, like finding the latest event before some timestamp,
we need to assume a positive lower bound on the time gap between any 2 events at a location.
Note that events at different locations can happen simultaneously.

This value is typically  constrained by the speed of the hardware, e.g. the NIC. 
The network model of a CPS can put additional constraints on this value.
*)

(*Ideally this should be a part of the definition of a CPS. 
But having it here is more convenient, because it saves one extra parameter in contexts
where a CPS instance is not available.
*)
  minGap : Q;
  (* remove this and change the type of [minGap] to [Qpos] *)
  minGapPos : (0 < minGap)%Q
 }.


(** 
A device is a relation between how the assosiated (measured/actuated)
physical quantity changes over time and a trace of events (messages sent/received)
at the device.
The latter is represented by the type [(nat -> option Event)].

[PhysQ] is the type denoting the evolution of physical quantities.

The type [(nat -> option Event)] needs to be specialized to indicate
facts that events are of same location and have increasing timestamps
Right now, a device property writer can assume that these hold.

For an example, see src/robots/icreate.v
*)

Definition Device  (PhysQ : Type ) : Type := forall {Event:Type} 
{tdeq : DecEq Event} {_ : EventType Event},
                  PhysQ
                  -> (nat -> option Event)
                  -> Prop.

End Event.

Close Scope Q_scope.
Arguments well_founded {A} P.

Class EventOrdering 
{Topic Event Loc  : Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq} 
(* assuming a whole CPS just to get this [minGap] value can cause circularity issues*)
  :=
{
  eLoc : Event ->  Loc;

  eLocIndex : Event -> nat;

  indexDistinct : forall (a b : Event), 
    eLoc a = eLoc b
    -> eLocIndex a = eLocIndex b
    -> a = b;
  timeIndexConsistent : forall (a b : Event),
    eLocIndex a < eLocIndex b
    <-> (eTime a < eTime b)%Q;

  localEvts : Loc -> (nat -> option Event);

  locEvtIndex : forall (l: Loc) n t,
    ((eLoc t) = l /\ (eLocIndex t) = n)
    <-> localEvts l n = Some t;

  localIndexDense : ∀ (l: Loc) n t (m : nat),
    ((eLoc t) = l /\ (eLocIndex t) = n)
    -> m <n 
    -> {tm : Event | ((eLoc tm) = l /\ (eLocIndex tm) = m)};

  eventSpacing :  forall (e1 e2 : Event),
    (eTime e1 >  minGap)%Q
    /\ (eLoc e1 = eLoc e2 
        -> minGap <= (Qabs ((eTime e1) - (eTime e2))))%Q;

  (* While this definitely a sensible property, is it needed anywhere? *)
  uniqueSendInfo :
    ∀ (si : SendEvtInfo) ev1 ev2,
      eLoc ev1 = eLoc ev2
      → eKind ev1 = sendEvt si
      → eKind ev2 = sendEvt si
      → ev1=ev2;

    causedBy : Event -> Event -> Prop;

    (* causalTrans : transitive _ causedBy; *)

    localCausal : forall (e1 e2 : Event),
        (eLoc e1) = (eLoc e2)
        -> (causedBy e1 e2 <-> eLocIndex e1 < eLocIndex e2);

    globalCausal : forall (e1 e2 : Event),
        causedBy e1 e2
        -> (eTime e1 < eTime e2)%Q;

    (* the properties below can probably be
      derived from the ones above *)

    causalWf : well_founded  causedBy
}.


Section EvtProps.

Context  
  `{rtopic : TopicClass RosTopic} 
  `{dteq : Deq RosTopic}
  `{etype : @EventType _ _ _ Event tdeq }.


(* Prop because the index is there in [ev] anyways *)
Definition isSendEvt (ev: Event) : bool :=
  match (eKind ev) with
  | sendEvt _ => true
  | _ => false
  end.

Definition isSendEvtOp (ev: option Event) : bool :=
  opApPure isSendEvt false ev.


Definition isDeqEvt (ev: Event) : bool :=
  match (eKind ev) with
  | deqEvt => true
  | _ => false
  end.

Definition isDeqEvtOp (ev: option Event) : bool :=
  opApPure isDeqEvt false ev.


Definition isRecvEvt := isDeqEvt.

Close Scope Q_scope.


Definition deqMesg (ev : Event): option Message :=
match eKind ev with
 | deqEvt => Some (eMesg ev)
 | _ => None
end.



Definition sentMesg (ev : Event) : option Message :=
match eKind ev with
| sendEvt _ =>  Some (eMesg ev)
| _ => None
end.

Definition deqMesgOp := (opBind deqMesg).



Definition getRecdPayload (tp : RosTopic) (ev : Event) 
  : option (topicType tp)  :=
opBind (getPayload tp) (deqMesg ev).


Definition getRecdPayloadOp (tp : RosTopic) 
  : (option Event) ->  option (topicType tp)  :=
opBind (getRecdPayload tp).


Definition getPayloadAndEv  (tp : RosTopic) (oev : option Event) 
    : option ((topicType tp) * Event)  :=
match oev with
| Some ev => match getRecdPayload tp ev with
             | Some vq => Some (vq, ev)
             | None => None
             end
| None => None
end.


Fixpoint filterPayloadsUptoIndex (tp : RosTopic) (evs : nat -> option Event) 
    (numPrevEvts : nat) : list ((topicType tp) * Event):=
match numPrevEvts with
| 0 => nil
| S numPrevEvts' => match getPayloadAndEv tp (evs numPrevEvts') with
          | Some pr => pr::(filterPayloadsUptoIndex tp evs numPrevEvts')
          | None => filterPayloadsUptoIndex tp evs numPrevEvts'
           end
end.



Coercion is_true  : bool >-> Sortclass.



Close Scope Q_scope.


(** first event is innermost, last event is outermost.
    only events earleir than m^th are elegible *)
Fixpoint prevProcessedEvents (m : nat)
  (locEvents : nat -> option Event) : list Event :=
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

Definition getDeqOutput (proc: Process Message (list Message))
  (ev : option Event) : option (list Message) :=
  opBind2 (getOutput proc) (deqMesgOp ev).

Close Scope Q_scope.

Require Export Coq.Program.Basics.

Open Scope program_scope.
  

Definition getDeqOutput2 (proc: Process Message (list Message))
  (ev : Event) : (list Message) :=
    (getOutput proc) (eMesg ev).

Local  Notation π₁ := fst.
Local  Notation π₂ := snd.

Definition minDelayForIndex (lm : list Message) (index : nat) : Q :=
  let delays := map (delay ∘ (π₂)) (firstn (S index) lm) in
  fold_right Qplus 0 delays.

Definition procOutMsgs
  (swNode : RosSwNode)
  (locEvts: nat -> option Event)
  (nd : nat) : list Message := 
    let procEvts := prevProcessedEvents nd locEvts in
    let procMsgs := map eMesg procEvts in
    let lastProc := getNewProcL (process swNode) procMsgs in
    match (locEvts nd) with
    | Some evd => (getDeqOutput2 lastProc evd)
    | None => nil
    end.

Require Import CoRN.model.metric2.Qmetric.
Open Scope mc_scope.
Definition possibleDeqSendOncePair2
  (procOutMsgs : list Message)
  (procTime : QTime)
  (timingAcc : Qpos)
  (locEvts: nat -> option Event)
  (nd ns sindex : nat) := 
  match (locEvts nd, locEvts ns) with
  | (Some evd, Some evs) =>
      match (eKind evd, eKind evs) with
      | (deqEvt, sendEvt sinf) =>
            let minDelay := (minDelayForIndex procOutMsgs (startIndex sinf)) in
              ns = (S nd) + sindex
              ∧ sindex = (startIndex sinf)
              ∧ Some (eMesg evs) = (nth_error procOutMsgs sindex)
              ∧ ball timingAcc (eTime evd + minDelay + procTime)%Q (QT2Q (eTime evs))
      | (_,_) => False
      end
  | _ => False
  end.

(* 
Our current assumption does not hold if too many messages are received too quicky.
One workaround is to increase the upper upper bound on the message delivery time
and its jitter.
Recall that time spent by a message waiting for being processed by the s/w
is included in deivery time.
*)

Definition RSwNodeSemanticsAux
  (swn : RosSwNode)
  (locEvts: nat -> option Event) :=
  let procTime := procTime swn in
  let timeAcc := timingAcc swn in
  ∀ n : nat, 
      (isSendEvtOp (locEvts n) 
       → {m : nat| {si : nat | let procMsgs := (procOutMsgs swn locEvts m) in
            possibleDeqSendOncePair2 procMsgs procTime timeAcc locEvts m n si}})
    × (isDeqEvtOp (locEvts n)
      → ∀ (ni : nat), let procMsgs:= (procOutMsgs swn locEvts n) in
        ni < length procMsgs
        → { m: nat |
              possibleDeqSendOncePair2 procMsgs procTime timeAcc locEvts n m ni}).
(** If the message handler does not output anything,
    no send event takes place *)

End EvtProps.

Close Scope Q_scope.



Section DeviceAndLoc.
(** [PhysicalEvolutionType] would typically represent how the relevant physical
    quantities like temperature, position, velocity
     changed over time *)

Context  {PhysicalEvolutionType : Type}
    `{rtopic : TopicClass RosTopic}.


(** 
A device in a CPS typicall does not measure or influence
all the physical quantities of the CPS.
So, to define a device, one has to specity its view of the physics,
typicall as a projection function, but sometimes more non-trivial.
For example, if the system's [PhysicalEvolutionType] records
a train's center's position, the proximity sensor on its
RHS end sees [rightPlatformBoundary -(trainCenterPos + trainWidth/2)]

For every device in a CPS, one must specify the type of its view ([PhysQ])
a way to extract it from the whole system's physical evolution ([PhysicalEvolutionType]).
*)

Definition DeviceView (PhysQ : Type) :=
    PhysicalEvolutionType
    ->   PhysQ.


Definition NodeSemantics  := forall {Event:Type} 
 {tdeq : DecEq Event} {_ : EventType Event},
  PhysicalEvolutionType
  -> (nat -> option Event)
  -> Type.

Definition DeviceSemantics
    {PhysQ : Type}
    (dview : DeviceView PhysQ)
    (dev : Device PhysQ)
     : NodeSemantics :=
 (fun Event tdeq evtype  penv evts => dev Event tdeq evtype (dview penv) evts).

Definition SwSemantics
    (swn : RosSwNode)
       : NodeSemantics :=
 (fun Event tdeq evtype penv evts => RSwNodeSemanticsAux  swn evts).

Record MessageDeliveryParams :=
{ expectedDelay : option QTime; maxVariation : QTime}.

Class Connectivity (RosLoc: Type) :=
{
   validTopics : RosLoc -> (@TopicInfo RosTopic);
(* TODO : make this a parementer of ReliableDelivery *)
   accDelDelay : RosLoc -> RosLoc -> Q -> Prop
}.

(* 
If in future a spec. of a network model needs an event to have more info,
just add additional fields to the [EventType] typeclass.
*)
Definition NetworkModel (RosLoc: Type) {ltop: Connectivity RosLoc} :=
  ∀ {Event : Type} {edeq : DecEq Event}
  {etype : @EventType RosTopic deq rtopic Event edeq}
  {eo : @EventOrdering RosTopic Event RosLoc deq edeq rtopic etype}, Type.

Class CPS (RosLoc: Type) 
     {rldeq : DecEq RosLoc} {ltop: Connectivity RosLoc}:=
{
(* TODO : rename to nodeSemantics *)
   locNode: RosLoc -> NodeSemantics;
   networkModel : NetworkModel RosLoc
}.


End DeviceAndLoc.




Set Implicit Arguments.
Definition PossibleSendRecvPair
  {Topic Event Loc: Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq}
  {eo : @EventOrdering Topic Event Loc tdeq edeq rtopic  etype}
  {ltop : Connectivity Loc}
  (Es  Er : Event) : Prop
 :=
   (fst (eMesg Es) = fst (eMesg Er))
   /\ (validRecvMesg (validTopics (eLoc Er)) (eMesg Er))
   /\ (validSendMesg (validTopics (eLoc Es)) (eMesg Es))
   /\ (accDelDelay  (eLoc Es) (eLoc Er) (eTime Er - eTime Es)).


Record EOReliableDelivery
  {Topic Event Loc: Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq} 
  {eo : @EventOrdering Topic Event Loc  tdeq edeq rtopic  etype}
  {ltop : Connectivity Loc}
 :=
{
    eventualDelivery: forall (Es : Event),
          isSendEvt Es
          ->  {Er: Event |
              PossibleSendRecvPair Es Er
              /\ causedBy Es Er /\ isRecvEvt Er};

    recvSend: forall (Er : Event),
          isRecvEvt Er
          ->  {Es : Event |
                  PossibleSendRecvPair Es Er
                  /\ causedBy Es Er /\ isSendEvt Es};
    noSpamRecv : forall ev, 
      isDeqEvt ev -> validRecvMesg (validTopics (eLoc ev)) (eMesg ev);
      (* In future, change above to [isEnqEvt] *)

(** [orderRespectingDelivery] also implies that a message sent by A to B will not be received twice by B.*)
    orderRespectingDelivery : ∀ evs1 evs2 evr1 evr2,
      (eLoc evs1 = eLoc evs2)
      → (eLoc evr1 = eLoc evr2) (* multicast is allowed*)
      → (eLoc evs1 ≠ eLoc evr1)
      → causedBy evs1 evr1
      → causedBy evs2 evr2
      → (eLocIndex evs1 < eLocIndex evs2
         ↔ eLocIndex evr1 < eLocIndex evr2)
}.


Section Global.

Context
  {Topic Loc PhysicalEvType: Type}
  {tdeq : DecEq Topic}
  {ldeq : DecEq Loc}
  {rtopic : @TopicClass Topic tdeq} 
  {lcon : Connectivity Loc}
  (cps : @CPS PhysicalEvType Topic tdeq rtopic  Loc ldeq lcon).

Close Scope Q_scope.

(* use a namespace (module) for better field names*)

(** 
The record below captures a possible execution of the CPS.
It has two main components : how the physical quanties evolved over time,
the message sequence diagram which captures the 
messages sent and received by the agents of the system.
It also includes proofs that the specifications of each agent hold.
*)
Record CPSExecution  := {
  physicsEvolution : PhysicalEvType;
  CPSEvent : Type;
  CPSedeq : DecEq CPSEvent;
  CPSetype : @EventType Topic tdeq rtopic CPSEvent CPSedeq;
  CPSEventOrdering : @EventOrdering Topic CPSEvent Loc tdeq CPSedeq rtopic CPSetype;
  CPSNetworkModelHolds : networkModel _ _ _ CPSEventOrdering;
  CPSAgentSpecsHold : ∀l:Loc, (locNode l) CPSEvent CPSedeq CPSetype physicsEvolution (localEvts l)
}.


End Global.

(** 
For brevity, we dont want to explicity specify arguments such as the [EventType] 
and [EventOrdering] instances when using functions such as [eLoc].
When a CPS execution is in scope, we want those instances to be automatically inferred
using Coq's typeclass inference mechanism.
This is partly achieved partly by the command below.
*)

Hint Resolve  CPSedeq CPSetype CPSEventOrdering : typeclass_instances.

(**
When considering a specific [CPSExecution] (say [cpsexec]), the user needs
to add it to the hint database for typeclass resolution using the following command
[[
Hint Resolve  cpsexec : typeclass_instances.
]]
*)