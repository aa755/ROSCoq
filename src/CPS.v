
Require Export message.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.
Require Import Psatz.


Record SendEvtInfo := mkSendEvtInfo  {
    (* index of the corresponding enq message which trigerred this processing *)
    enqIndex : nat;
    (** [startIndex] into the list of messages output by the process
        on the message received at index [enqIndex]. In this send event,
        some message starting at that index were sent *)
    startIndex : nat
}.

(* received messages are enqued in a mailbox
    and the dequed.
    Should we add another event to mark the time when processing of an
    event finished. Now, one has to compute this from the particular
    s/w.
 *)
Inductive EventKind : Set := 
  | sendEvt (inf : SendEvtInfo) 
  | deqEvt.


Section Event.
Context  `{rtopic : TopicClass RosTopic}.

Close Scope Q_scope.


(** [Event] could just be a record type. However, over the time, we might need to
   extend it with more information. Hence, using a typeclass.
   Between different executions of the same CpS, the definition of the
   type [Event] is not supposed to change. However, different executions of a 
   CPS may correspond to different [EventOrdering], as defined below. *)
Class EventType (Event: Type) 
      (* minimum time diff between events *)
      {tdeq: DecEq Event}  := {
  eMesg : Event -> Message;
  eKind : Event -> EventKind;
  eTime : Event -> QTime;
  timeDistinct : forall (a b : Event), 
    eTime a = eTime b
    -> a = b
 }.


(** A device is a relation between how the assosiated (measured/actuated)
    physical quantity changes over time and a trace of events
    generated/consumed by the device.
    The latter is represented by the type [(nat -> option Event)].
    It will be obtained by plugging in a location in [localEvts] above.
    
    The type [(nat -> option Event)] needs to be specialized to indicate
    facts that events are of same location and have increasing timestamps
    Right now, a device property writer can assume that these hold. *)

Definition Device `{EventType Event } (PhysQ : Type ) : Type :=
                  PhysQ
                  -> (nat -> option Event)
                  -> Prop.

End Event.

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

(* these notations have to be defined again at the end of the section *)
Definition deqMesgOp := (opBind deqMesg).
(* Definition sentMesgOp := (opBind sentMesg). *)



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


Definition latestEvt (P : Event -> Prop) (ev : Event) :=
  P ev /\ (forall ev':Event, P ev' -> ((eTime ev') <= (eTime ev))%Q).

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

(* When will the next deque happen? Assume webserver with
    infinite threads. These start working as soon as a message
    comes. Therefore, no enque event.
    So, the answer is that the next deq happens
    as soon as the message gets delivered *)


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
(** If the functional process does not output anything,
    no send event takes place *)


End EvtProps.

Close Scope Q_scope.

Section DeviceAndLoc.
(** [PhysicalEnvType] would typically represent how physical
    quantities like temperature, position, velocity
     changed over time *)

Context  {PhysicalEnvEvolutionType : Type}
    `{rtopic : TopicClass RosTopic}
    `{evt : @EventType _ _ _ Event  tdeq}.




   (** When one uses a device in a CPS, they must provide
      a way to extract from the system's [PhysicalEnvType]
      a function that represents the way physical quantity
      measured/ controlled by devices changes.
      
      For example, if the system's [PhysicalEnvType] records
      a train's center's position, the proximity sensor on its
      RHS end sees [rightPlatformBoundary -(trainCenterPos + trainWidth/2)]

    *)
   
Definition DeviceView (PhysQ : Type) :=
    PhysicalEnvEvolutionType
    ->   PhysQ.


Definition NodeSemantics  :=
  PhysicalEnvEvolutionType
  -> (nat -> option Event)
  -> Type.

Definition DeviceSemantics
    {PhysQ : Type}
    (dview : DeviceView PhysQ)
    (inpDev : Device PhysQ)
     : NodeSemantics :=
 (fun penv evts => inpDev (dview penv) evts).

Definition SwSemantics
    (swn : RosSwNode)
       : NodeSemantics :=
 (fun penv evts => RSwNodeSemanticsAux  swn evts).

Record MessageDeliveryParams :=
{ expectedDelay : option QTime; maxVariation : QTime}.

Class CPS (RosLoc: Type) 
     {rldeq : DecEq RosLoc} :=
{
   locNode: RosLoc -> NodeSemantics;

   validTopics : RosLoc -> (@TopicInfo RosTopic);

   accDelDelay : RosLoc -> RosLoc -> Q -> Prop
}.


End DeviceAndLoc.

Set Implicit Arguments.


Arguments well_founded {A} P.

Class EventOrdering 
   {Topic Event Loc: Type} (minGap:Q)
  `{rtopic : TopicClass Topic} 
  `{etype : @EventType _ _ _ Event tdeq} :=
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

  (** remove this and change the type of [minGap] to [Qpos] *)
  minGapPos : (0 < minGap)%Q;

  (** While this definitely a sensible property, is it needed anywhere? *)
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

    causalWf : well_founded  causedBy

}.

Definition PossibleSendRecvPair (minGap:Q)
  {Topic Event Loc PhysicalEnvType : Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {ldeq : DecEq Loc}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq} 
  {_ : @EventOrdering Topic Event Loc minGap tdeq rtopic edeq etype}
  {rlct : @CPS PhysicalEnvType Topic Event Loc ldeq}
  (Es  Er : Event) : Prop
 :=
   (fst (eMesg Es) = fst (eMesg Er))
   /\ (validRecvMesg (validTopics (eLoc Er)) (eMesg Er))
   /\ (validSendMesg (validTopics (eLoc Es)) (eMesg Es))
   /\ (accDelDelay  (eLoc Es) (eLoc Er) (eTime Er - eTime Es)).




Record EOReliableDelivery (minGap:Q)
  {Topic Event Loc PhysicalEnvType: Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {ldeq : DecEq Loc}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq} 
  {eo : @EventOrdering Topic Event Loc minGap tdeq rtopic edeq etype}
  {rlct : @CPS PhysicalEnvType Topic Event Loc ldeq} :=
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
      (* !FIX! change above to [isEnqEvt] *)

    orderRespectingDelivery : ∀ evs1 evs2 evr1 evr2,
      (eLoc evs1 = eLoc evs2)
      → (eLoc evr1 = eLoc evr2) (* multicast is allowed*)
      → (eLoc evs1 ≠ eLoc evr1)
      → causedBy evs1 evr1
      → causedBy evs2 evr2
      → (eLocIndex evs1 < eLocIndex evs2
         ↔ eLocIndex evr1 < eLocIndex evr2)

    (* the stuff below can probably be
      derived from the stuff above *)
}.


Section Global.

Context  (minGap:Q)
  {Topic Event Loc PhysicalEvType: Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {ldeq : DecEq Loc}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq} 
  {rlct : @CPS PhysicalEvType Topic Event Loc ldeq}.

Close Scope Q_scope.


Record CPSExecution  := {
  physicsEvolution : PhysicalEvType;
  cpsEventOrdering :> @EventOrdering Topic Event Loc minGap tdeq rtopic edeq etype
}.

Definition NodeBehCorrect 
{eo : @EventOrdering Topic Event Loc minGap tdeq rtopic edeq etype}
  (physics : PhysicalEvType) (l : Loc) : Type :=
  (locNode l) physics (localEvts l).

 
Definition CPSExecutionValid (ce: CPSExecution) := 
  forall l:Loc, @NodeBehCorrect (cpsEventOrdering ce) (physicsEvolution ce) l.



End Global.