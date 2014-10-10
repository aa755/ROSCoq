Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export roscore.
Require Export CoList.

(** received messages are enqued in a mailbox
    and the dequed *)
Inductive EventKind := 
sendEvt | enqEvt | deqEvt.


Section EventLoc.
Context  `{rtopic : RosTopicType RosTopic}.


(** In any run, there will only be a finitely
    many events. So the collection of events
    in the entire system can be represented
    as a list. [Event] is a type
    representing all events in the system *)

Class EventType (T: Type) 
      (Loc : Type) 
      {tdeq: DecEq T} := {
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
    -> {tm : T | ((eLoc tm) = l /\ (eLocIndex tm) = m)};

    (** At any time, we can partition local events
      into a finite set of events happening before
      and ones happening after *)

  prevEvts : Loc -> Time -> nat;


   prevEventsIndexCorrect: 
    forall (l: Loc) (t: Time) (n : nat) , 
            match (localEvts l n) with
            | None => True
            | Some ev => 
                  (n <= prevEvts l t -> eTime ev [<=] t)
                  /\ (n > prevEvts l t -> Cast (eTime ev [>] t))
            end
 }.


Class RosLocType ( RosLoc: Type) {deq : DecEq RosLoc} :=
{
   locNode: RosLoc -> RosNode;
   maxDeliveryDelay : RosLoc -> RosLoc -> option Time;
   (** a location type should also provide out a way
      to access the way physical quantities
      measured/ controlled by devices changes *)
    
   timeValuedEnv : forall rl, TimeValuedEnvType (locNode rl)
    
}.

End EventLoc.


Set Implicit Arguments.


Section EventProps.
Context  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
 `{etype : @EventType _ _ _ E LocT tdeq }
  `{rlct : @RosLocType _ _ _ LocT ldeq}.


(** FIFO queue axiomatization *)
Fixpoint CorrectFIFOQueueUpto   (upto : nat)
    (locEvts: nat -> option E) :  Prop * list Message :=
match upto with
| 0 => (True, nil)
| S upto' =>
    let (pr, queue) := CorrectFIFOQueueUpto upto' locEvts in
    match locEvts upto' with
    | None => (pr, queue)
    | Some ev => 
          match (eKind ev) with
          | sendEvt => (pr,queue)
          | enqEvt =>  (pr, enqueue (eMesg ev) queue)
          | deqEvt => 
              let (el, newQueue) := dequeue queue in
              match el with
              | None => (False, queue)
              | Some mesg => (pr /\ mesg = (eMesg ev), newQueue)
               end
          end
    end
end.


Definition CorrectFIFOQueue    :  Prop :=
forall (l: LocT)
 (upto : nat), fst (CorrectFIFOQueueUpto upto (localEvts l)).

(** A node only receives meeages from subscribed topics *)

Definition noSpamRecv 
    (locEvents : nat -> option E)
    (rnode :  RosNode) :=
    
    forall n, match (locEvents n) with
              | Some rv => validRecvMesg rnode (eMesg rv)
              | None => True
              end.

Definition noSpamSend 
    (locEvents : nat -> option E)
    (rnode :  RosNode) :=    
    forall n, match (locEvents n) with
              | Some rv => validSendMesg rnode (eMesg rv)
              | None => True
              end.


(** Some properties about events at a particular location. In the
    next Coq Section, we formalize the interlocation properties. *)

(** first event is innermost, last event is outermost *)
Fixpoint prevProcessedEvents (m : nat)
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


Fixpoint futureSends (start : nat) (len : nat)
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

Definition sendsInRange  (startIncl : nat) (endIncl : nat)
  (locEvents : nat -> option E) : list Message :=
  futureSends startIncl (endIncl + 1 - startIncl) locEvents.

Definition CorrectSWNodeBehaviour 
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

(** What does it mean for a physical quantity
    to be controlled by an output device.
    
    [uptoTime] only makes sense if it is later than
    the timestamp of the last event
 *)

Fixpoint OutDevBehaviourCorrectUpto 
    {Env : Type}
    (physQ : Time -> Env)
    (outDev : RosOutDevNode Env)
    (processedEvts: list E)
    (uptoTime : Time) :=
  match processedEvts with
  | nil => (fst (odev outDev)) _ (restrictTill physQ uptoTime)
  | last :: rest =>  
      let recUptoTime := (eTime last) in
      let timeDiff := tdiff uptoTime recUptoTime in
      let recProp := OutDevBehaviourCorrectUpto physQ outDev rest recUptoTime in
      let restMsgs := map eMesg rest in
      let outdBh := getRosOutDevBhv outDev restMsgs in
      recProp /\ outdBh timeDiff 
            (fastFwdAndRestrict physQ recUptoTime uptoTime)
      (* physQ needs to be advanced *)
  end.

  

Definition OutDevBehaviourCorrect 
    {Env : Type}
    (physQ : Time -> Env)
    (outDev : RosOutDevNode Env)
    (locEvents : nat -> option E)
    (lastEvtIndex : Time -> nat)
     :=
  forall (t : Time),
    let lastIndex := lastEvtIndex t in
    let prevProcEvents :=  prevProcessedEvents lastIndex locEvents in
    OutDevBehaviourCorrectUpto physQ outDev prevProcEvents t.

Definition noMessagesAfter 
    (locEvents : nat -> option E)
    (lastEvtIndex : Time -> nat)
    (t : Time) : Prop :=
    
  let tIndex := lastEvtIndex t in
  forall n,
     n > tIndex
     -> locEvents n = None.

Definition nextMessageAtTime 
    (locEvents : nat -> option E)
    (lastEvtIndex : Time -> nat)
    (curTime : Time)
    (mesgTime : Time)
    (m : Message) : Prop :=
    
  let tIndex := lastEvtIndex curTime in
  match locEvents tIndex with
  | None => False
  | Some ev  => (eTime ev = tadd curTime mesgTime) 
                /\ (eMesg ev = m)
  end.

CoFixpoint InpDevBehaviourCorrectAux 
    {Env : Type}
    (physQ : Time -> Env)
    (inpDev : RosInpDevNode Env)
    (locEvents : nat -> option E)
    (lastEvtIndex : Time -> nat)
    (startTime : Time) : CoList Prop :=

  let indev := getIDev (idev inpDev) in
  match (indev (fastFwd physQ startTime)) with
  | inl _ => 
      ccons (noMessagesAfter 
                  locEvents 
                  lastEvtIndex 
                  startTime)
            (@cnil Prop)
  | inr ((mesg, timeSent), newIdev) => 
      ccons (nextMessageAtTime 
                  locEvents 
                  lastEvtIndex 
                  startTime 
                  timeSent 
                  (makeTopicMesg mesg))
            (InpDevBehaviourCorrectAux 
                  physQ 
                  ( substIDev inpDev newIdev )
                  locEvents 
                  lastEvtIndex 
                  timeSent)
  end.

Definition InpDevBehaviourCorrect
  {Env : Type}
  (physQ : Time -> Env)
  (inpDev : RosInpDevNode Env)
  (locEvents : nat -> option E)
  (lastEvtIndex : Time -> nat) :=

  let props := InpDevBehaviourCorrectAux physQ inpDev locEvents lastEvtIndex t0 in
  forall n, ConjL (initialSegment n props).
    

Definition NodeBehCorrect (l : LocT) : Prop.
  pose proof (timeValuedEnv l) as timeEnv.
  destruct (locNode l).
  - exact (CorrectSWNodeBehaviour r (localEvts l)).
  - exact (InpDevBehaviourCorrect timeEnv r (localEvts l) (prevEvts l)).
  - exact (OutDevBehaviourCorrect timeEnv r (localEvts l) (prevEvts l)).
Defined.

Definition AllNodeBehCorrect : Prop:= 
  forall l, NodeBehCorrect l.

Definition PossibleSendRecvPair
  (Es  Er : E) : Prop :=
match (eKind Es, eKind Er) with
| (sendEvt, enqEvt) =>
   (eMesg Es = eMesg Er)
   /\ (validRecvMesg (locNode (eLoc Er)) (eMesg Er))
   /\ (validSendMesg (locNode (eLoc Es)) (eMesg Es))
   /\ (match (maxDeliveryDelay (eLoc Es) (eLoc Er)) with
      | Some td =>  Cast (eTime Er [<]  tadd (eTime Es) td)
      | None => True
      end )
    
| _ => False
end.


Record PossibleEventOrder  := {
    causedBy : E -> E -> Prop;
    localCausal : forall (e1 e2 : E),
        (eLoc e1) = (eLoc e2)
        -> (causedBy e1 e2 <-> eLocIndex e1 < eLocIndex e1);

    globalCausal : forall (e1 e2 : E),
        causedBy e1 e2
        -> eTime e1 [<] eTime e1;

    (** the stuff below can probably be
      derived from the stuff above *)

    causalWf : well_founded _ causedBy;
    
    eventualDelivery: forall (Es : E), exists (Er : E),
    PossibleSendRecvPair Es Er
    /\ causedBy Es Er
    
}.
End EventProps.
