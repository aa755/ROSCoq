Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export roscore.
Require Export CoList.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.



(** received messages are enqued in a mailbox
    and the dequed *)
Inductive EventKind := 
sendEvt | enqEvt | deqEvt.


Section Event.
Context  `{rtopic : RosTopicType RosTopic}.

(** In any run, there will only be a finitely
    many events. So the collection of events
    in the entire system can be represented
    as a list. [Event] is a type
    representing all events in the system *)

Class EventType (T: Type) 
      (Loc : Type) 
      (** minimum time diff between events *)
      (minGap : Qpos) 
      {tdeq: DecEq T}  := {
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
    -> eTime a < eTime b;

  localEvts : Loc -> (nat -> option T);

  locEvtIndex : forall (l: Loc) n t,
    ((eLoc t) = l /\ (eLocIndex t) = n)
    <-> localEvts l n = Some t;

  localIndexDense : forall (l: Loc) n t (m : nat),
    ((eLoc t) = l /\ (eLocIndex t) = n)
    -> m <n 
    -> {tm : T | ((eLoc tm) = l /\ (eLocIndex tm) = m)};

    (** At any time, we can partition local events
      into a finite set of events happening before
      and ones happening after *)

  eventSpacing :  forall (e1 e2 : T),
    Cast ((eTime e1) > minGap)
    /\ (eLoc e1 = eLoc e2 -> Qabs (eTime e1 - eTime e2) <= minGap)
 }.


End Event.

Section DeviceAndLoc.
Context  `{rtopic : RosTopicType RosTopic}
  `{evt : @EventType _ _ _ Event LocT minG tdeq}.

(** A device is a relation between how the assosiated (measured/actuated)
    physical quantity changes over time and a trace of events
    generated/consumed by the device.
    The latter is represented by the type [(nat -> Event)].
    It will be obtained by plugging in a location in [localEvts] above.
    
    The type [(nat -> Event)] needs to be specialized to indicate
    facts that events are of same location and have increasing timestamps
    Right now, a device property writer can assume that these hold. *)

Definition Device (PhysQ : Type ) : Type :=
                  (Time -> PhysQ)
                  -> (nat -> option Event)
                  -> Prop.

Record RosNode : Type := { 
  topicInf : @TopicInfo  RosTopic;
  rnode : RosSwNode +  {PhysQ : Type | Device PhysQ}
}.

(** For devices, this function returns the type
    which of functions denoting
    how the associated physical quantity changes over time *)
Definition TimeValuedPhysQType  (rn : RosNode) : Type :=
match (rnode rn) with
| inl _ => unit
| inr (existT PhysQ _) => Time -> PhysQ
end.

Class RosLocType (PhysicalEnvType : Type) ( RosLoc: Type) 
     {rldeq : DecEq RosLoc} :=
{
   locNode: RosLoc -> RosNode;
   maxDeliveryDelay : RosLoc -> RosLoc -> option Time;
   (** a location type should also provide out a way
      to access the way physical quantities
      measured/ controlled by devices changes *)
   
   timeValuedEnv : (Time -> PhysicalEnvType) 
        -> forall rl, TimeValuedPhysQType (locNode rl)
}.


End DeviceAndLoc.

Set Implicit Arguments.


Section EventProps.
Context  (PhysicalEnvType : Type)
  (physics : Time -> PhysicalEnvType)
  (minGap : Qpos)
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
 `{etype : @EventType _ _ _ E LocT minGap tdeq }
  `{rlct : @RosLocType _ _ _ E PhysicalEnvType LocT ldeq}.

(*
Definition  prevEvts (l : LocT) (t :Time) : nat.
assert R as maxEvts.
apply (cf_div  t (realV _ minGap)).
simpl. destruct minGap. simpl. simpl in realVPos.
apply pos_ap_zero; trivial.
remember (Z.to_nat (proj1_sigT _ _ (overApproximate maxEvts))) as maxSearch.
Admitted.


Lemma    prevEventsIndex0 : 
    forall (l: LocT) , prevEvts l 0 =0.
Admitted.


Lemma    prevEventsIndexCorrect: 
    forall (l: LocT) (t: Time) (n : nat) , 
            match (localEvts l n) with
            | None => True
            | Some ev => 
                  (n <= prevEvts l t -> eTime ev [<=] t)
                  /\ (n > prevEvts l t -> Cast (eTime ev [>] t))
            end.
Admitted.
*)
Close Scope Q_scope.

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
    (rnode :  @RosNode  _ _ _ E) :=
    
    forall n, match (locEvents n) with
              | Some rv => validRecvMesg (topicInf rnode) (eMesg rv)
              | None => True
              end.

Definition noSpamSend 
    (locEvents : nat -> option E)
    (rnode :  @RosNode  _ _ _ E) :=    
    forall n, match (locEvents n) with
              | Some rv => validSendMesg (topicInf rnode) (eMesg rv)
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
  (locEvents : nat -> option E) : list E :=
  match len with
  | 0 => nil
  | S len' => 
      match locEvents (start + len') with
      | Some ev => 
          match (eKind ev) with
          | sendEvt => ev :: (futureSends (S start) len' locEvents)
          | deqEvt => nil (* event processing is atomic, as of now*)
          | enqEvt => (futureSends (S start) len' locEvents)
          end
      | None => nil (* this will never happen *)
       end
  end.

Definition sendsInRange  (startIncl : nat) (endIncl : nat)
  (locEvents : nat -> option E) : list Message :=
  map eMesg (futureSends startIncl (endIncl + 1 - startIncl) locEvents).

Open Scope Q_scope.

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
            exists len, let sEvts := (futureSends (eLocIndex ev) len locEvts) in
                        map eMesg sEvts = lastOutMsgs
                        /\ match (rev sEvts) with
                            | hsm :: _ => (eTime hsm <
                                                  tadd (eTime ev) 
                                                        (pTiming swNode (eMesg ev)))
                            | nil => True
                            end

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
(*
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
  forall n:nat,
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
  | Some ev  => (realV _ (eTime ev) = curTime [+] mesgTime) 
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

  let props := InpDevBehaviourCorrectAux physQ inpDev locEvents lastEvtIndex 0 in
  forall n, ConjL (initialSegment n props).

*)    
(*noSpamRecv *)

Definition DeviceBehaviourCorrect
    {Env : Type}
    (physQ : Time -> Env)
    (inpDev : Device Env)
    (locEvents : nat -> option E) : Prop :=

 inpDev physQ locEvents.




Definition NodeBehCorrect (l : LocT) : Prop.
  pose proof (timeValuedEnv physics l) as timeEnv.
  destruct (locNode l). destruct rnode0 as [rsw  Hxyxyx| PhysQ dev].
  - exact (CorrectSWNodeBehaviour rsw (localEvts l)).
  - destruct PhysQ as [PhysQ dev]. unfold TimeValuedPhysQType in timeEnv.
    simpl in timeEnv.
    exact (DeviceBehaviourCorrect timeEnv dev (localEvts l)).
Defined.

Definition AllNodeBehCorrect : Prop:= 
  forall l,  NodeBehCorrect l.


Definition PossibleSendRecvPair
  (Es  Er : E) : Prop :=
match (eKind Es, eKind Er) with
| (sendEvt, enqEvt) =>
   (eMesg Es = eMesg Er)
   /\ (validRecvMesg (topicInf (locNode (eLoc Er))) (eMesg Er))
   /\ (validSendMesg (topicInf (locNode (eLoc Es))) (eMesg Es))
   /\ (match (maxDeliveryDelay (eLoc Es) (eLoc Er)) with
      | Some td =>   (eTime Er <  tadd (eTime Es) td)
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
        -> eTime e1 < eTime e1;

    eventualDelivery: forall (Es : E), exists (Er : E),
          PossibleSendRecvPair Es Er
          /\ causedBy Es Er;

    recvSend: forall (Er : E), exists (Es : E),
          PossibleSendRecvPair Es Er
          /\ causedBy Es Er;

    corr : CorrectFIFOQueue /\ AllNodeBehCorrect;


    (** the stuff below can probably be
      derived from the stuff above *)

    causalWf : well_founded _ causedBy
    
}.
End EventProps.
