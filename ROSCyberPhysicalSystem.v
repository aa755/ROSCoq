Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Add LoadPath "../../../nuprl/coq".

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

(** [Event] is a type
    representing all events in the system *)

Class EventType (T: Type) 
      (Loc : Type) 
      (** minimum time diff between events *)
      (minGap : Qpos) 
      {tdeq: DecEq T}  := {
  eLoc : T ->  Loc;
  eMesg : T -> Message;
  eKind : T -> EventKind;
  eTime : T -> QTime;
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
    (eTime e1 >  minGap)
    /\ (eLoc e1 = eLoc e2 
        -> Qabs ((eTime e1) - (eTime e2)) <=  minGap)
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

   maxDeliveryDelay : RosLoc -> RosLoc -> option QTime;
   (** a location type should also provide out a way
      to access the way physical quantities
      measured/ controlled by devices changes *)
   
   timeValuedEnv : PhysicalEnvType
        -> forall rl, TimeValuedPhysQType (locNode rl)
}.


End DeviceAndLoc.

Set Implicit Arguments.


Section EventProps.
Context  (PhysicalEnvType : Type)
  (physics : PhysicalEnvType)
  (minGap : Qpos)
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
 `{etype : @EventType _ _ _ EV LocT minGap tdeq }
  `{rlct : @RosLocType _ _ _ EV PhysicalEnvType LocT ldeq}.


(** would fail if [QTime] is changed to [Time].
    This should be definable, thanks to [minGap] *)
Definition lastEvtIndex : LocT -> QTime -> nat.
Admitted.

Definition eTimeOp := 
option_map eTime.


Lemma lastEvtIndexCorrect :
forall t loc m,
  match eTimeOp (localEvts loc m) with
  | Some tm =>
    (m <= lastEvtIndex loc t
         -> tm <= t)
    /\ (m > lastEvtIndex loc t
         -> tm > t)
  | None => True
  end.
Admitted.


Definition isSendEvt (ev: EV) :Prop :=
match (eKind ev) with
| sendEvt => True
| _ => False
end.

Definition isRecvEvt (ev: EV) :Prop :=
match (eKind ev) with
| enqEvt => True
| deqEvt => True
| _ => False
end.


Definition isSendOnTopic
  (tp: RosTopic) (property : (topicType tp) -> Prop) (ev: EV) : Prop :=
isSendEvt ev /\ 
(opApPure property False (getPayLoad tp (eMesg ev))).

Close Scope Q_scope.

(** FIFO queue axiomatization *)
Fixpoint CorrectFIFOQueueUpto   (upto : nat)
    (locEvts: nat -> option EV) :  Prop * list Message :=
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

Definition deqMesg (oev : option EV) : option Message :=
match oev with
| Some ev => match eKind ev with
             | deqEvt => Some (eMesg ev)
             | _ => None
             end
| None => None
end.

Definition enqMesg (oev : option EV) : option Message :=
match oev with
| Some ev => match eKind ev with
             | enqEvt => Some (eMesg ev)
             | _ => None
             end
| None => None
end.

Require Export Coq.Unicode.Utf8.

Ltac parallelExist Hyp :=
      match type of Hyp with
      | exists _ : ?A, _   =>
            match goal with
            [ |- exists _ : A, _] =>
              let xx := fresh "x" in
              destruct Hyp as [xx Hyp]; exists xx
             end
      end.

Ltac parallelForall Hyp :=
      match type of Hyp with
      | forall _ : ?A, _   =>
            match goal with
            [ |- forall _ : A, _] =>
              let xx := fresh "x" in
              intro xx; specialize (Hyp xx)
             end
      end.

Ltac Parallel Hyp := 
  repeat progress (parallelForall Hyp || parallelExist Hyp).

Lemma queueContents : forall  (locEvts: nat -> option EV)
     (upto : nat),
   let (prp, queue) := CorrectFIFOQueueUpto upto locEvts  in
   prp ->
   forall m, In m queue -> exists n,
   n< upto /\ (Some m = enqMesg (locEvts n)).
Proof.
  induction upto as [| upto' Hind];
  [simpl; tauto| ].
  simpl.
  destruct (CorrectFIFOQueueUpto upto' locEvts)
    as [prp queue].
  remember (locEvts upto') as lev.
  destruct lev as [ev|]; auto;  
    [| Parallel Hind; destruct Hind; split; trivial; omega].
  remember (eKind ev) as evk.
  destruct evk; 
    [Parallel Hind; destruct Hind; split; trivial; omega | |].
  - parallelForall Hind. intros m Hin.
    unfold enqueue.
    simpl in Hin. destruct Hin as [Hin| Hin].
    + exists upto'. rewrite <- Heqlev.
      simpl. rewrite <- Heqevk. split; auto; try omega.
      symmetry in Hin. rewrite Hin. reflexivity.
    + apply Hind in Hin.
      Parallel Hin; destruct Hin; split; trivial; omega.
  - unfold dequeue. remember (rev queue) as revq.
    destruct revq as [| revh revt]; intro Hf;
        [contradiction|].
    destruct Hf as [Hfp H99]. specialize (Hind Hfp).
    clear H99. parallelForall Hind.
    rewrite in_rev in Hind.
    rewrite <- Heqrevq in Hind.
    simpl in Hind.
    intro Hin. rewrite <- in_rev  in Hin.
    specialize (Hind (or_intror Hin)).
    Parallel Hind; destruct Hind; split; trivial; omega.
Qed.

Lemma deqEnq : CorrectFIFOQueue
  -> ∀ (l: LocT) (deqIndex : nat),
    match deqMesg (localEvts l deqIndex) with
    | None => True
    | Some m => ∃ evEnq,(eLocIndex evEnq) < deqIndex ∧
              (m = eMesg evEnq) /\ eKind evEnq = enqEvt
              /\ eLoc evEnq = l
     end.
Proof.
 intros Hc l dn. specialize (Hc l).
 destruct dn.
- specialize (Hc 1).
  simpl in Hc.
  destruct (localEvts l 0) as [ev|] ;auto.
  unfold deqMesg. simpl.
  destruct (eKind ev); simpl in Hc; tauto.
- specialize (Hc (S (S dn))). 
  remember (S dn) as sdn.
  simpl in Hc.
  pose proof  (queueContents (localEvts l) sdn) as Hdq.
  destruct  (CorrectFIFOQueueUpto sdn (localEvts l))
      as [prp que].
  destruct (localEvts l sdn) as [ev|]; simpl;[|tauto].
  destruct (eKind ev); try tauto;[].
  pose proof (dequeueIn que) as Hqin.
  destruct (dequeue que) as [oqm  ].
  destruct oqm;simpl in Hc; [| contradiction].
  destruct Hc as [Hcp Heq]. rewrite <- Heq.
  specialize (Hdq Hcp m Hqin). clear Hqin.
  clear Heq.
  destruct Hdq as [n Hdq]. clear ev.
  remember (localEvts l n) as oev.
  destruct Hdq as [Hlt Heq].
  unfold enqMesg in Heq.
  destruct oev as [ev |];[| inversion Heq; fail].
  exists ev.
  symmetry in Heqoev.
  apply locEvtIndex in Heqoev.
  destruct Heqoev as [? Heqq].
  destruct (eKind ev); inversion Heq as [Heqm]; 
  clear Heq. split; auto.
  rewrite  Heqq.
  trivial.
Qed.

(** A node only receives meeages from subscribed topics *)

Definition noSpamRecv 
    (locEvents : nat -> option EV)
    (rnode :  @RosNode  _ _ _ EV) :=
    
    forall n, match (locEvents n) with
              | Some rv => validRecvMesg (topicInf rnode) (eMesg rv)
              | None => True
              end.

Definition noSpamSend 
    (locEvents : nat -> option EV)
    (rnode :  @RosNode  _ _ _ EV) :=    
    forall n, match (locEvents n) with
              | Some rv => validSendMesg (topicInf rnode) (eMesg rv)
              | None => True
              end.


(** Some properties about events at a particular location. In the
    next Coq Section, we formalize the interlocation properties. *)

(** first event is innermost, last event is outermost *)
Fixpoint prevProcessedEvents (m : nat)
  (locEvents : nat -> option EV) : list EV :=
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
  (locEvents : nat -> option EV) : list EV :=
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
  (locEvents : nat -> option EV) : list Message :=
  map eMesg (futureSends startIncl (endIncl + 1 - startIncl) locEvents).

Open Scope Q_scope.

Definition CorrectSWNodeBehaviour 
    (swNode : RosSwNode)
    (locEvts: nat -> option EV) : Prop :=

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
                                                   (eTime ev) +
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

  
(*noSpamRecv *)

Definition DeviceBehaviourCorrect
    {Env : Type}
    (physQ : Time -> Env)
    (inpDev : Device Env)
    (locEvents : nat -> option EV) : Prop :=

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
  (Es  Er : EV) : Prop :=
match (eKind Es, eKind Er) with
| (sendEvt, enqEvt) =>
   (eMesg Es = eMesg Er)
   /\ (validRecvMesg (topicInf (locNode (eLoc Er))) (eMesg Er))
   /\ (validSendMesg (topicInf (locNode (eLoc Es))) (eMesg Es))
   /\ (match (maxDeliveryDelay (eLoc Es) (eLoc Er)) with
      | Some td => (eTime Er <  eTime Es + td)
      | None => True
      end)
| _ => False
end.


Record PossibleEventOrder  := {
    causedBy : EV -> EV -> Prop;

    localCausal : forall (e1 e2 : EV),
        (eLoc e1) = (eLoc e2)
        -> (causedBy e1 e2 <-> eLocIndex e1 < eLocIndex e1);

    globalCausal : forall (e1 e2 : EV),
        causedBy e1 e2
        -> eTime e1 < eTime e1;

    eventualDelivery: forall (Es : EV), exists (Er : EV),
          PossibleSendRecvPair Es Er
          /\ causedBy Es Er;

    recvSend: forall (Er : EV), exists (Es : EV),
          PossibleSendRecvPair Es Er
          /\ causedBy Es Er;

    corrFIFO : CorrectFIFOQueue;
    corrNodes : AllNodeBehCorrect;

    (** the stuff below can probably be
      derived from the stuff above *)

    causalWf : well_founded _ causedBy
    
}.



Definition holdsUptoNextEvent (prp : Time -> R -> Prop)
  (phys : Time -> R)
  (evs : nat -> option EV) (n: nat) :=
  let otn := eTimeOp (evs n) in
  let otsn := eTimeOp (evs (S n)) in
  match otn with
  |  Some tn => 
      let Tintvl := nextInterval tn otsn in
      forall t: Time,  (Tintvl) t -> prp t (phys t)
  | None => True
  end.

End EventProps.
