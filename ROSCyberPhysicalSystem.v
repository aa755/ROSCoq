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
  eMesg : T -> list Message;
  eKind : T -> EventKind;
  
  enQDeq1Mesg : forall t, match eKind t with
                          | enqEvt => length (eMesg t) = 1%nat
                          | deqEvt => length (eMesg t) = 1%nat
                          | sendEvt => True
                          end;

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


(** A device is a relation between how the assosiated (measured/actuated)
    physical quantity changes over time and a trace of events
    generated/consumed by the device.
    The latter is represented by the type [(nat -> Event)].
    It will be obtained by plugging in a location in [localEvts] above.
    
    The type [(nat -> Event)] needs to be specialized to indicate
    facts that events are of same location and have increasing timestamps
    Right now, a device property writer can assume that these hold. *)

Definition Device `{EventType Event } (PhysQ : Type ) : Type :=
                  (Time -> PhysQ)
                  -> (nat -> option Event)
                  -> Prop.

End Event.

Section EvtProps.

Context  
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
 `{etype : @EventType _ _ _ EV LocT minGap tdeq }.

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

Definition isSendEvtOp (ev: option EV) :Prop :=
  opApPure isSendEvt False ev.



Definition isDeqEvt (ev: EV) :Prop :=
match (eKind ev) with
| deqEvt => True
| _ => False
end.



Definition isDeqEvtOp (ev: option EV) :Prop :=
  opApPure isDeqEvt False ev.

Definition isEnqEvt (ev: EV) :Prop :=
match (eKind ev) with
| enqEvt => True 
| _ => False
end.

Definition isEnqEvtOp (ev: option EV) :Prop :=
  opApPure isEnqEvt False ev.

(** !!FIX!! this should be [isEnqEvt] *)
Definition isRecvEvt := isDeqEvt.

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
          | enqEvt =>  (pr, enqueueAll (eMesg ev) queue)
          | deqEvt => 
              let (el, newQueue) := dequeue queue in
              match el with
              | None => (False, queue)
              | Some mesg => (pr /\ (mesg::nil) = (eMesg ev), newQueue)
               end
          end
    end
end.


Definition CorrectFIFOQueue    :  Prop :=
forall (l: LocT)
 (upto : nat), fst (CorrectFIFOQueueUpto upto (localEvts l)).

Definition deqMesg (ev : EV) : option Message :=
match eKind ev with
 | deqEvt => head (eMesg ev)
(** BTW, [(eMesg ev)] is supposed to be a singletop *)
 | _ => None
end.

Lemma deqSingleMessage : forall evD,
  isDeqEvt evD
  -> {m : Message | m::nil = eMesg evD /\ (deqMesg evD = Some m)}.
Proof.
  intros ? Hd.
  pose proof (enQDeq1Mesg evD) as XX.
  unfold isDeqEvt in Hd.
  unfold deqMesg. 
  destruct (eKind evD) ;try contradiction.
  destruct ((eMesg evD)); inversion XX.
  destruct l; inversion H0.
  eexists; eauto.
Defined.

Definition enqMesg (ev : EV) : option Message :=
match eKind ev with
| enqEvt => head (eMesg ev)
| _ => None
end.

Definition sentMesg (ev : EV) : list Message :=
match eKind ev with
| sendEvt =>  (eMesg ev)
| _ => nil
end.

(* these notations have to be defined again at the end of the section *)
Definition deqMesgOp := (opBind deqMesg).
Definition enqMesgOp := (opBind enqMesg).
(* Definition sentMesgOp := (opBind sentMesg). *)

Lemma deqMesgSome : forall ev sm,
    Some sm = deqMesg ev
    -> eKind ev = deqEvt.
Proof.
  intros ? ? Heq.
  unfold deqMesg in Heq.
  destruct (eKind ev); auto;
  inversion Heq.
Qed.

Lemma deqIsRecvEvt : forall ev sm,
    Some sm = deqMesg ev
    -> isRecvEvt ev.
Proof.
  intros ? ? Heq.
  unfold deqMesg in Heq.
  unfold isRecvEvt, isDeqEvt.
  destruct (eKind ev); auto;
  inversion Heq.
Qed.





Lemma evEnqHead : forall ev m, 
    enqEvt = eKind ev
    -> In m (eMesg ev)
    -> Some m = head (eMesg ev).
Proof.
  intros ? ? Heq Hin.
  pose proof (enQDeq1Mesg ev) as XX.
  rewrite <- Heq in XX.
  eapply length1In in XX; eauto.
  rewrite <- XX.
  simpl.
  reflexivity.
Qed.



Lemma queueContents : forall  (locEvts: nat -> option EV)
     (upto : nat),
   let (prp, queue) := CorrectFIFOQueueUpto upto locEvts  in
   prp ->
   forall m, In m queue -> exists n,
   n< upto /\ (Some m = enqMesgOp (locEvts n)).
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
    unfold enqueue, enqueueAll in Hin.
    simpl in Hin. apply in_app_or in Hin.
    destruct Hin as [Hin| Hin].
    + exists upto'. rewrite <- Heqlev.
      simpl. unfold enqMesg. rewrite <- Heqevk. split; auto; try omega.
      eapply evEnqHead; eauto.
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
    match deqMesgOp (localEvts l deqIndex) with
    | None => True
    | Some m => ∃ evEnq,(eLocIndex evEnq) < deqIndex ∧
              (m::nil = eMesg evEnq) ∧ eKind evEnq = enqEvt
              /\ eLoc evEnq = l
     end.
Proof.
 intros Hc l dn. unfold deqMesgOp. specialize (Hc l).
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
  unfold deqMesg. destruct (eKind ev); try tauto;[].
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
  destruct Heqoev as [? Heqq]. simpl in Heq. unfold enqMesg in Heq.
  pose proof (enQDeq1Mesg ev) as XX.  
  destruct (eKind ev);  inversion Heq as [Heqm]; 
  clear Heq. split; auto;[rewrite  Heqq; trivial|].
  split; auto.
  destruct (eMesg ev); simpl in XX; inversion XX.
  destruct l1; inversion H1.
  simpl in Heqm. inversion Heqm. reflexivity.
Qed.


(** first event is innermost, last event is outermost.
    only events earleir than m^th are elegible *)
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

Definition getDeqOutput (proc: Process Message (list Message))
  (ev : option EV) : option (list Message) :=
  opBind2 (getOutput proc) (deqMesgOp ev).

Open Scope Q_scope.

  
(** assuming all outgoing messages resulting from processing
    an event happen in a single send event (send once) *)
Definition possibleDeqSendOncePair
  (swNode : RosSwNode)
  (locEvts: nat -> option EV)
  (nd ns: nat) := 
  match (locEvts nd, locEvts ns) with
  | (Some evd, Some evs) => 
    isDeqEvt evd ∧ isSendEvt evs ∧ nd < ns
    ∧ (forall n: nat, nd < n < ns -> isEnqEvtOp (locEvts n))
    ∧ (eTime evs <(eTime evd) + (pTiming swNode))
    ∧ let procEvts := prevProcessedEvents nd locEvts in
      let procMsgs := flat_map eMesg procEvts in
      let lastProc := getNewProcL (process swNode) procMsgs in
      (getDeqOutput lastProc (locEvts nd)) = opBind2 eMesg (locEvts ns)
  
  | _ => False
  end.

Definition RSwNodeSemanticsAux
  (swn : RosSwNode)
  (locEvts: nat -> option EV) :=
  ∀ n : nat, 
      (isSendEvtOp (locEvts n) 
          -> ∃ m: nat, possibleDeqSendOncePair swn locEvts m n)
    ∧ (isDeqEvtOp (locEvts n) 
          -> ∃ m: nat, possibleDeqSendOncePair swn locEvts n m).




End EvtProps.
(*
Definition isSendOnTopic
  (tp: RosTopic) (property : (topicType tp) -> Prop) (ev: EV) : Prop :=
isSendEvt ev /\ 
(opApPure property False (getPayLoad tp (eMesg ev))).
*)

Close Scope Q_scope.

Section DeviceAndLoc.
(** [PhysicalEnvType] would typically represent how physical
    quantities like temperature, position, velocity
     changed over time *)

Context  {PhysicalEnvEvolutionType : Type}
    `{rtopic : RosTopicType RosTopic}
    `{evt : @EventType _ _ _ Event LocT minG tdeq}.




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
    ->  (Time -> PhysQ).


Definition NodeSemantics  :=
  PhysicalEnvEvolutionType
  -> (nat -> option Event)
  -> Prop.

Definition DeviceSemantics
    {PhysQ : Type}
    (dview : DeviceView PhysQ)
    (inpDev : Device PhysQ)
     : NodeSemantics :=
 (fun penv evts => inpDev (dview penv) evts).

Definition RSwSemantics
    (swn : RosSwNode)
       : NodeSemantics :=
 (fun penv evts => RSwNodeSemanticsAux swn evts).

Class RosLocType (RosLoc: Type) 
     {rldeq : DecEq RosLoc} :=
{
   locNode: RosLoc -> NodeSemantics;

   validTopics : RosLoc -> (@TopicInfo RosTopic);

   maxDeliveryDelay : RosLoc -> RosLoc -> option QTime
}.


End DeviceAndLoc.

Set Implicit Arguments.


Section Global.
Context  (PhysicalEnvType : Type)
  (physics : PhysicalEnvType)
  (minGap : Qpos)
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
 `{etype : @EventType _ _ _ EV LocT minGap tdeq }
  `{rlct : @RosLocType PhysicalEnvType RosTopic EV LocT ldeq}.

Open Scope Q_scope.

Definition NodeBehCorrect (l : LocT) : Prop :=
  (locNode l) physics (localEvts l).

Definition AllNodeBehCorrect : Prop:= 
  forall l,  NodeBehCorrect l.

Definition PossibleSendRecvPair
  (Es  Er : EV) : Prop :=
   (eMesg Es = eMesg Er)
   /\ (validRecvMesg (validTopics (eLoc Er)) (eMesg Er))
   /\ (validSendMesg (validTopics (eLoc Es)) (eMesg Es))
   /\ (match (maxDeliveryDelay  (eLoc Es) (eLoc Er)) with
      | Some td => (eTime Es < eTime Er <  eTime Es + td)
      | None => True (* None stands for infinity *)
      end).
    


Require Import Coq.Relations.Relation_Definitions.

Record PossibleEventOrder  := {
    causedBy : EV -> EV -> Prop;

    (* causalTrans : transitive _ causedBy; *)

    localCausal : forall (e1 e2 : EV),
        (eLoc e1) = (eLoc e2)
        -> (causedBy e1 e2 <-> eLocIndex e1 < eLocIndex e1);

    globalCausal : forall (e1 e2 : EV),
        causedBy e1 e2
        -> eTime e1 < eTime e2;

    eventualDelivery: forall (Es : EV),
          isSendEvt Es
          ->  sig (fun Er : EV =>
              PossibleSendRecvPair Es Er
              /\ causedBy Es Er /\ isRecvEvt Er);

    recvSend: forall (Er : EV),
          isRecvEvt Er
          ->  sig (fun Es : EV => 
                  PossibleSendRecvPair Es Er
                  /\ causedBy Es Er /\ isSendEvt Es);

    corrFIFO : CorrectFIFOQueue;
    corrNodes : AllNodeBehCorrect;

    (** the stuff below can probably be
      derived from the stuff above *)

    causalWf : well_founded _ causedBy;

    noSpamRecv : forall ev, 
      isDeqEvt ev -> validRecvMesg (validTopics (eLoc ev)) (eMesg ev)
      (** !FIX! change above to [isEnqEvt] *)
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

End Global.
