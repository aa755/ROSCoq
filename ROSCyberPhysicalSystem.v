Add LoadPath "../../../nuprl/coq".

Require Export roscore.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.
Require Import Psatz.


Record SendEvtInfo := mkSendEvtInfo  {
    (** index of the corresponding enq message which trigerred this processing *)
    enqIndex : nat;
    (** [startIndex] into the list of messages output by the process
        on the message received at index [enqIndex]. In this send event,
        some message starting at that index were sent *)
    startIndex : nat
}.

(** received messages are enqued in a mailbox
    and the dequed.
    Should we add another event to mark the time when processing of an
    event finished. Now, one has to compute this from the particular
    s/w.
 *)
Inductive EventKind : Set := 
  | sendEvt (inf : SendEvtInfo) 
  | enqEvt 
  | deqEvt (enqIndex: nat).


Section Event.
Context  `{rtopic : RosTopicType RosTopic}.

(** [Event] is a type
    representing all events in the system *)
Close Scope Q_scope.

Class EventType (T: Type) 
      (Loc : Type) 
      (** minimum time diff between events *)
    	(minGap : Q) 
      {tdeq: DecEq T}  := {
  eLoc : T ->  Loc;
  eMesg : T -> list Message;
  eKind : T -> EventKind;
  
  enQDeq1Mesg : forall t, match eKind t with
                          | enqEvt => length (eMesg t) = 1%nat
                          | deqEvt _ => length (eMesg t) = 1%nat
                          | sendEvt _ => True
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
    <-> (eTime a < eTime b)%Q;

  localEvts : Loc -> (nat -> option T);

  locEvtIndex : forall (l: Loc) n t,
    ((eLoc t) = l /\ (eLocIndex t) = n)
    <-> localEvts l n = Some t;

  localIndexDense : ∀ (l: Loc) n t (m : nat),
    ((eLoc t) = l /\ (eLocIndex t) = n)
    -> m <n 
    -> {tm : T | ((eLoc tm) = l /\ (eLocIndex tm) = m)};

    (** At any time, we can partition local events
      into a finite set of events happening before
      and ones happening after *)

  eventSpacing :  forall (e1 e2 : T),
    (eTime e1 >  minGap)%Q
    /\ (eLoc e1 = eLoc e2 
        -> minGap <= (Qabs ((eTime e1) - (eTime e2))))%Q;

  (** While this definitely a sensible property, is it needed anywhere? *)
  uniqueSendInfo :
    ∀ (si : SendEvtInfo) ev1 ev2,
      eLoc ev1 = eLoc ev2
      → eKind ev1 = sendEvt si
      → eKind ev2 = sendEvt si
      → ev1=ev2

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
                  PhysQ
                  -> (nat -> option Event)
                  -> Prop.

End Event.

Section EvtProps.

Context  
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
  `{etype : @EventType _ _ _ Event LocT minGap tdeq }.

(** would fail if [QTime] is changed to [Time].
    This should be definable, thanks to [minGap].
    if the returned value is is [n], the indices of prev events are less than
    [n]. see [numPrevEvtsCorrect]
 *)

Definition eTimeOp := 
option_map eTime.

Definition numPrevEvts : (nat -> option Event) -> QTime -> nat.
Admitted.

Close Scope Q_scope.

Lemma evSpacIndex :  forall (ev1 ev2: Event),
    eLoc ev1 = eLoc ev2
    -> eLocIndex ev1 <  eLocIndex ev2
    -> (eTime ev1 + minGap <= eTime ev2)%Q.
Proof.
  intros  ? ?  Hl Hlt.
  pose proof (proj2 ( eventSpacing ev1 ev2) Hl) as Ht.
  apply timeIndexConsistent in Hlt.
  rewrite Q.Qabs_Qminus in Ht.
  rewrite Qabs.Qabs_pos in Ht; lra.
Qed.

(** this is the spec of the above function *)
Lemma numPrevEvtsSpec:
  forall loc qt,
    forall ev: Event , eLoc ev = loc
    -> ((eLocIndex ev < numPrevEvts (localEvts loc) qt)%nat 
          <-> (eTime ev < qt)%Q).
Admitted.

Lemma numPrevEvtsEtime:
  forall (ev: Event) loc ,
    eLoc ev = loc
    -> numPrevEvts (localEvts loc) (eTime ev)
        = eLocIndex ev.
Proof.
  intros ? ?.
  remember (eLocIndex ev) as en.
  generalize dependent ev.
  induction en as [|enp  Hind]; intros ? Hin Hl.
- pose proof (numPrevEvtsSpec loc (eTime ev) ev Hl) as Hs;
  rewrite <- Hin in Hs. 
  unfold iff in Hs.
  repnd.
  destruct (numPrevEvts (localEvts loc) (eTime ev));
    [reflexivity| assert False;[| contradiction]].
  apply (Qlt_irrefl (eTime ev)).
  apply Hsl. omega.
- symmetry in Hin.
  pose proof (localIndexDense _ _ ev enp 
    (conj Hl Hin) (lt_n_Sn enp)) as Hld.
  destruct Hld as [evp Hld].
  repnd. symmetry in Hldr.
  specialize (Hind _ Hldr Hldl).
  pose proof (numPrevEvtsSpec loc (eTime ev) evp Hldl) as Hs.
  rewrite <- timeIndexConsistent in Hs.
  rewrite <- Hldr in Hs.
  apply proj2  in Hs.
  rewrite Hin in Hs.
  specialize (Hs (lt_n_Sn _)).
  unfold lt in Hs.
  apply le_lt_or_eq in Hs.
  destruct Hs as [Hs|Hs];[| auto; fail].
  assert False;[| contradiction].
  rewrite <- Hin in Hs.
  pose proof (numPrevEvtsSpec loc (eTime ev) ev Hl) as Hss.
  apply proj1 in Hss.
  apply Hss in Hs.
  apply (Qlt_irrefl (eTime ev)).
  apply Hs.
Qed.

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
  | deqEvt _ => true
  | _ => false
  end.


Definition isDeqEvtOp (ev: option Event) : bool :=
  opApPure isDeqEvt false ev.

Definition isEnqEvt (ev: Event) :Prop :=
eKind ev = enqEvt.

Definition isEnqEvtOp (ev: option Event) :Prop :=
  opApPure isEnqEvt False ev.

(** !!FIX!! this should be [isEnqEvt] *)
Definition isRecvEvt := isDeqEvt.

Close Scope Q_scope.

(** FIFO queue axiomatization *)
Fixpoint CorrectFIFOQueueUpto   (upto : nat)
    (locEvts: nat -> option Event) :  Prop * list Message :=
match upto with
| 0 => (True, nil)
| S upto' =>
    let (pr, queue) := CorrectFIFOQueueUpto upto' locEvts in
    match locEvts upto' with
    | None => (pr, queue)
    | Some ev => 
          match (eKind ev) with
          | sendEvt _ => (pr,queue)
          | enqEvt =>  (pr, enqueueAll (eMesg ev) queue)
          | deqEvt _ => 
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

Definition deqMesg (ev : Event) : option Message :=
match eKind ev with
 | deqEvt _ => head (eMesg ev)
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
  unfold deqMesg. destruct (eKind evD); try (inversion Hd; fail);[].
  destruct ((eMesg evD)); inversion XX.
  destruct l; inversion H0.
  eexists; eauto.
Defined.

Lemma deqMesgSome : forall ev sm,
    Some sm = deqMesg ev
    -> isDeqEvt ev.
Proof.
  intros ? ? Heq.
  unfold deqMesg in Heq.
  unfold isDeqEvt.
  destruct (eKind ev); auto;
  inversion Heq. reflexivity.
Qed.

Lemma deqSingleMessage2 : forall evD m,
  Some m = deqMesg evD
  -> m::nil = eMesg evD.
Proof.
  intros ? ? Hd. pose proof Hd as Hdb.
  apply deqMesgSome in Hd.
  apply deqSingleMessage in Hd.
  destruct Hd as [m' Hd].
  repnd.
  congruence.
Defined.

Definition enqMesg (ev : Event) : option Message :=
match eKind ev with
| enqEvt => head (eMesg ev)
| _ => None
end.

Definition sentMesg (ev : Event) : list Message :=
match eKind ev with
| sendEvt _ =>  (eMesg ev)
| _ => nil
end.

(* these notations have to be defined again at the end of the section *)
Definition deqMesgOp := (opBind deqMesg).
Definition enqMesgOp := (opBind enqMesg).
(* Definition sentMesgOp := (opBind sentMesg). *)


Lemma deqIsRecvEvt : forall ev sm,
    Some sm = deqMesg ev
    -> isRecvEvt ev.
Proof.
  intros ? ? Heq.
  unfold deqMesg in Heq.
  unfold isRecvEvt, isDeqEvt.
  destruct (eKind ev); auto;
  inversion Heq. reflexivity.
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

Definition getRecdPayload (tp : RosTopic) (ev : Event) 
  : option (topicType tp)  :=
opBind (getPayload tp) (deqMesg ev).
Require Import LibTactics.

Lemma getRecdPayloadSpecDeq: 
    forall tp ev tv,
      getRecdPayload tp ev = Some tv
      -> isDeqEvt ev.
Proof.
  intros ? ? ? Hp.
  unfold getRecdPayload in Hp.
  pose proof (deqSingleMessage ev) as Hs.
  unfold isDeqEvt.
  unfold isDeqEvt in Hs.
  unfold deqMesg in Hp, Hs.
  destruct (eKind ev); simpl in Hp; try discriminate;[].
  eexists; eauto.
Qed.

Lemma MsgEta: forall tp m pl,
 getPayload tp m = Some pl
  -> π₁ m = (mkMesg tp pl).
Proof.
  unfold getPayload,getPayloadR. intros ? ? ? Heq.
  destruct m as [m hdr]. destruct m as [x].
  unfold mkMesg. simpl. simpl in Heq.
  destruct (eqdec x tp);simpl in Heq; inversion Heq; subst; reflexivity.
Qed.

Lemma getRecdPayloadSpecMesg: forall tp ev tv,
      getRecdPayload tp ev = Some tv
      -> isDeqEvt ev ∧ map fst (eMesg ev) = (mkMesg tp tv)::nil.
Proof.
  unfold getRecdPayload. intros ? ? ? Heq.
  pose proof (deqMesgSome ev) as Hd.
  remember (deqMesg ev) as dm.
  destruct dm as [sm|]; [| inverts Heq; fail].
  simpl in Heq. specialize (Hd _ eq_refl).
  dands; [trivial; fail|].
  apply deqSingleMessage in Hd.
  destruct Hd as [mhd Hd].
  repnd.
  rewrite Hdr in Heqdm.
  inverts Heqdm.
  apply MsgEta in Heq.
  rewrite <- Hdl.
  simpl. rewrite Heq.
  reflexivity.
Qed.


Lemma isSendEvtIf : ∀ {ed deqIndex}, 
    eKind ed = sendEvt deqIndex
    -> isSendEvt ed.
Proof.
  intros ? ? Heq.
  unfold isSendEvt.
  destruct  (eKind ed); inversion Heq.
  reflexivity.
Qed.

Lemma isDeqEvtIf : ∀ {ed enqIndex}, 
    eKind ed = deqEvt enqIndex
    -> isDeqEvt ed.
Proof.
  intros ? ? Heq.
  unfold isDeqEvt.
  destruct  (eKind ed); inversion Heq.
  reflexivity.
Qed.

  
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

Definition filterPayloadsUptoTime (tp : RosTopic)
  (evs : nat -> option Event) (t : QTime) : list ((topicType tp) * Event):=
filterPayloadsUptoIndex tp evs (numPrevEvts evs t).

Definition lastPayloadAndTime (tp : RosTopic)
  (evs : nat -> option Event) (upto : QTime) (defPayL : (topicType tp))
    :((topicType tp) × QTime):=
hd (defPayL,mkQTime 0 I)
   (map (fun p => (fst p, eTime (snd p)))
        (filterPayloadsUptoTime tp evs upto)).

Definition latestEvt (P : Event -> Prop) (ev : Event) :=
  P ev /\ (forall ev':Event, P ev' -> ((eTime ev') <= (eTime ev))%Q).

Lemma latestEvtStr: forall  (PS P : Event -> Prop) (ev : Event),
   PS ev
   -> (forall ev, PS ev -> P ev)
   -> latestEvt P ev
   -> latestEvt PS ev.
Proof.
  intros ? ? ? Hp Him Hl.
  split; [auto;fail|].
  intros evp Hps. TrimAndLHS Hl.
  specialize (Hl evp (Him _ Hps)).
  trivial.
Qed.


Lemma filterPayloadsIndexCorr : forall tp loc (n:nat) mev lmev,
  (mev::lmev = filterPayloadsUptoIndex tp (localEvts loc) n)
  ->  let m:= fst mev in
      let ev := snd mev in
        (getRecdPayload tp ev) = Some m
         /\ eLoc ev = loc
         /\ (eLocIndex ev < n)%nat
         /\ lmev = filterPayloadsUptoIndex tp (localEvts loc) (eLocIndex ev).
Proof.
  induction n as [| np Hind]; intros ? ? Hmem; simpl in Hmem;
    [inversion Hmem; fail|].
  remember (localEvts loc np) as oev.
  simpl.
  destruct oev as [ev|];
    [|specialize (Hind _ _ Hmem); simpl in Hind; repnd; dands; auto; fail].
  unfold getPayloadAndEv in Hmem.
  remember (getRecdPayload tp ev) as osp.
  destruct osp as [sp | ];
    [|specialize (Hind _ _ Hmem); simpl in Hind; repnd; dands; auto; fail].
  inverts Hmem.
  simpl. rewrite <- Heqosp.
  symmetry in Heqoev. apply locEvtIndex in Heqoev.
  repnd. subst np.
  dands; auto.
Qed.

Lemma filterPayloadsIndexCorr2 : forall tp loc (n:nat) mev,
  member mev (filterPayloadsUptoIndex tp (localEvts loc) n)
  ->  let m:= fst mev in
      let ev := snd mev in
         (getRecdPayload tp ev) = Some m
         /\ eLoc ev = loc
         /\ (eLocIndex ev < n).
Proof.
  simpl. intros ? ? ?.
  remember (filterPayloadsUptoIndex tp (localEvts loc) n) as ll.
  generalize dependent n.
  induction ll; intros ? Hf ? Hm;[inverts Hm|].
  simpl in Hm.
  destruct Hm as [Hm|?]; [| subst];
  apply filterPayloadsIndexCorr in Hf.
- repnd. apply IHll with (mev:=mev)  in Hfrrr; auto.
  repnd. dands; auto. omega.
- repnd.  dands; auto.
Qed.

Lemma filterPayloadsTimeCorr2 : forall tp loc (t:QTime) mev,
  member mev (filterPayloadsUptoTime tp (localEvts loc) t)
  ->  let m:= fst mev in
      let ev := snd mev in
         (getRecdPayload tp ev) = Some m
         /\ eLoc ev = loc
         /\ (eTime ev < t)%Q.
Proof.
  simpl. intros ? ? ? ? Hmem.
  apply filterPayloadsIndexCorr2 in Hmem.
  repnd.
  dands; auto.
  apply numPrevEvtsSpec in Hmemrr; trivial.
Qed.

Lemma filterPayloadsIndexSorted : forall tp loc (n:nat) mev lmev,
  (mev::lmev = filterPayloadsUptoIndex tp (localEvts loc) n)
  ->  let m:= fst mev in
      let ev := snd mev in
      forall mp evp,  
        member (mp, evp) lmev
        -> (eLocIndex evp) < (eLocIndex ev).
Proof.
  simpl. intros ? ? ? ? ? Heq ? ? Hmem; simpl in Hmem. simpl.
  apply filterPayloadsIndexCorr in Heq.
  repnd. subst lmev.
  apply filterPayloadsIndexCorr2 in Hmem.
  simpl in Hmem.
  repnd. trivial.
Qed.

Lemma filterPayloadsTimeSorted : forall tp loc (t:QTime) mev lmev,
  (mev::lmev = filterPayloadsUptoTime tp (localEvts loc) t)
  ->  let m:= fst mev in
      let ev := snd mev in
      forall mp evp,  
        member (mp, evp) lmev
        -> ((eTime evp) < (eTime ev))%Q.
Proof.
  simpl. intros ? ? ? ? ? Heq ? ? Hm.
  eapply filterPayloadsIndexSorted in Heq; eauto.
  apply timeIndexConsistent.
  trivial.
Qed.

Lemma filterPayloadsTimeCorr : forall tp loc (t:QTime) mev lmev,
  (mev::lmev = filterPayloadsUptoTime tp (localEvts loc) t)
  ->  let m:= fst mev in
      let ev := snd mev in
        (getRecdPayload tp ev) = Some m
         /\ eLoc ev = loc
         /\ (eTime ev < t)%Q
         /\ lmev = filterPayloadsUptoTime tp (localEvts loc) (eTime ev).
Proof.
  simpl. intros ? ? ? ? ? Heq.
  unfold filterPayloadsUptoTime in Heq.
  apply filterPayloadsIndexCorr in  Heq.
  repnd. dands; auto.
- pose proof (numPrevEvtsSpec loc t (snd mev) Heqrl) as Hnm. simpl in Hnm.
  apply Hnm.
  trivial.
- unfold filterPayloadsUptoTime.
  rewrite numPrevEvtsEtime; auto.
Qed.

Lemma locNoneIndex : forall loc n,
    None = localEvts loc n
    -> forall ev,
        eLoc ev = loc
        -> eLocIndex ev < n.
Proof.
  intros ? ?  Hn ? Hl.
  apply not_ge.
  intros Hc.
  unfold ge in Hc.
  apply le_lt_or_eq in Hc.
  destruct Hc as [Hc|Hc].
- eapply localIndexDense in Hc; eauto.
  destruct Hc as [evn Hc].
  apply locEvtIndex in Hc.
  rewrite Hc in Hn.
  discriminate.
- symmetry in Hc. 
  rewrite (proj1 (locEvtIndex _ _ _) (conj Hl Hc)) in Hn.
  discriminate.
Qed.

Definition locEvtIndexRW :=
(λ c a b p, proj1 (locEvtIndex a b c) p).

  
Lemma filterPayloadsIndexComp : forall tp loc (n:nat) pl ev,
  (getRecdPayload tp ev) = Some pl
  -> eLoc ev = loc
  -> (eLocIndex ev < n)
  -> member (pl,ev) (filterPayloadsUptoIndex tp (localEvts loc) n).
Proof.
  induction n as [| np Hind]; intros ? ? Hp Heq Hl;
    [omega|].
  simpl.
  remember (localEvts loc np) as oev.
  destruct oev as [evnp|];
    [|specialize (Hind _ _ Hp); simpl in Hind; apply Hind; auto;
                      eapply locNoneIndex; eauto; fail].
  unfold getPayloadAndEv.
  remember (getRecdPayload tp evnp) as osp.
  destruct osp as [sp | ];
    [|specialize (Hind _ _ Hp); simpl in Hind].
- pose proof (eq_nat_dec (eLocIndex ev) np) as Hd.
  destruct Hd as [Hd|Hd];[right|left].
  + symmetry in Heqoev. apply locEvtIndex in Heqoev.
    repnd. subst np. eapply indexDistinct in Hd; eauto;[|congruence].
    subst. rewrite Hp in Heqosp. inverts Heqosp. reflexivity.
  + assert (eLocIndex ev <  np) by omega.
    apply Hind; auto.
- apply Hind; trivial. unfold lt in Hl. apply le_lt_or_eq in Hl.
  clear Hind. destruct Hl as [Hl|Hl];[omega|].
  inverts Hl.
  symmetry in Heqoev. apply locEvtIndex in Heqoev.
  repnd.
  eapply indexDistinct in Heqoevr; eauto;[|congruence].
  subst. rewrite Hp in Heqosp. discriminate.
Qed.
  
Lemma filterPayloadsTimeComp : forall tp loc (t: QTime) ev pl,
  (getRecdPayload tp ev) = Some pl
  -> eLoc ev = loc
  -> (eTime ev < t)%Q
  -> member (pl,ev) (filterPayloadsUptoTime tp (localEvts loc) t).
Proof.
  intros ? ? ? ? ? Hev Hl Hi.
  apply filterPayloadsIndexComp; auto.
  apply numPrevEvtsSpec; auto.
Qed.


Coercion is_true  : bool >-> Sortclass.

Lemma filterPayloadsTimeLatest : forall tp loc (t:QTime) mev ll,
  (mev::ll = filterPayloadsUptoTime tp (localEvts loc) t)
  -> latestEvt (fun ev => notNone (getRecdPayload tp ev)
                            /\ eLoc ev = loc
                            /\ (eTime ev < t)%Q) (snd mev).
Proof.
  intros ? ? ? ? ? Heq.
  pose proof (filterPayloadsTimeSorted _ _ _ _ _ Heq) as Hs.
  pose proof Heq as Heqb.
  simpl in Hs. apply filterPayloadsTimeCorr in Heq.
  repnd. split; dands; auto;[rewrite Heql; reflexivity|].
  intros evp Hp.
  repnd. 
  pose proof (filterPayloadsTimeComp tp loc t evp) as Hc.
  destruct (getRecdPayload tp evp) as [plp|]; inversion Hpl.
  specialize (Hc _ eq_refl Hprl Hprr).
  rewrite <- Heqb in Hc.
  simpl in Hc.
  destruct Hc as [Hc | Hc]; subst; eauto 3 with *.
Qed.


(*
Lemma filterPayloadsSpec : forall tp loc m lm  t,
   (m::lm = filterPayloadsUptoTime tp (localEvts loc) t)
  -> sig (fun ev=> (eMesg ev) = ((mkMesg _ (fst m))::nil)
                /\ latestEvt (fun ev' => eTime ev' < t) ev
                /\ eTime ev = (snd m)
                /\ lm = filterPayloadsUptoTime tp (localEvts loc) (snd m)
                /\ eLoc ev = loc
                /\ isDeqEvt ev).
Proof.
  intros ? ? ? ? ? Heq.
  
*)
Close Scope Q_scope.


Lemma queueContents : forall  (locEvts: nat -> option Event)
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
  (locEvents : nat -> option Event) : list Event :=
  match m with
  | 0 => nil
  | S m' => (match locEvents m' with
              | Some ev => match (eKind ev) with
                            | deqEvt _ => (ev)::nil
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

  
(** assuming all outgoing messages resulting from processing
    an event happen in a single send event (send once) *)
Definition possibleDeqSendOncePair
  (swNode : RosSwNode)
  (locEvts: nat -> option Event)
  (nd ns: nat) := 
  match (locEvts nd, locEvts ns) with
  | (Some evd, Some evs) => 
    isDeqEvt evd ∧ isSendEvt evs ∧ nd < ns (** the last bit is redundant because of time *)
    ∧ (forall n: nat, nd < n < ns -> isEnqEvtOp (locEvts n))
    ∧ (eTime evd < eTime evs < (eTime evd) + (procTime swNode))%Q
    ∧ let procEvts := prevProcessedEvents nd locEvts in
      let procMsgs := flat_map eMesg procEvts in
      let lastProc := getNewProcL (process swNode) procMsgs in
      (getDeqOutput lastProc (locEvts nd)) = opBind2 eMesg (locEvts ns)
  
  | _ => False
  end.

Definition getDeqOutput2 (proc: Process Message (list Message))
  (ev : Event) : (list Message) :=
   flat_map (getOutput proc) (eMesg ev).

Require Export Coq.Program.Basics.

Open Scope program_scope.

Definition minDelayForIndex (lm : list Message) (index : nat) : Q :=
  let delays := map (delay ∘ (π₂)) (firstn index lm) in
  fold_right Qplus 0 delays.

Definition procOutMsgs
  (swNode : RosSwNode)
  (locEvts: nat -> option Event)
  (nd : nat) : list Message := 
    let procEvts := prevProcessedEvents nd locEvts in
    let procMsgs := flat_map eMesg procEvts in
    let lastProc := getNewProcL (process swNode) procMsgs in
    match (locEvts nd) with
    | Some evd => (getDeqOutput2 lastProc evd)
    | None => nil
    end.

Require Import CoRN.model.metric2.Qmetric.
Open Scope mc_scope.
(** assuming all outgoing messages resulting from processing
    an event happen in a single send event (send once) *)
Definition possibleDeqSendOncePair2
  (procOutMsgs : list Message)
  (procTime : QTime)
  (timingAcc : Qpos)
  (locEvts: nat -> option Event)
  (nd ns sindex : nat) := 
  match (locEvts nd, locEvts ns) with
  | (Some evd, Some evs) =>
      match (eKind evd, eKind evs) with
      | (deqEvt enqIndex , sendEvt sinf) =>
            let minDelay := (minDelayForIndex procOutMsgs (startIndex sinf)) in
              ns = (S nd) + sindex
              ∧ sindex = (startIndex sinf)
              ∧ isPrefixOf (eMesg evs) (skipn sindex procOutMsgs)
              ∧ ball timingAcc (eTime evd + minDelay + procTime)%Q (QT2Q (eTime evs))
              ∧ length (eMesg evs) =1
      | (_,_) => False
      end
  | _ => False
  end.

Definition sendInfoStartIndex (ev: Event) : option nat :=
match eKind ev with
| sendEvt sinf => Some (startIndex sinf)
| _ => None
end.


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
(*
Definition isSendOnTopic
  (tp: RosTopic) (property : (topicType tp) -> Prop) (ev: Event) : Prop :=
isSendEvt ev /\ 
(opApPure property False (getPayload tp (eMesg ev))).
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

Definition RSwSemantics
    (swn : RosSwNode)
       : NodeSemantics :=
 (fun penv evts => RSwNodeSemanticsAux  swn evts).

Class RosLocType (RosLoc: Type) 
     {rldeq : DecEq RosLoc} :=
{
   locNode: RosLoc -> NodeSemantics;

   validTopics : RosLoc -> (@TopicInfo RosTopic);

   maxDeliveryDelay : RosLoc -> RosLoc -> option QTime
}.

Lemma possibleDeqSendOncePair2_index : ∀ proc pt tacc evs m n si,
  possibleDeqSendOncePair2 proc pt tacc evs m n si
  → m < n.
Proof.
  intros ? ? ? ? ? ? ?  Hp.
  unfold possibleDeqSendOncePair2 in Hp.
  destruct (evs m), (evs n); simpl in Hp; try contradiction.
  destruct (eKind e), (eKind e0); try contradiction.
  repnd. omega.
Qed.

Lemma SwFirstMessageIsNotASend:  ∀ (swn : RosSwNode) pp evs ev,
  RSwSemantics swn pp evs
  → evs 0 = Some ev
  → ~ (isSendEvt ev).
Proof.
  intros ? ? ? ? Hrw Heq His.
  specialize (Hrw 0).
  rewrite Heq in Hrw.
  simpl in Hrw.
  apply π₁ in Hrw.
  apply Hrw in His. clear Hrw.
  destruct His as [m His]. destruct His as [si His].
  apply possibleDeqSendOncePair2_index in His.
  omega.
Qed.


End DeviceAndLoc.

Set Implicit Arguments.


Section Global.
Context  (PhysicalEnvType : Type)
  (physics : PhysicalEnvType)
  (minGap : Q)
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
 `{etype : @EventType _ _ _ Event LocT minGap tdeq }
  `{rlct : @RosLocType PhysicalEnvType RosTopic Event LocT ldeq}.

Close Scope Q_scope.

Definition NodeBehCorrect (l : LocT) : Type :=
  (locNode l) physics (localEvts l).

Definition AllNodeBehCorrect : Type:= 
  forall l,  NodeBehCorrect l.

Definition PossibleSendRecvPair
  (Es  Er : Event) : Prop :=
   (map fst (eMesg Es) = map fst (eMesg Er))
   /\ (validRecvMesg (validTopics (eLoc Er)) (eMesg Er))
   /\ (validSendMesg (validTopics (eLoc Es)) (eMesg Es))
   /\ (match (maxDeliveryDelay  (eLoc Es) (eLoc Er)) with
      | Some td => (eTime Es < eTime Er <  eTime Es + td)%Q
      | None => True (* None stands for infinity *)
      end).
    


Require Import Coq.Relations.Relation_Definitions.

Record PossibleEventOrder  := {
    causedBy : Event -> Event -> Prop;

    (* causalTrans : transitive _ causedBy; *)

    localCausal : forall (e1 e2 : Event),
        (eLoc e1) = (eLoc e2)
        -> (causedBy e1 e2 <-> eLocIndex e1 < eLocIndex e2);

    globalCausal : forall (e1 e2 : Event),
        causedBy e1 e2
        -> (eTime e1 < eTime e2)%Q;

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

    corrFIFO : CorrectFIFOQueue;
    corrNodes : AllNodeBehCorrect;


    noSpamRecv : forall ev, 
      isDeqEvt ev -> validRecvMesg (validTopics (eLoc ev)) (eMesg ev);
      (* !FIX! change above to [isEnqEvt] *)

    noDuplicateDelivery : ∀ evs evr1 evr2,
      (eLoc evs ≠ eLoc evr1)
      → (eLoc evr1 = eLoc evr2) (* multicast is allowed*)
      → causedBy evs evr1
      → causedBy evs evr2
      → evr1 = evr2;
      
    (** the stuff below can probably be
      derived from the stuff above *)
    causalWf : well_founded _ causedBy

}.


Lemma PureProcDeqSendOncePair : forall ns nd TI TO qt qac loc
    (sp : SimplePureProcess TI TO),
  let sproc := mkPureProcess (liftToMesg sp)in
  possibleDeqSendOncePair (Build_RosSwNode sproc (qt,qac)) (localEvts loc) nd ns
  -> {es : Event | {ed : Event | isDeqEvt ed × isSendEvt es
          × (nd < ns)
            × (∀ n : nat, (nd < n) ∧ (n < ns) → isEnqEvtOp (localEvts loc n))
              × (eTime ed <eTime es < eTime ed + qt)%Q
        × localEvts loc nd = Some ed × localEvts loc ns = Some es ×
          (validRecvMesg (TI::nil,nil) (eMesg ed)
           ->  {dmp : topicType TI |  
                      map fst (eMesg ed) = ((mkMesg _ dmp)::nil)
                      ∧ (mkImmMesg TO (sp dmp) )::nil = (eMesg es)})}}.
Proof.
  intros ? ? ? ? ? ? ? ?. simpl. intro Hnc.
  unfold possibleDeqSendOncePair in Hnc.
  remember (localEvts loc nd) as oevD.
  destruct oevD as [evD |]; [| contradiction].
  remember (localEvts loc ns) as oevS.
  destruct oevS as [evS |]; [| contradiction].
  destruct Hnc as [Hdeq  Hnc].
  exists evS. exists evD. unfold procTime, compose in Hnc. simpl in Hnc.
  remember (eTime evD < eTime evS ∧ eTime evS < eTime evD + qt)%Q as dontSplit.
  repnd.
  split; [trivial |].
  split; [trivial |].
  split; [trivial |].
  split; [trivial |].
  split; [trivial |].
  split; [reflexivity |].
  split; [reflexivity |].
  clear Hncrrrl Hncrrl Hncrl Hncl.
  rename Hncrrrr into Hnc.
  unfold validRecvMesg. simpl.
  intro Hsub.
  apply deqSingleMessage in Hdeq.
  clear HeqoevD.
  clear HeqoevS.
  destruct Hdeq as [dm Hdeq]. repnd.
  rewrite <- Hdeql in Hsub.
  specialize (Hsub _ (or_introl  eq_refl)).
  rewrite RemoveOrFalse in Hsub.
  symmetry in Hsub.
  exists (transport Hsub (mPayload dm)).
  unfold getDeqOutput in Hnc.
  simpl in Hnc. rewrite Hdeqr in Hnc.
  simpl in Hnc.
  rewrite getNewProcLPure in Hnc.
  rewrite <- Hdeql.
  clear Hdeql Hdeqr. 
  simpl. inversion Hnc as [Hncc]. clear Hnc Hncc.
  unfold liftToMesg. unfold getPayload.
  destruct dm as [dm hdr].
  destruct dm as [dmt dmp].
  simpl in Hsub.  destruct Hsub.
  simpl. unfold mtopic. simpl. split;[reflexivity|].
  destruct (eqdec dmt dmt) as [Heq| Hneq];
    [| apply False_rect; apply Hneq; reflexivity].
  simpl.
  pose proof (@UIPReflDeq RosTopic _ _ Heq) as Heqr.
  rewrite Heqr.
  simpl. reflexivity.
Qed.

Lemma  sameELoc : forall loc nd ns ed es,
  localEvts loc nd = Some ed 
  -> localEvts loc ns = Some es
  -> eLoc ed = eLoc es.
Proof.
  intros ? ? ? ? ? H1l H2l.
  apply locEvtIndex in H1l.
  apply locEvtIndex in H2l.
  repnd. congruence.
Qed.

Lemma  sameLocCausal : forall eo loc nd ns ed es,
  localEvts loc nd = Some ed 
  -> localEvts loc ns = Some es
  -> nd < ns
  -> causedBy eo ed es.
Proof.
  intros ? ? ? ? ? ? H1l H2l Hlt.
  pose proof H2l as H2lb.
  eapply (sameELoc _ nd ns) in H2l; eauto.
  apply (localCausal eo) in H2l.
  apply H2l.
  apply locEvtIndex in H1l.
  apply locEvtIndex in H2lb.
  repnd. congruence.
Qed.

    

Definition holdsUptoNextEvent (prp : Time -> ℝ -> Prop)
  (phys : Time -> ℝ)
  (evs : nat -> option Event) (n: nat) :=
  let otn := eTimeOp (evs n) in
  let otsn := eTimeOp (evs (S n)) in
  match otn with
  |  Some tn => 
      let Tintvl := nextInterval tn otsn in
      forall t: Time,  (Tintvl) t -> prp t (phys t)
  | None => True
  end.

End Global.
