
Require Import message.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.
Require Import Psatz.
Require Import CPS.


Lemma assertTrueAuto : assert true.
Proof.
reflexivity. 
Qed.

Hint Resolve assertTrueAuto.

Section EventProps.
Context  
  {Topic Event Loc: Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq}.

Definition onlyRecvEvts (evs : nat -> option Event) : Prop :=
∀ n:nat, isDeqEvtOp (evs n).

Definition eTimeOp := 
	option_map eTime.

Lemma DeqNotSend: forall ev,
  isDeqEvt ev
  → (~ isSendEvt ev).
Proof.
  unfold isDeqEvt, isSendEvt. intros ? Hd Hc.
  destruct (eKind ev); try congruence.
Qed.


Lemma isDeqEvtImplies : forall ev,
  isDeqEvt ev -> eKind ev = deqEvt.
Proof.
  intros ev Hd.
  unfold isDeqEvt in Hd.
  destruct (eKind ev); try reflexivity; try discriminate.
Qed.

Definition getSentPayload (tp : Topic) (ev : Event) 
  : option (topicType tp)  :=
opBind (getPayload tp) (sentMesg ev).

Definition getSentPayloadOp (tp : Topic) 
  : (option Event) ->  option (topicType tp)  :=
opBind (getSentPayload tp).

Definition eTimeDef0 (oev : option Event) : QTime :=
match oev with
| Some ev => eTime ev
| None => mkQTime 0 I
end.

Definition nthEvtBefore  (evs : nat -> option Event)
  (t:  QTime) (n:nat) : bool :=
match evs n with
| Some ev => toBool (Qlt_le_dec (eTime ev) t)
| None => false
end.
  

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

Lemma SwFirstMessageIsNotASend:  ∀ (PE: Type) (swn : RosSwNode) pp evs ev,
  @SwSemantics PE _ _ _ swn _ _  _ pp evs
  → evs 0 = Some ev
  → ~ (isSendEvt ev).
Proof.
  intros ? ? ? ? ? Hrw Heq His.
  specialize (Hrw 0).
  rewrite Heq in Hrw.
  simpl in Hrw.
  apply π₁ in Hrw.
  apply Hrw in His. clear Hrw.
  destruct His as [m His]. destruct His as [si His].
  apply possibleDeqSendOncePair2_index in His.
  omega.
Qed.

Typeclasses eauto := 1.
Context 
{eo : @EventOrdering Topic Event Loc tdeq edeq rtopic etype}.


Definition locEvtIndexRW :=
(λ c a b p, proj1 (locEvtIndex a b c) p).

(** would fail if [QTime] is changed to [Time]. *)
Definition searchBound  (t:  QTime) : nat :=
  Z.to_nat (Qround.Qceiling (t/minGap)).

Definition numPrevEvts 
  (evs : nat -> option Event) (t:  QTime) : nat :=
match (search (searchBound t) (nthEvtBefore evs t)) with
| Some n => S n
| None => 0%nat
end.

Close Scope Q_scope.

Lemma searchBoundSpec:
  forall  loc  ev (qt : QTime), 
  eLoc ev = loc
  → (eTime ev < qt)%Q 
  → eLocIndex ev < (searchBound qt).
Proof.
  intros ? ? .
  remember (eLocIndex ev) as n.
  generalize dependent ev.
  induction n; intros ? ? ? Heq Hlt.
- unfold searchBound.
  destruct (eTime ev) as [? p].
  simpl in Hlt.
  apply QTimeD in p.
  assert (0<qt)%Q by lra.
  apply Q.Qlt_lt_of_nat_inject_Z.
  pose proof (minGapPos).
  apply Qlt_shift_div_l; auto.
  simpl. unfold inject_Z.
  lra.

- unfold searchBound.
  apply Q.Qlt_lt_of_nat_inject_Z.
  pose proof (minGapPos).
  apply Qlt_shift_div_l; auto.
  symmetry in Heqn.
  pose proof (localIndexDense loc (S n) ev n) as Hd.
  DestImp Hd; [| auto].
  DestImp Hd; [| auto].
  destruct Hd as [evp Hd].
  repnd.
  symmetry in Hdr.
  pose proof (eventSpacing evp ev) as Hsp.
  repnd.
  DestImp Hspr;[| congruence].
  pose proof (timeIndexConsistent evp ev) as Hti.
  apply proj1 in Hti.
  rewrite Heqn in Hti.
  rewrite <- Hdr in Hti.
  DestImp Hti;[|auto].
Typeclasses eauto :=5.
  rewrite Q.Qabs_Qminus,Qabs_pos in Hspr;
  [ |clear H Hspl Hspr; lra].
  (* remember (QT2Q (eTime evp)) as qp.
   remember (QT2Q (eTime ev)) as q. 
    lra. *)

  assert (0<=(qt-minGap))%Q as Hgt by lra.
  apply mkQTimeSnd in Hgt.
  apply IHn with (qt:=mkQTime (qt-minGap) Hgt) in Hdr; auto; 
   [|simpl; remember (QT2Q (eTime evp)) as qp; lra].
  unfold searchBound in Hdr.
  simpl in Hdr. clear Hgt.
  apply Q.Qlt_lt_of_nat_inject_Z in Hdr.
  apply (Qmult_lt_r _ _ _ H) in Hdr.
  field_simplify in Hdr; [| simpl; remember (QT2Q (eTime evp)) as qp;
     remember (QT2Q (eTime ev)) as q; lra].
  simpl in Hdr.
  rewrite  Q.Qdiv_1_r in Hdr.
  rewrite  Q.Qdiv_1_r in Hdr.
  assert (((-1 # 1) * minGap + qt) == qt - minGap)%Q 
    as Heqq by ring.
  rewrite Heqq in Hdr.
  clear Heqq.
  rewrite Q.S_Qplus.
  lra.
Qed.

  Typeclasses eauto :=1.


Lemma numPrevEvtsSpec:
  forall loc qt,
    forall ev: Event , eLoc ev = loc
    -> ((eLocIndex ev < numPrevEvts (localEvts loc) qt)%nat 
          <-> (eTime ev < qt)%Q).
Proof.
  intros ? ? ? Heq.
  unfold numPrevEvts.
  remember (search (searchBound qt) (nthEvtBefore (localEvts loc) qt))
    as sop. symmetry in Heqsop.
  destruct sop;
  split; intros Hlt; [| | omega |].
- apply searchSome in Heqsop.
  repnd.
  unfold nthEvtBefore in Heqsopl.
  remember (localEvts loc n) as evnop.
  destruct evnop as [evn|]; [| discriminate].
  destruct (Qlt_le_dec (eTime evn) qt); try discriminate;[].
  clear Heqsopl.
  assert (eLocIndex ev < n \/ eLocIndex ev = n) as Hd by omega.
  symmetry in Heqevnop.
  apply locEvtIndex in Heqevnop.
  repnd.
  Dor Hd.
  + clear Hlt.
    assert (eTime ev < eTime evn)%Q ;[| lra].
    apply timeIndexConsistent; auto.
    congruence.
  + assert (ev=evn);[| subst; congruence].
    apply indexDistinct; congruence.

- apply searchMax with (c:= eLocIndex ev) in Heqsop;
  [omega| | eapply searchBoundSpec; eauto; fail].
  unfold nthEvtBefore.
  rewrite locEvtIndexRW with (c:= ev);
    [| split; auto].
  destruct (Qlt_le_dec (eTime ev) qt); auto. simpl. remember (QT2Q (eTime ev)) as qp. lra.

- provefalse. unfold nthEvtBefore in Heqsop.
  pose proof Hlt as Hltb.
  eapply searchBoundSpec in Hlt; eauto.
  apply searchNone with (m:=eLocIndex ev) in Heqsop; auto.
  rewrite locEvtIndexRW with (c:= ev)in Heqsop;
    [| split; auto].
  destruct (Qlt_le_dec (eTime ev) qt);
  simpl in Heqsop; try discriminate.
  lra.
Qed.


Lemma evSpacIndex :  forall (ev1 ev2: Event),
    eLoc ev1 = eLoc ev2
    -> eLocIndex ev1 <  eLocIndex ev2
    -> (eTime ev1 + minGap <= eTime ev2)%Q.
Proof.
  intros  ? ?  Hl Hlt.
  pose proof (proj2 ( eventSpacing ev1 ev2) Hl) as Ht.
  apply timeIndexConsistent in Hlt.
Typeclasses eauto := 4.
  rewrite Q.Qabs_Qminus in Ht.
  remember ((QT2Q(eTime ev2))) as qt2.
  remember ((QT2Q(eTime ev1))) as qt1.
  rewrite Qabs.Qabs_pos in Ht; lra.
Qed.


Typeclasses eauto := 1.

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
Typeclasses eauto := 3.

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

Typeclasses eauto := 1.





Close Scope Q_scope.


Lemma deqSingleMessage : forall evD,
  isDeqEvt evD
  -> {m : Message |  m = eMesg evD ∧ (deqMesg evD = Some m)}.
Proof.
  intros ? Hd.
  unfold isDeqEvt in Hd.
  unfold deqMesg. destruct (eKind evD); try (inversion Hd; fail);[].
  eexists; eauto.
Defined.

Lemma sendSingleMessage : forall evD,
  isSendEvt evD
  -> {m : Message |  m = eMesg evD ∧ (sentMesg evD = Some m)}.
Proof.
  intros ? Hd.
  unfold isSendEvt in Hd.
  unfold sentMesg. destruct (eKind evD); try (inversion Hd; fail);[].
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
  inversion Heq.
Qed.

Lemma deqSingleMessage2 : forall evD m,
  Some m = deqMesg evD
  -> m = eMesg evD.
Proof.
  intros ? ? Hd. unfold deqMesg in Hd.
  destruct (eKind evD); inversion Hd.
  reflexivity.
Defined.

Lemma deqSingleMessage3 : forall evD,
  isDeqEvt evD
  -> (deqMesg evD = Some (eMesg evD)).
Proof.
  intros ? Hd.
  unfold isDeqEvt in Hd.
  unfold deqMesg. destruct (eKind evD); try (inversion Hd; fail);[].
  eexists; eauto.
Defined.

Lemma moveMapInsideSome : forall tp lm,
  opBind (getPayload tp)  (Some lm)
  = (getPayloadR tp) (fst lm).
Proof.
  intros ?. destruct lm; reflexivity.
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

Lemma getRecdPayloadSpecMsg: 
    forall tp ev tv,
      getRecdPayload tp ev = Some tv
      -> getPayload tp (eMesg ev) = Some tv.
Proof.
  intros ? ? ? Hp.
  unfold getRecdPayload in Hp.
  pose proof (deqSingleMessage ev) as Hs.
  unfold isDeqEvt.
  unfold isDeqEvt in Hs.
  unfold deqMesg in Hp, Hs.
  destruct (eKind ev); simpl in Hp; try discriminate;[].
   eauto.
Qed.

Lemma getSentPayloadSpecMsg: 
    forall tp ev tv,
      getSentPayload tp ev = Some tv
      -> getPayload tp (eMesg ev) = Some tv.
Proof.
  intros ? ? ? Hp.
  unfold getSentPayload in Hp.
  pose proof (sendSingleMessage ev) as Hs.
  unfold isSendEvt.
  unfold isSendEvt in Hs.
  unfold sentMesg in Hp, Hs.
  destruct (eKind ev); simpl in Hp; try discriminate;[].
   eauto.
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

Require Import LibTactics.
Lemma getRecdPayloadSpecMesg: forall tp ev tv,
      getRecdPayload tp ev = Some tv
      -> isDeqEvt ev ∧ π₁ (eMesg ev) = (mkMesg tp tv).
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

Lemma isDeqEvtIf : ∀ {ed}, 
    eKind ed = deqEvt
    -> isDeqEvt ed.
Proof.
  intros ? Heq.
  unfold isDeqEvt.
  destruct  (eKind ed); inversion Heq.
  reflexivity.
Qed.

Definition filterPayloadsUptoTime (tp : Topic)
  (evs : nat -> option Event) (t : QTime) : list ((topicType tp) * Event):=
filterPayloadsUptoIndex tp evs (numPrevEvts evs t).

Definition lastPayloadAndTime (tp : Topic)
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


(* Coercion is_true  : bool >-> Sortclass. *)

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


Close Scope Q_scope.

Require Export Coq.Program.Basics.

Open Scope program_scope.
  
(** semantics where all outgoing messages resulting from processing
    an event happen in a single send event (send once) *)
Definition possibleDeqSendOncePair
  (swNode : RosSwNode)
  (locEvts: nat -> option Event)
  (nd ns: nat) := 
  match (locEvts nd, locEvts ns) with
  | (Some evd, Some evs) => 
    isDeqEvt evd ∧ isSendEvt evs ∧ nd < ns (* the last bit is redundant because of time *)
    ∧ (eTime evd < eTime evs < (eTime evd) + (procTime swNode))%Q
    ∧ let procEvts := prevProcessedEvents nd locEvts in
      let procMsgs := map eMesg procEvts in
      let lastProc := getNewProcL (process swNode) procMsgs in
      (getDeqOutput lastProc (locEvts nd)) 
        = opBind2 ((λ m, m::nil)∘ eMesg) (locEvts ns)
  
  | _ => False
  end.

Local  Notation π₁ := fst.
Local  Notation π₂ := snd.


Require Import CoRN.model.metric2.Qmetric.
Open Scope mc_scope.




Definition sendInfoStartIndex (ev: Event) : option nat :=
match eKind ev with
| sendEvt sinf => Some (startIndex sinf)
| _ => None
end.


End EventProps.
(*
Definition isSendOnTopic
  (tp: RosTopic) (property : (topicType tp) -> Prop) (ev: Event) : Prop :=
isSendEvt ev /\ 
(opApPure property False (getPayload tp (eMesg ev))).
*)

Close Scope Q_scope.

Set Implicit Arguments.



Section EOProps.
Context 
  {Topic Event Loc: Type}
  {tdeq : DecEq Topic}
  {edeq : DecEq Event}
  {rtopic : @TopicClass Topic tdeq} 
  {etype : @EventType Topic tdeq rtopic Event edeq} 
  {eo : @EventOrdering Topic Event Loc tdeq edeq rtopic etype}.


Lemma  sameELoc : forall (loc: Loc) nd ns (ed es : Event),
  localEvts loc nd = Some ed 
  -> localEvts loc ns = Some es
  -> eLoc ed = eLoc es.
Proof.
  intros ? ? ? ? ? H1l H2l.
  apply locEvtIndex in H1l.
  apply locEvtIndex in H2l.
  repnd. congruence.
Qed.

Definition  NoDuplicateDelivery : Prop := ∀ (evs evr1 evr2 : Event),
      (eLoc evs ≠ eLoc evr1)
      → (eLoc evr1 = eLoc evr2) (* multicast is allowed*)
      → causedBy evs evr1
      → causedBy evs evr2
      → evr1 = evr2.


Lemma  sameLocCausal : forall (loc: Loc) nd ns (ed es : Event),
  localEvts loc nd = Some ed 
  -> localEvts loc ns = Some es
  -> nd < ns
  -> causedBy ed es.
Proof.
  intros ? ? ? ? ? H1l H2l Hlt.
  pose proof H2l as H2lb.
  eapply (sameELoc _ nd ns) in H2l; eauto.
  apply (localCausal) in H2l.
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


Section ReliableDeliveryProps.
Typeclasses eauto := 3.
Context 
  {lcon : Connectivity Loc}
   {e : @EOReliableDelivery Topic Event Loc 
   tdeq edeq rtopic etype eo lcon}.

Lemma noDuplicateDelivery : NoDuplicateDelivery.
Proof.
  unfold NoDuplicateDelivery.
  intros ? ? ? Hneq Heq H1c H2c.
  pose proof (lt_eq_lt_dec (eLocIndex evr1) (eLocIndex evr2)) as Htric.
  destruct Htric as[Htric| Htric];
    [ destruct Htric as[Htric| Htric]|].
- pose proof (orderRespectingDelivery e evs evs evr1 evr2 eq_refl Heq Hneq H1c H2c) as Hord.
  apply Hord in Htric.
  omega.
- eauto using indexDistinct.
- symmetry in Heq.
  pose proof (λ hn, orderRespectingDelivery e evs evs evr2 evr1 eq_refl Heq hn H2c H1c) as Hord.
  apply Hord in Htric;[ | congruence].
  omega.
Qed.

Typeclasses eauto := 2.
Lemma orderRespectingDeliverySR:  ∀ (evs1 evs2 evr1 evr2 : Event),
      (eLoc evs1 = eLoc evs2)
      → (eLoc evr1 = eLoc evr2)
      → (eLoc evs1 ≠ eLoc evr1)
      → causedBy evs1 evr1
      → causedBy evs2 evr2
      → eLocIndex evs1 < eLocIndex evs2
      → eLocIndex evr1 < eLocIndex evr2.
Proof.
  intros.
  rewrite <- (orderRespectingDelivery e); eauto.
Qed.

Lemma orderRespectingDeliveryRS:  ∀ evs1 evs2 evr1 evr2,
      (eLoc evs1 = eLoc evs2)
      → (eLoc evr1 = eLoc evr2)
      → (eLoc evs1 ≠ eLoc evr1)
      → causedBy evs1 evr1
      → causedBy evs2 evr2
      → eLocIndex evr1 < eLocIndex evr2
      → eLocIndex evs1 < eLocIndex evs2.
Proof.
  intros.
  rewrite (orderRespectingDelivery e); eauto.
Qed.

End ReliableDeliveryProps.

Lemma PureProcDeqSendOncePair : forall ns nd TI TO qt qac loc
    (sp : SimplePureProcess TI TO),
  let sproc := mkPureProcess (liftToMesg sp)in
  possibleDeqSendOncePair (Build_RosSwNode sproc (qt,qac)) (localEvts loc) nd ns
  -> {es : Event | {ed : Event | isDeqEvt ed × isSendEvt es
          × (nd < ns)
              × (eTime ed <eTime es < eTime ed + qt)%Q
        × localEvts loc nd = Some ed × localEvts loc ns = Some es ×
          (validRecvMesg (TI::nil,nil) (eMesg ed)
           ->  {dmp : topicType TI |  
                      fst (eMesg ed) = ((mkMesg _ dmp))
                      ∧ (mkImmMesg TO (sp dmp) ) = (eMesg es)})}}.
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
  split; [reflexivity |].
  split; [reflexivity |].
  clear  Hncrrl Hncrl Hncl.
  rename Hncrrr into Hnc.
  unfold validRecvMesg. simpl.
  intro Hsub.
  apply deqSingleMessage in Hdeq.
  clear HeqoevD.
  clear HeqoevS.
  destruct Hdeq as [dm Hdeq]. repnd.
  rewrite <- Hdeql in Hsub.
  rewrite RemoveOrFalse in Hsub.
  symmetry in Hsub.
  exists (transport Hsub (mPayload dm)).
  unfold getDeqOutput in Hnc.
  simpl in Hnc. rewrite Hdeqr in Hnc.
  simpl in Hnc.
  rewrite getNewProcLPure in Hnc.
  rewrite <- Hdeql.
  clear Hdeql Hdeqr. 
  simpl. inverts Hnc as Hnc. 
  unfold liftToMesg in Hnc. unfold getPayload in Hnc.
  destruct dm as [dm hdr].
  destruct dm as [dmt dmp].
  simpl in Hnc, Hsub.
  destruct Hsub.
  simpl. simpl in Hnc. 
  unfold mkPureProcess, mkPureHandler, getOutput in Hnc.
  simpl in Hnc.
  unfold mtopic. unfold mtopic in Hnc. simpl. 
  simpl in Hnc. split;[reflexivity|].
  destruct (eqdec dmt dmt) as [Heq| Hneq];
    [| apply False_rect; apply Hneq; reflexivity].
  inversion Hnc.
  simpl.
  pose proof (@UIPReflDeq Topic _ _ Heq) as Heqr.
  rewrite Heqr.
  simpl. reflexivity.
Qed.



Local  Notation π₁ := fst.
Local  Notation π₂ := snd.

Lemma DelayedPureProcDeqSendPair : ∀ TI TO (sp : PureProcWDelay TI TO)
    qt qac nd (pl : topicType TI) evs ,
  let sproc := mkPureProcess (delayedLift2Mesg sp) in
  let response :=  sp pl in
  let respPayLoads := (map π₂ response) in
  RSwNodeSemanticsAux (Build_RosSwNode sproc (qt,qac)) evs
  → (getRecdPayloadOp TI (evs nd) = Some pl)
  →  ∀ n: nat, 
      n < length response
      → {ev : Event | evs (S nd + n) = Some ev
            ∧ (isSendEvt ev) 
            ∧ Some (eMesg ev) 
               = nth_error
                    (map (λ p, mkDelayedMesg (π₁ p) (π₂ p)) (sp pl)) n
            ∧ ball qac
                (eTimeDef0  (evs nd)
                     + minDelayForIndex
                         (map (λ p, mkDelayedMesg (π₁ p) (π₂ p))(sp pl)) 
                         n 
                     + qt)%Q 
                (QT2Q (eTime ev))}.
Proof.
  simpl. intros ? ? ? ? ? ? ?  ? Hrs Hrcd.
  unfold RSwNodeSemanticsAux, procTime, timingAcc, compose in Hrs.
  simpl in Hrs.
  specialize (Hrs nd). apply snd in Hrs.
  unfold getRecdPayloadOp in Hrcd.
  remember ((evs nd)) as oevd.
  destruct oevd as [evd|]; inverts Hrcd as Hcrd.
  simpl in Hrs.
  assert (isDeqEvt evd) as Hdeqd by
    (eapply getRecdPayloadSpecDeq; eauto).
  specialize (Hrs Hdeqd).
  unfold procOutMsgs in Hrs.
  rewrite <- Heqoevd in Hrs.
  simpl in Hrs.
  rewrite getNewProcLPure in Hrs.
  unfold mkPureProcess, getDeqOutput2, getOutput in Hrs.
  unfold delayedLift2Mesg in Hrs.
  simpl in Hrs. apply getRecdPayloadSpecMsg in Hcrd.
  rewrite Hcrd in Hrs. simpl in Hrs.
  rewrite map_length in Hrs.
  parallelForall Hrs. rename x into si.
  parallelForall Hrs. clear x.
  destruct Hrs as [ns  Hrs].
  unfold possibleDeqSendOncePair2 in Hrs.
  rewrite <- Heqoevd in Hrs.
  remember (evs ns) as oes.
  destruct oes as [es|];[| contradiction].
  exists es.
  unfold isSendEvt.
  rewrite isDeqEvtImplies  in Hrs;[| assumption].
  destruct (eKind es); [| contradiction].
  repnd. subst ns.
  dands; auto.
  clear Hrsrrl.
  simpl. rewrite Hrsrl. assumption.
Qed.


End EOProps.

