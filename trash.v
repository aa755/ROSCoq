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


(** this is a correct proof; only temporarily wrong *)
Lemma velMessages:
  forall n : nat,
     match getVelFromMsg (motorEvents n) with
     | Some v => v = speed \/ v = (0-speed)
     | None => True
     end.
Proof.
  intros n.
  unfold motorEvents.
  unfold getVelFromMsg.
  unfold getVelFromEv.
  (** the message of this deque event must have come
      from a prior enque event as evEnq*)
  pose proof (corrFIFO eo) as Hfifo.
  pose proof (deqEnq Hfifo BASEMOTOR n) as Henq.
  unfold deqMesgOp in Henq.
  unfold opBind.
  unfold opBind in Henq.
  remember (localEvts BASEMOTOR n)  as oev.
  destruct oev as [ ev| ]; [| auto; fail].
  remember (deqMesg ev)  as om.
  destruct om as [ sm| ]; [| auto; fail].
  destruct Henq as [evEnq Henq].
  clear Hfifo.
  (** someone must have sent this message
      which is contained in the receive (enque)
      event evEnq. let the sent message
      be [sm] and the corresponding event be [es] *)
  pose proof (recvSend eo evEnq) as Hrecv.
  repnd.
  destruct Hrecv as [es Hrecv];
    [unfold isRecvEvt; rewrite Henqrrl; auto |].
  TrimAndRHS Hrecv.
  unfold PossibleSendRecvPair in Hrecv.
  rewrite Henqrrl in Hrecv.
  rewrite Henqrrr in Hrecv.
  rewrite <- Henqrl in Hrecv.
  clear Henqrrl Henqrl Henqrrr.
  remember (eKind es) as eks.
  destruct eks; try contradiction;[].
  simpl in Hrecv.
  repnd. clear Hrecvrrr.
  (** since [BASEMOTOR] only receives on [MOTOR]
      topic, the message [sm] must have that topic *)
  unfold validRecvMesg in Hrecvrl.
  simpl in Hrecvrl.
  unfold validSendMesg in Hrecvrrl.
  destruct Hrecvrl as [Hmt | ?];[| contradiction].
  rewrite Hrecvl in Hrecvrrl.
  rewrite <- Hmt in Hrecvrrl.
  remember (eLoc es) as sloc.
  (** Only [SWCONTROLLER] sends on that topic *)
  destruct sloc; simpl in Hrecvrrl;
    try contradiction;
    inversion Hrecvrrl; 
    try discriminate;
    try contradiction;[].
  clear H Hrecvrrl.
  apply swControllerMessages in Heqeks;
    [| trivial].
  rewrite <- Hrecvl. trivial.
Qed.


(** A node only receives messeages from subscribed topics *)
(*
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

*)


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
                        | hsm :: _ => 
                                (eTime hsm <
                                         (eTime ev) +
                                              (pTiming swNode (eMesg ev)))
                        | nil => True
                        end

        | sendEvt => 
          match procEvts with
          | nil => False
          | last :: _ =>
    (** NOT REQD; DERIVABLE*) In (eMesg ev) lastOutMsgs /\
              length (sendsInRange (eLocIndex last)  evIndex locEvts)
                 <= length lastOutMsgs 
          end

        | enqEvt => True (* messages are always welcome. When modelling a finite sized mailbox,this may no longer be true *)
      end
  end.


Definition DeviceBehaviourCorrect
    {Env : Type}
    (physQ : Time -> Env)
    (inpDev : Device Env)
    (locEvents : nat -> option EV) : Prop :=

 inpDev physQ locEvents.
