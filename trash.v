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


(*
Class RosMesgType (T : Type) {unm: UniqueNames T} := {
    payLoadType : T -> Type
}.
  {unm : UniqueNames MT}
  {rmt : RosMesgType MT}
    masterAndName : RT -> TCP * string;
    rtInj : InjectiveFun masterAndName;
  {deqtcp : DecEq TCP}
  {tcpad : TCPAddressType TCP} 

Class TCPAddressType (T : Type) {deq : DecEq T}:= {
}.

*)


(*
Definition SimpleSwProc (inT outT : RosTopic) : Type :=
Process (topicType inT) (list (topicType outT)).

Definition SSimpleSwProc (inT outT : RosTopic) : Type :=
Process (topicType inT) (topicType outT).

Add LoadPath "../../../nuprl/coq".
Require Import UsefulTypes.

CoFixpoint makeSuperSimple {inT outT : RosTopic}
  (sswp : SSimpleSwProc inT outT) : SimpleSwProc inT outT.
  constructor. intro inp.
  apply sswp in inp. repnd.
  split; [ | exact [inp]; fail].
  apply makeSuperSimple.
  trivial.
Defined.


Coercion  makeSuperSimple : SSimpleSwProc >-> SimpleSwProc.
*)


(*
Inductive RosNode : Type := 
| rsw :> RosSwNode -> RosNode
| rhi :> forall {Env : Type}, 
        RosInpDevNode Env -> RosNode
| rho :> forall {Env : Type}, 
        RosOutDevNode Env -> RosNode.

Open Scope list_scope.

Definition SubscribeTopics  (rn : RosNode) : list RosTopic
  :=
match rn with
| rsw rsn => subscribeTopics rsn
| rhi _ _ => nil
| rho _ rout =>  cons (inpTopic rout) nil
end.

Definition PublishTopics  (rn : RosNode) : list RosTopic
  :=
match rn with
| rsw rsn => publishTopics rsn
| rhi _ rinp => cons (outTopic rinp) nil
| rho _ _ =>   nil
end.

Definition TimeValuedEnvType  (rn : RosNode) : Type
  :=
match rn with
| rsw rsn => unit
| rhi Env _ => Time -> Env
| rho Env _ => Time -> Env
end.



*)


(*
Definition mkSimplePureRosProc {InTopic OutTopic} 
  (f : SimplePureProcess InTopic OutTopic) 
    : Process Message (list Message) :=
*)
  
(** There is no code to extract for devices
    These are here to model environment *)

Record RosInpDevNode (Env : Type) :=
{
  (*  IDnodeName : string; *)
    outTopic : RosTopic; 
    idev :> InpDev Env  (topicType outTopic)
}.


Definition substIDev {Env : Type} (rid : RosInpDevNode Env)
  (newd : InpDev Env ((topicType (outTopic rid))))
  : RosInpDevNode Env :=
Build_RosInpDevNode 
                    (outTopic rid)
                    newd.


Record RosOutDevNode (Env : Type) :=
{
    (* ODMasterAddress : TCPAddress;
    ODnodeName : string; *)
    inpTopic : RosTopic;
    odev :> OutDev Env ((topicType inpTopic))
}.


  
(** Implementing this will need simplification of topic definitions.
  We need decidable equality on topics, which is not currently true.
  Also, one could have 2 topics with same string name and different
  payload types

 *)





  
Definition getRosOutDevBhv  {Env : Type}
    (p: RosOutDevNode Env )
    (allInputs : list Message)  : OutDevBehaviour Env :=
    let filterMsgs := filterMegsByTopic allInputs (inpTopic p) in
    match filterMsgs with
    | nil => fst (odev p)
    | last :: rest => getLastOutput (snd (odev p)) rest last
    end.

Lemma RHSSafe : forall t: QTime,  (centerPosAtTime tstate t) [<=] Z2R 95.
Proof.
  intros.
  pose proof (less_cotransitive_unfolded _ (Z2R 94) (Z2R 95)) as Hdi.
  lapply Hdi; [clear Hdi; intro Hdi
                |apply inj_Q_less; unfold inject_Z; simpl; lra; fail].
  match goal with
  [|- ?l [<=] ?r] => specialize (Hdi l)
  end.
  destruct Hdi;[|apply less_leEq].
  assert False;[| contradiction].
Abort.
(** While this method works, a better one is also constructive *)


Lemma velocityMessagesEv : forall m t,
  member m (velocityMessages t)
  -> sig (fun ev=> (eMesg ev) = ((mkMesg MOTOR (fst m))::nil)
                /\ eTime ev < t
                /\ eTime ev = (snd m)
                /\ eLoc ev = BASEMOTOR
                /\ isDeqEvt ev).
Admitted.


(** not relevant for code generation, 
    only relevant for reasoning *)

Section Dev.

Variable Env : Type.
  
(** Output devices receive messages and
    affect their environment. Examples are
    heating devices, motors in mobile robots
    like iCreate
    
    In our model,
    an output device receives a message and outputs
    a property about how future environment evolves.
    Note that the device can use the previous history of
    inputs.

    For example, when a roomba icreate receives
    a message with a request to go along X axis with
    speed 1m/s , the output property could be
    that the robots physical speed somewhere between
    0.9m/s and 1.1 m/s until a new message arrives
 *)
Open Scope type_scope.

Record OutDevBehaviour := {
  allowedBhv :> forall (t:RTime), (RInInterval (clcr [0] t) -> Env) -> Prop

    (* ; extendTime : forall (t1 t2 :Time)
            (ev1 : RInInterval (clcr [0] t1) -> Env) ,
            t1 [<] t2
            -> allowedBhv t1 ev1
            -> {ev2 : RInInterval (clcr [0] t2) -> Env | allowedBhv t2 ev2} *)
}.

Definition OutDev (Inp : Type) :=
  OutDevBehaviour * Process Inp OutDevBehaviour.

Definition MemoryLessOutDev (Inp : Type) :=
  OutDevBehaviour * (Inp -> OutDevBehaviour).
Close Scope type_scope.

CoFixpoint makeOutDevAux {Inp: Type} 
  (m: Inp -> OutDevBehaviour) 
    : Process Inp OutDevBehaviour :=
   buildP (fun inp : Inp => (makeOutDevAux  m,  m inp)).

Definition makeOutDev {Inp: Type} 
  (m: MemoryLessOutDev Inp) 
    : OutDev  Inp :=
  (fst m,  makeOutDevAux (snd m)).

Definition getOutDevBhv  {In : Type}
    (p: OutDev In )
    (allInputs : list In)  : OutDevBehaviour :=
    match allInputs with
    | nil => fst p
    | last :: rest => getLastOutput (snd p) rest last
    end.

Coercion makeOutDev : MemoryLessOutDev >-> OutDev.


(** An input device observes the environment over time
    and may emit messages.
    In the following model, it is a function which
    when given how environment evolved,
    either never outputs a message ([unit] case)
    our outputs a triple indicating the output message,
    time of output and a new device (possibly storing some state)

    Time is relative to the previous emitted message.
    If no message was emitted yet, time is relative to
    the instant the device (driver) was turned on.

    The reason why [InpDev] cannot be modeled
    by a software node is because unlike
    software nodes, input devices can emit
    messages even when they did not receive
    any input. Maybe we can generalize software
    nodes to do that. 
*)
CoInductive InpDev (Out : Type) :=
maybeSendMesg : 
      ((Time -> Env) 
        -> (unit + (Out * Time * InpDev Out)))
        -> InpDev Out.

(** Input devices may receive message as instructions.
    This model is not expressive enough to capture that.
    
    Howver, that is not too bad. In ROS, sensors like
    kinect continuously emit and there is no control data.
 *)

Definition getIDev {Out : Type} (idv : InpDev Out ) :
((Time -> Env) -> (unit + (Out * Time * InpDev Out)))
  :=
match idv with
maybeSendMesg mmm => mmm
end.

End Dev.


(*
CoInductive StateFulProcess (In State Out : Type) :=
buildSP : (In -> State -> ((StateFulProcess In State Out)* Out))
          -> StateFulProcess In State Out.

CoFixpoint fromSFProcess {In State Out : Type} (initState : State)
  (sfp : StateFulProcess In State Out)
   : Process In Out.
constructor. intro inp.
destruct sfp.
pose proof (p inp initState) as Hsfs.
destruct Hsfs; split; [| trivial]. clear p.
eauto.
Defined.

Coercion  fromSFProcess : StateFulProcess >-> Process.
*)

Lemma restrictTill {A} (f : Time -> A) 
    (right : Time) : (RInInterval (clcr [0] right)) -> A.
  intro rint.
  destruct rint.
  apply f. exists realV0.
  unfold iprop.
  unfold iprop in realVPos0.
  destruct realVPos0.
  trivial.
Defined.

Lemma fastFwd {A} (f : Time -> A) 
    (duration : Time) : Time  -> A.
  intro rint.
  destruct rint.
  apply f. exists (realV0 [+] duration).
  destruct duration. simpl.
  unfold iprop.
  unfold iprop in realVPos0.
  unfold iprop in realVPos1.
  eauto with *.
Defined.
