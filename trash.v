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


Lemma TimeDiffOprBnd : ∀ (opr : QTime),
  let t0 : QTime := MotorEventsNthTime 0 (decAuto (0<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 1 (decAuto (1<4)%nat I) in
 (Qabs.Qabs
        (opr * (t1 - t0) -
         opr *
         (Qabs.Qabs (approximate (polarTheta targetPos) anglePrec) *
          / rotspeed)) <= opr * ((1 + 1) * (sendTimeAcc + delivDelayVar)))%Q.
Proof.
  intros ? ? ?. pose proof MotorEv01Gap as Hg.
  simpl in Hg.
  fold t0 t1 in Hg.
  apply Q.Qmult_le_compat_l with (z:= Qabs.Qabs opr) in Hg;
      [|apply Qabs.Qabs_nonneg].
  rewrite <- Qabs.Qabs_Qmult in Hg. idtac.
  revert Hg.
  unfoldMC.
  intros Hg.
  rewrite foldQminus in Hg.
  rewrite  QmultOverQminusL in Hg.
  rewrite foldQminus in Hg.
  unfold CanonicalNotations.norm, NormSpace_instance_Q in Hg.
  revert Hg.
  unfoldMC.
  intros Hg. 
  rewrite QabsTime in Hg.
  trivial.
Qed.

(*
Definition UIP_refl := ∀ (U:Type) (x:U) (p:x = x), p = eq_refl.
Definition VoidNat_Ext := ∀ (f g : void -> nat), f = g.

Lemma UIP_implies_not_void_ext :
  UIP_refl -> VoidNat_Ext -> False.
Proof.
  intros Huip Hvn.
  specialize (Hvn (λ x, 0) (λ x, 1)).
  specialize (Huip _ _ Hvn).
*)


Definition isVecDerivativeOf 
    {n : nat} (f f' : Vector n TContR) : Type.
  revert f f'.
  induction n as [| np Hind]; intros f f';[exact unit|].
  destruct f as [fv ft].
  destruct f' as [fv' ft'].
  exact ((isDerivativeOf ft ft') × (Hind fv fv')).
Defined.

(*
Lemma XChangeUBEv2To3_2 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  let t2 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in

   ({X rotOrigininPos} t3 [-] {X rotOrigininPos} t2) 
      ≤  (Ev23TimeGapUB * (speed + transErrTrans)%Q).
Proof.
  intros.
  pose proof (XChangeUBEv2To3) as Hyd.
  cbv zeta in Hyd.
  eapply leEq_transitive;[apply Hyd|].
  fold t2 t3. clear Hyd.
  unfold Q2R. rewrite inj_Q_mult.
  apply mult_resp_leEq_rht;[apply MotorEv23Gap2_3; fail|].
  eauto 2 with CoRN ROSCOQ.
Qed.
*)

(*
Lemma ThetaConstFunSin :  IContREqInIntvl 
                          Ev2To3Interval
                            ((transVel icreate)[*]CFSine (theta icreate))
                            ((ContConstFun _ _ (Sin θ2)) [*] (transVel icreate)).
Proof.
  intros t Hb.
  rewrite TContRMult, TContRMult, CFSineAp.
  rewrite mult_commutes.
  apply mult_wdl.
  apply pfwdef.
  simpl. eapply TContRR2QCompactIntEq2; eauto.
  apply OmegaThetaEv2To3.
  unfold inBounds, Ev2To3Interval in Hb.
  simpl in Hb.   rewrite <- QT2T_Q2R, <- QT2T_Q2R in Hb.
  assumption.
Qed.

Lemma ThetaConstFunCos :  IContREqInIntvl 
                          Ev2To3Interval
                            ((transVel icreate)[*]CFCos (theta icreate))
                            ((ContConstFun _ _ (Cos θ2)) [*] (transVel icreate)).
Proof.
  intros t Hb.
  rewrite TContRMult, TContRMult, CFCosAp.
  rewrite mult_commutes.
  apply mult_wdl.
  apply pfwdef.
  simpl. eapply TContRR2QCompactIntEq2; eauto.
  apply OmegaThetaEv2To3.
  unfold inBounds, Ev2To3Interval in Hb.
  simpl in Hb.   rewrite <- QT2T_Q2R, <- QT2T_Q2R in Hb.
  assumption.
Qed.

Lemma PosPosAtEV3 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  posAtTime t3 = {|X := distTraveled * (Cos θ2);
                            Y := distTraveled * (Sin θ2) |}.
Proof.
  pose proof (TBarrowEta (derivX icreate) Ev2To3Interval) as HX.
  pose proof ThetaConstFunCos as Heq.
  apply Cintegral_wd2 in Heq.
  rewrite Heq in HX.
  simpl scs_elem in HX.
  unfold fst, snd in HX.
  clear Heq.
  rewrite CIntegral_scale in HX.
  fold distTraveled in HX.
  pose proof (TBarrowEta (derivY icreate) Ev2To3Interval) as HY.
  pose proof ThetaConstFunSin as Heq.
  apply Cintegral_wd2 in Heq.
  rewrite Heq in HY.
  simpl scs_elem in HY.
  unfold fst, snd in HY.
  clear Heq.
  rewrite CIntegral_scale in HY.
  fold distTraveled in HY.
  pose proof (TransVelPosAtEV2 
      (MotorEventsNthTime 2 (decAuto (2 < 4)%nat I))) as H2.
  unfold le, Le_instance_QTime in H2.
  DestImp H2;
    [|split; [apply MotorEventsNthTimeInc; omega| lra]].
  repnd.
  unfold posAtTime in H2r.
  unfold equiv, EquivCart in H2r.
  simpl in H2r. repnd.
  rewrite H2rl in HX.
  rewrite H2rr in HY. 
  clear H2rr H2rl.
  destruct (initPos icreate) as [Hx Hy].
  setoid_rewrite Hx in HX.
  setoid_rewrite Hy in HY.
  clear Hx Hy.
  intros ?.
  fold t3 in HX, HY.
  unfold zero, Zero_instance_IR, cg_minus in HX, HY.
  ring_simplify in HX.
  ring_simplify in HY.
  unfold posAtTime, equiv, EquivCart.
Local Opaque Sin Cos.
  simpl.
  rewrite <- HX, <- HY.
  unfoldMC. unfold Mult_instance_IR.
  split; ring.
Qed.



Lemma normSqrQ : ∀ (q : Cart2D Q),
  (' (X q))[^]2 [+] (' (Y q))[^]2
  [=] ('(|q|))[^]2.
Proof. 
  intros q.
  unfold CanonicalNotations.norm, NormSpace_instance_Cart2D.
  unfold cast, Cart_CR_IR, Cast_instace_Q_IR.
  unfold sqrtFun, rational_sqrt_SqrtFun_instance.
  rewrite rational_sqrt_correct.
  rewrite IRasCRasIR_id.
  rewrite sqrt_sqr. rewrite <- inj_Q_power, <- inj_Q_power.
  rewrite <- inj_Q_plus.
  apply inj_Q_wd.
  simpl. unfoldMC. reflexivity.
Grab Existential Variables.
  rewrite <- inj_Q_Zero.
  apply inj_Q_leEq.
  unfoldMC. pose proof (cc_abs_aid _ (X q) (Y q)) as HH.
  simpl in HH.
  simpl. lra.
Qed.

  
  
(*
Lemma ABCSqrRW : ∀ d X Y: IR, 
d[^]2 [+] X[^]2 [+] Y[^]2 =
(d [-] NRootIR.sqrt (X[^]2 [+] Y[^]2) _ )[^]2
  [+] 2[*] NRootIR.sqrt (X[^]2 [+] Y[^]2) _.
*)
  

Local Opaque nexp_op.  
Require Import  MathClasses.interfaces.additional_operations.

Lemma XDistEV3 :
  let t3 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  (distSqr (posAtTime t3) targetPosR) = 
      (distTraveled - ('|targetPos |)) ^ 2 
      + 2 * distTraveled *('|targetPos |) * (1 - Cos (optimalTurnAngle - θ2)).
Proof.
  simpl. rewrite PosPosAtEV3.
  unfold targetPosR, cast, castCart.
  unfold distSqr. 
  unfold canonical_names.negate, Negate_instance_Cart2D
      ,plus, Plus_instance_Cart2D.
  simpl. unfold normSqr.
  simpl.
  unfoldMC. fold zero. autounfold with IRMC.
  remember (' X targetPos) as Xt.
  remember (' Y targetPos) as Yt.
  remember (Cos θ2) as ct.
  remember (Sin θ2) as st.
  remember distTraveled as dt.

  match goal with
  [ |- ( ?x [=] _) ] => assert (x 
      [=] (dt[*]dt)[*](ct[*]ct [+] st[*]st)
          [+] (Xt[*]Xt [+] Yt[*]Yt)
          [-] ([1] [+] [1]) [*]dt[*](Xt[*]ct [+] Yt[*]st)) as Heq
  end.
  unfold cg_minus. ring.
  rewrite Heq. clear Heq.
  subst ct st.
  repeat (rewrite <- nexp_two).
  rewrite FFT.
  rewrite mult_one.
  rewrite HeqXt at 1.
  rewrite HeqYt at 1.
  rewrite normSqrQ.
  rewrite <- squareMinusIR2.
  fold (normSqr targetPosR).
  unfold cg_minus. rewrite <- plus_assoc_unfolded.
  unfold nat_pow.nat_pow_peano, peano_naturals.nat_1. 
  unfold pow.
  unfoldMC. unfold One_instance_IR. rewrite mult_one.
  rewrite <- nexp_two.
  apply plus_resp_eq.
  rewrite one_plus_one.

  pose proof (CartToPolarToXIR targetPos) as Ht.
  simpl in Ht.
  unfold castCart in Ht.
  unfold equiv, EquivCart in Ht.
  simpl in Ht.
  repnd.
  rewrite <- HeqXt in Htl.
  rewrite <- HeqYt in Htr.
  rewrite Htr, Htl.
  Replace (' polarTheta targetPos [=] optimalTurnAngle).
  unfoldMC. unfold Mult_instance_IR.
  remember (' (|targetPos |)) as tp.

  match goal with
  [ |- ( ?x [=] _) ] => assert (x 
      [=] Two[*]dt[*] tp [*] ([1] [-] (Cos optimalTurnAngle[*]Cos θ2[+] Sin optimalTurnAngle[*]Sin θ2))) as Heq
  end.
  unfoldMC. unfold cg_minus. ring.
  rewrite Heq. rewrite <- Cos_minus.
  unfold One_instance_IR.
  unfold cg_minus. 
  subst tp. unfold cast.
  ring.
Qed.
*)
(*
Lemma TransVelPosAtEV3 :
  let t0 : QTime := MotorEventsNthTime 2 (decAuto (2<4)%nat I) in
  let t1 : QTime := MotorEventsNthTime 3 (decAuto (3<4)%nat I) in
  ∀ (t : QTime),  t0 ≤ t ≤ t1
      → t1 ≤ t ≤ t0.
Proof.
  intros ? ? ? Hle.
  unfold le, Le_instance_QTime in Hle.
  pose proof correctVel2to3 as Hc.
  simpl in Hc. fold t0 t1 in Hc.
  unfold correctVelDuring in Hc.
  apply proj1 in Hc. simpl rad in Hc.
  match type of Hc with
  context[changesTo _ _ _ (Q2R ?nv) _ (QT2Q ?om)]
    => remember om as opr
  end.
  assert ((t0 + reacTime < t1)%Q) 
    as Hassumption by (apply MotorEventsNthTimeReac; omega).
  pose proof (qtimePos reacTime) as H99.
  (** multiply by the constant cos theta in Hc *)
  apply changesToDerivInteg2
    with (F:=(theta icreate)) (oldVal:=0) in Hc;
    eauto with ICR.
  clear H99.
Abort.
  rewrite initTheta in Ht0r.
  rewrite Ht0r in Hc.
  rewrite Ht0l in Hc.
  rewrite  (AbsIR_minus 0)  in Hc .
  rewrite cg_inv_zero in Hc.
  rewrite IR_inv_Qzero in Hc.
  rewrite AbsIRNewOmega in Hc.
  pose proof MotorEv01Gap2 as Hg.
  Local Opaque Qabs.Qabs.
  simpl in Hg.
  fold t0 t1 in Hg.
  apply (inj_Q_leEq IR) in Hg.
  rewrite <- AbsIR_Qabs in Hg.
  rewrite inj_Q_minus in Hg.
  rewrite <- inj_Q_mult in Hc.
  Local Opaque Qmult AbsIR.
  simpl in Hc.
  rewrite Qmult_comm in Hc.
  apply AbsIR_imp_AbsSmall in Hg.
  apply AbsIR_imp_AbsSmall in Hc.
  pose proof (AbsSmall_plus _ _ _ _ _ Hc Hg) as Hadd.
  fold (newVal) in Hadd.

  unfold Q2R in Hadd. ring_simplify in Hadd.
  unfold cg_minus in Hadd. ring_simplify in Hadd.
  clear Hg Hc.
  revert Hadd.
  unfoldMC. intro Hadd. unfold QT2R in Hadd.
  unfold Q2R in Hadd.
  Local Opaque inj_Q.
  autorewrite with QSimpl in Hadd. simpl in Hadd.
  match type of Hadd with 
  AbsSmall (inj_Q _ ?r%Q) _ => assert (r == rotspeed * (2 * (sendTimeAcc + delivDelayVar) + reacTime) + opr * (t1 - t0))%Q
                                    as Heqq by (unfoldMC ;ring); rewrite Heqq in Hadd; clear Heqq
  end.
  pose proof (approximateAbsSmallIR (polarTheta targetPos) anglePrec) as Hball.
  apply AbsSmall_minus in Hball.
  pose proof (AbsSmall_plus _ _ _ _ _  Hadd Hball) as Haddd.
  clear Hball Hadd. rename Haddd into Hadd.
  fold (optimalTurnAngle) in Hadd.
  unfold Q2R, cg_minus in Hadd.
  ring_simplify in Hadd. 
  rewrite <- inj_Q_plus in Hadd.
  subst opr.
  unfold Le_instance_IR.
  simpl in Hadd.
  apply AbsSmall_imp_AbsIR in Hadd.
  eapply leEq_transitive;[apply Hadd|].
  apply eqImpliesLeEq.
  apply inj_Q_wd.
  simpl. unfoldMC. ring.
*)
