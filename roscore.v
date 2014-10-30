Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export core.


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

Set Implicit Arguments.
Class RosTopicType (RT : Type) {deq : DecEq RT}
:=
{
    (** each topic is associated with a type of messages *)
    topicType : RT -> Type
}.

(** the [RosTopic] "selfTCP" is reserved.
    it is subscribed by only the node with that
    TCP adress and anyone can write to it *)

Section RosCore.

Context  `{rtopic : RosTopicType RosTopic}.

Definition Message := sigT topicType.
(* string could be rrplaced by a list bool to indicate a binary blob *)


Require Export Process.

Definition ProcessTiming 
  (p : Process Message (list Message)) :=
  Message -> Time.

Set Implicit Arguments.

Record TopicInfo :=
{
    subscribeTopics : list RosTopic;
    publishTopics : list RosTopic
}.

Record RosSwNode :=
{
    process :> Process Message (list Message);

(* 
    privateTopic : RosTopic;


    need to ensure that when processes are give
    inputs in topics [subscribedTopics] the outputs
    are only in [publishTopics].
    the implementation subscribes to these topics
*)

    (** The following is only for reasoning purposes
      and will not be extracted *)

    pTiming : ProcessTiming process
  
}.

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

Definition SimplePureProcess (inT outT : RosTopic)
  := (topicType inT) -> (topicType outT).

Definition transport {T:Type} {a b:T} {P:T -> Type} (eq:a=b) (pa: P a) : (P b):=
@eq_rect T a P pa b eq.


Definition getPayLoad  (topic : RosTopic) (m : Message) :
option (topicType topic) :=
match m with
| existT tp pl => match (eqdec  tp topic) with
                  | left peq =>  Some (@transport _ _ _ (fun tpp => ( (topicType tpp))) peq pl)
                  | right _ => None
                  end
end.


CoFixpoint liftToMesg {InTopic OutTopic} 
  (f : SimplePureProcess InTopic OutTopic) 
    : Process Message (list Message) :=
buildP ( fun inpMesg : Message => (liftToMesg f,
match (getPayLoad InTopic inpMesg ) with
| Some tmesg => cons (existT  _ _ (f tmesg)) nil
| None => nil
end)).
  
(** There is no code to extract for devices
    These are here to model environment *)

Record RosInpDevNode (Env : Type) :=
{
  (*  IDnodeName : string; *)
    outTopic : RosTopic; 
    idev :> InpDev Env  (topicType outTopic)
}.

Definition makeTopicMesg {outTopic : RosTopic}
  (payload : ( (topicType outTopic))) : Message.
econstructor; eauto. 
  (* in this context, there is only one possible message *)
Defined.

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




Definition filterMegsByTopic (lm : list Message) 
  (topic : RosTopic) : list ( (topicType topic)) :=
flat_map (fun m => op2List (getPayLoad topic m)) lm.


  
Definition getRosOutDevBhv  {Env : Type}
    (p: RosOutDevNode Env )
    (allInputs : list Message)  : OutDevBehaviour Env :=
    let filterMsgs := filterMegsByTopic allInputs (inpTopic p) in
    match filterMsgs with
    | nil => fst (odev p)
    | last :: rest => getLastOutput (snd (odev p)) rest last
    end.


Definition mtopic (m : Message) :=
(proj1_sigT _ _ m).

Definition validRecvMesg (rn : TopicInfo) (m : Message) :=
In (mtopic m) (subscribeTopics rn).

Definition validSendMesg (rn : TopicInfo) (m : Message) :=
In (mtopic m) (publishTopics rn).

End RosCore.


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
