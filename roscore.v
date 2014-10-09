Require Import String.

Set Implicit Arguments.

Record RosMesgType := {
    RosMsgID : string;
    payLoadType : Type
}.

Record TCPAddress := {
    addrAsString : string
}.

Record RosTopic := {
    TMasterAddress : TCPAddress;
    topicName : string;
    (** each topic is associated with a type of messages *)
    topicType : RosMesgType
}.

(** the [RosTopic] "selfTCP" is reserved.
    it is subscribed by only the node with that
    TCP adress and anyone can write to it *)

Inductive Message :=
| topicM :  forall (r :RosTopic), payLoadType (topicType r) -> Message.
(* string could be rrplaced by a list bool to indicate a binary blob *)


Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export Process.

Definition ProcessTiming 
  (p : Process Message (list Message)) :=
  forall (m: Message),
    {tl : list Time | length tl = length (getOutput p m) }.



Record RosSwNode :=
{
    SNmaster : TCPAddress;
    nodeName : string;
    nodeAddress : TCPAddress;
    subscribedTopics : list RosTopic;
    publishTopics : list RosTopic;
    process : Process Message (list Message);
(* need to ensure that when processes are give
    inputs in topics [subscribedTopics] the outputs
    are only in [publishTopics].
    the implementation subscribes to these topics
*)

    (** The following is only for reasoning purposes
      and will not be extracted *)
    pTiming : ProcessTiming process

  
}.

(** There is no code to extract for devices
    These are here to model environment *)

Record RosInpDevNode (Env : Type) :=
{
    IDMasterAddress : TCPAddress;
    IDnodeName : string;
    outTopic : RosTopic;
    idev : InpDev Env (payLoadType (topicType outTopic))
}.

Definition makeTopicMesg {outTopic : RosTopic}
  (payload : (payLoadType (topicType outTopic))) : Message.
econstructor; eauto. 
  (* in this context, there is only one possible message *)
Defined.

Definition substIDev {Env : Type} (rid : RosInpDevNode Env)
  (newd : InpDev Env (payLoadType (topicType (outTopic rid))))
  : RosInpDevNode Env :=
Build_RosInpDevNode (IDMasterAddress rid)
                    (IDnodeName rid)
                    (outTopic rid)
                    newd.


Record RosOutDevNode (Env : Type) :=
{
    ODMasterAddress : TCPAddress;
    ODnodeName : string;
    inpTopic : RosTopic;
    odev : OutDev Env (payLoadType (topicType inpTopic))
}.
  
(** Implementing this will need simplification of topic definitions.
  We need decidable equality on topics, which is not currently true *)
Definition filterMegsByTopic (lm : list Message)
  (topic : RosTopic) : list (payLoadType (topicType topic)).
Admitted.
  
Definition getRosOutDevBhv  {Env : Type}
    (p: RosOutDevNode Env )
    (allInputs : list Message)  : OutDevBehaviour Env :=
    let filterMsgs := filterMegsByTopic allInputs (inpTopic p) in
    match filterMsgs with
    | nil => fst (odev p)
    | last :: rest => getLastOutput (snd (odev p)) rest last
    end.

Set Implicit Arguments.

Inductive RosNode : Type := 
| rsw : RosSwNode -> RosNode
| rhi : forall {Env : Type}, 
        RosInpDevNode Env -> RosNode
| rho : forall {Env : Type}, 
        RosOutDevNode Env -> RosNode.

Open Scope list_scope.

Definition IncomingTopics  (rn : RosNode) : list RosTopic
  :=
match rn with
| rsw rsn => subscribedTopics rsn
| rhi _ _ => nil
| rho _ rout =>  cons (inpTopic rout) nil
end.

