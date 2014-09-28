Require Import String.

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



Inductive Message :=
| topicM :  forall (r :RosTopic), payLoadType (topicType r) -> Message
(* string could be rrplaced by a list bool to indicate a binary blob *)
| genricM :  TCPAddress -> string -> Message.

Require Export Process.

Record RosSwNode :=
{
    SNmaster : TCPAddress;
    nodeName : string;
    nodeAddress : TCPAddress;
    subscribedTopics : list RosTopic;
    publishTopics : list RosTopic;
    process : Process Message Message
(* need to ensure that when processes are give
    inputs in topics [subscribedTopics] the outputs
    are only in [publishTopics].
    the implementation subscribes to these topics
*)
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

Record RosOutDevNode (Env : Type) :=
{
    ODMasterAddress : TCPAddress;
    ODnodeName : string;
    inpTopic : RosTopic;
    odev : OutDev Env (payLoadType (topicType inpTopic))
}.

