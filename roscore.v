Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.

Require Import String.

Record RosMesgType := {
    RosMsgID : string;
    payLoadType : Type
}.

Record ROSTopic := {
    topicName : string;
    (** each topic is associated with a type of messages *)
    topicType : RosMesgType
}.

Record GenericAddress := {
    addrAsString : string
}.

Inductive Message :=
| topicM :  forall (r :ROSTopic), payLoadType (topicType r) -> Message
(* string could be rrplaced by a list bool to indicate a binary blob *)
| genricM :  GenericAddress -> string -> Message.

Require Export Process.

Record ROSNode :=
{
    nodeName : string;
    genericAddress : string;
    subscribedTopics : list ROSTopic;
    publishTopics : list ROSTopic;
    process : Process Message Message
}.




