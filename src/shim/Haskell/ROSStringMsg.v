Require Import RoshaskMsg.
Require Import String.
Require Import ExtrHaskellString.


(** This file exposes https://github.com/aa755/ROSCoq/blob/bbc63a39163b8df2e287673fc769f0f77529be21/src/shim/Haskell/examples/String.hs to Coq.
   It defines the following ROS message : http://docs.ros.org/api/std_msgs/html/msg/String.html
*)

Extraction Language Haskell.

(** temporary example for generation of Coq types for ROS messages, 
   and extraction to corresponding Haskell messages.*)
Record ROS_StdMsg_String := mkString
                              {__data:string}.

Extract Inductive ROS_StdMsg_String => "Ros.Std_msgs.String.String"
                                            [ "Ros.Std_msgs.String.String"].

Extract Constant __data => "Ros.Std_msgs.String.__data".

Require Import RoshaskNodeMonad.
Require Import RoshaskTopic.

Axiom subscribe_ROS_StdMsg_String : TopicName -> Node (RTopic ROS_StdMsg_String).
Extract Constant  subscribe_ROS_StdMsg_String => "(Ros.Node.subscribe)".

Axiom publish_ROS_StdMsg_String : TopicName -> RTopic ROS_StdMsg_String -> Node unit.
Extract Constant  publish_ROS_StdMsg_String => "(Ros.Node.advertise)".

(*
Axiom advertise_String  : TopicName -> Node (Chan ROS_StdMsg_String).
Extract Constant advertise_String => "Ros.ROSCoqUtil.advertiseNewChan".
 *)

Instance ROSMsgInstance_ROS_StdMsg_String : ROSMsgType ROS_StdMsg_String :=
  Build_ROSMsgType _  subscribe_ROS_StdMsg_String  publish_ROS_StdMsg_String (* advertise_String *).



