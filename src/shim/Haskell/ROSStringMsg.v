Require Import RoshaskMsg.
Require Import String.
Require Import ExtrHaskellString.


Extraction Language Haskell.

(** temporary example for generation of Coq types for ROS messages, 
   and extraction to corresponding Haskell messages.*)
Record ROS_StdMsg_String := mkString
                              {__data:string}.

Extract Inductive ROS_StdMsg_String => "Ros.Std_msgs.String.String"
                                            [ "Ros.Std_msgs.String.String"].

Extract Constant __data => "Ros.Std_msgs.String.__data".

Require Import RoshaskNodeMonad.

Axiom subscribe_ROS_StdMsg_String : TopicName -> Node (ROSStream ROS_StdMsg_String).
Extract Constant  subscribe_ROS_StdMsg_String => "(Ros.ROSCoqUtil.subscribeCoList)".

Axiom publish_ROS_StdMsg_String : TopicName -> ROSStream ROS_StdMsg_String -> Node unit.
Extract Constant  publish_ROS_StdMsg_String => "(Ros.ROSCoqUtil.publishCoList)".

Instance ROSMsgInstance_ROS_StdMsg_String : ROSMsgType ROS_StdMsg_String :=
  Build_ROSMsgType _  subscribe_ROS_StdMsg_String  publish_ROS_StdMsg_String.



