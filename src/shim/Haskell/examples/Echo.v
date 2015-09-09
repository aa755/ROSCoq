Require Import RoshaskMsg.
Require Import String.
Require Import ExtrHaskellString.
Require Import RoshaskNodeMonad.
Require Import ROSStringMsg.
Extraction Language Haskell.
Open Scope string_scope.
Require Import MathClasses.interfaces.monads.
Open Scope mc_scope.
Require Import CoList.


(** This file illustrates how to directly use the roshask API exported to Coq. These programs (e.g. [echoNode] below) look
    very much like their roshask versions.
    [echoNode] listens for messages in the /chatter topic and echoes them to /chatterecho topic after prepending "I heard" to those strings.
 *)


Definition chatter : TopicName := "/chatter". (*its extract is unreadable*)
Definition chatterecho : TopicName := "/chatterecho". (*its extract is unreadable*)

Definition procStr (s:string) : string :=
  "I heard "++s.

Definition procStrMsg (s:  ROS_StdMsg_String ) :  ROS_StdMsg_String :=
  mkString (procStr (__data s)).


Definition echoNode : Node unit :=
  strmIn  ← (subscribe chatter);
  publish chatterecho (coMap procStrMsg strmIn).

Extraction "coqEcho.hs" echoNode.


