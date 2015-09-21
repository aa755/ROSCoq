Require Import String.
Require Import ExtrHaskellString.
Require Import ROSCOQ.CoList.
Require Import RoshaskNodeMonad.
Require Import RoshaskTopic.


(*
Axiom Chan : Type -> Type.
Extract Constant Chan "a" => "Control.Concurrent.Chan a".
*)

Class ROSMsgType (T:Type) :=
  {
   subscribe : TopicName -> Node (RTopic T);
   publish : TopicName -> RTopic T -> Node unit (*will be mapped to advertize in Roshask*)
   (*; advertiseNewChan  : TopicName -> Node (Chan T) *)
}.

(**roshask will be modified to generate Coq Types for ROS message types. These message types
will be instances of the above typeclass. The publish and subscribe implementations will use 
subscribe and advertize methods respectively in roshask.
On top of these functions, the ROSCoq message handler functionality has been built.
*)


(*
Axiom  publishMsgOnChan: forall {a:Type}, (Chan a) -> a -> Node unit.
Extract Constant publishMsgOnChan => "Ros.ROSCoqUtil.publishMsgOnChan".



Axiom publishDelayedMsgOnChan: forall {a:Type}, Z -> (Chan a) -> a -> Node unit.
Extract Constant publishDelayedMsgOnChan => "Ros.ROSCoqUtil.publishDelayedMsgOnChan".
 *)

Require ExtrHaskellZNum.
Require Import ZArith.
Axiom delayMsgsRoshask : forall {A:Type}, (A -> Z) -> (RTopic A) ->  (RTopic A).
Extract Constant delayMsgsRoshask =>  "Ros.ROSCoqUtil.delayMsgs".
Definition delayResolutionSecInv :  positive := (1000000)%positive. (** depends on the Haskell definition of the function above.*)

