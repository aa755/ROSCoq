Require Import String.
Require Import ExtrHaskellString.
Require Import ROSCOQ.CoList.
Require Import RoshaskNodeMonad.


Definition TopicName : Type := string.

(** These are streams that can be published/subscribed to/from ROS topics.
    However, there can be streams which are 
    only used for intermediate results, or even stremas
    which have nothing to do with topics.
    
    One can think of [ROSStream T] as [Topic IO T] in roshask.
    Note that the notation [] in comments has nothing to do with lists.
    These are coqdoc directives to indicate that the thing inside is a code object.
  *)
Definition ROSStream (T:Type) := CoList T.

Class ROSMsgType (T:Type) :=
  {    
   subscribe : TopicName -> Node (ROSStream T);
   publish : TopicName -> ROSStream T -> Node unit (*will be mapped to advertize in Roshask*)
}.

(**roshask will be modified to generate Coq Types for ROS message types. These message types
will be instances of the above typeclass. The publish and subscribe implementations will use 
subscribe and advertize methods respectively in roshask.
On top of these functions, the ROSCoq message handler functionality will be built.
*)
