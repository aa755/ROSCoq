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

(* Haskell Definition, which doesn't work in Coq, because m may not be positive
newtype Topic m a = Topic { runTopic :: m (a, Topic m a) } 

CoInductive Topic (m:Type ->Type) `{Monad m} (a:Type) :=
| CTopic (runTopic : m (a × Topic m a)).


Error: Non strictly positive occurrence of "Topic" in
 "m (a × Topic m H H0 H1 H2 a) → Topic m H H0 H1 H2 a". 
*)


Class ROSMsgType (T:Type) :=
  {
    (* it will be incorrect to remove [Node] (monad) below. If the return type was
      just [CoList T], Coq's semantics need that it be reduced to either a [cnil]
      or a [ccons _ _] within a bounded amount of time. Unfortunately, since
      elements of this "stream" are coming from outside world, we have no control over
      when things will arrive.       
      Also, there will be issues with being a function, i.e. equal output for equal topic name.
 *)
   subscribe : TopicName -> Node (CoList T);
   publish : TopicName -> CoList T -> Node unit (*will be mapped to advertize in Roshask*)
}.

(**roshask will be modified to generate Coq Types for ROS message types. These message types
will be instances of the above typeclass. The publish and subscribe implementations will use 
subscribe and advertize methods respectively in roshask.
On top of these functions, the ROSCoq message handler functionality will be built.
*)


Axiom Chan : Type -> Type.
Extract Constant Chan "a" => "Control.Concurrent.Chan".

(** The first two arguments are implicit in Haskell. They musst be so here*)
Axiom advertiseNewChan  : forall {a:Type} {_: ROSMsgType a} , TopicName -> Node (Chan a).
Extract Constant advertiseNewChan => "Ros.ROSCoqUtil.advertiseNewChan".


Axiom  publishMsgOnChan: forall {a:Type}, (Chan a) -> a -> Node unit.
Extract Constant publishMsgOnChan => "Ros.ROSCoqUtil.publishMsgOnChan".


Require ExtrHaskellZNum.
Require Import ZArith.
Axiom publishDelayedMsgOnChan: forall {a:Type}, Z -> (Chan a) -> a -> Node unit.
Extract Constant publishDelayedMsgOnChan => "Ros.ROSCoqUtil.publishDelayedMsgOnChan".

