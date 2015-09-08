Require Import String.
Require Import RoshaskMsg.
Require Import ROSCOQ.roscore.

(** To run a ROSCoq CPS using roshask, one has to provide some 
   ROS(hask) specific implementation details.
   One has to map the abstract ROSCoq topic types to actual ROS message types whose
   Haskell and Coq files have already been generated using the roshask utility.
   Ideally, if one directly used ROS message types in ROSCoq, this mapping will be
   an identity function. However, one may wish to reason about a simplified datatype
   in ROSCoq. For examples, while reasoning, it is painful to reason about
   how data is encoded into bytes.
*)


(*Inspired by CompCert. NoDup was not there perhaps. 
  Perhaps finiteness of the Topic type is not needed. All we need
  is the finiteness of the collection of subscribed and published topics.
  They are already finite, as they are represented as lists. 
  
  TODO: 
  Add
  a NoDup condition in those lists, because the implmentation has to subscribe/publish
  to the topics one by one, and it does not make sense to subscribe/publish
  streams several times on a topic.
  
  What does roshask do if one tries to publish (or subscribe) multiple
  types on the same topic? What if different types of streams were used
   in the different attempts?
 *)
Definition FiniteC (T:Type) {deq : DecEq T} := {all:list T | NoDup all /\ forall t:T, In t all}.

Class RosHaskImplementable  `{RosTopicType RosTopic} :=
{
   topicImplType  : RosTopic -> Type (** Would Set suffice?*);
   topicImplTypeCorrect: forall (t:RosTopic), RoshashMsgType (topicImplType t);
   (**ideally, identity, used when sending a message*)
   toImpl : forall (t:RosTopic), (topicType t) ->  (topicImplType t) ;
   (**ideally, identity, used when receiving a message*)
   fromImpl : forall (t:RosTopic), (topicImplType t) ->  (topicType t)
}.


