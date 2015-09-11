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
   
   One also has to map each topic to the string that represents the 
   fully qualified name of the actual ROS topic.

   To avoid confusion, perhaps we should drop the prefix ROS from names of types used in reasoning.
   So, RosTopicType should just be TopicType, because the information there is not yet at the level of ROS.
  
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

Class RosHaskImplementable (RosTopic:Type) `{RosTopicType RosTopic} :=
{
   topicImplType  : RosTopic -> Type (** Would Set suffice?*);
   topicImplTypeCorrect: forall (t:RosTopic), ROSMsgType (topicImplType t);
   (**ideally, identity, used when sending a message*)
   toImpl : forall (t:RosTopic), (topicType t) ->  (topicImplType t) ;
   (**ideally, identity, used when receiving a message*)
   fromImpl : forall (t:RosTopic), (topicImplType t) ->  (topicType t)
}.

(** Given the above (possibly trivial) implementation details, we promise to run a software agent
    in a way specified by [SwSemantics]. *)

Section RunSwAgent.
  Context (Topic:Type) `{RosTopicType Topic} `{RosHaskImplementable Topic}.
  Variable (sw: RosSwNode). (** we are supposed to run this agent(node), using the API exported from roshask *)

  Require Import RoshaskNodeMonad.
  Open Scope mc_scope. (** to get the monadic notations*)
 
  Definition runSwNode : Node unit. Admitted.
End RunSwAgent.
