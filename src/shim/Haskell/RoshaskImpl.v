Require Import String.
Require Import RoshaskMsg.
Require Import ROSCOQ.message.

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

Class RosHaskImplementable (Topic:Type) `{TopicClass Topic} :=
{
   topicImplType  : Topic -> Type (** Would Set suffice?*);
   topicImplTypeCorrect: forall (t:Topic), ROSMsgType (topicImplType t);
   (**ideally, identity, used when sending a message*)
   toImpl : forall (t:Topic), (topicType t) ->  (topicImplType t) ;
   (**ideally, identity, used when receiving a message*)
   fromImpl : forall (t:Topic), (topicImplType t) ->  (topicType t);
   
   rosQualName : Topic -> TopicName
                                                       
}.

(** Given the above (possibly trivial) implementation details, we promise to run a software agent
    in a way specified by [SwSemantics]. *)

Require Import CPS.

Section RunSwAgent.
  Context (Topic:Type) `{TopicClass Topic} `{RosHaskImplementable Topic}.

  Require Import RoshaskNodeMonad.
  Require Import CoList.
  

  (** some helper functions *)
  Definition mkMsg (t:Topic) (rospayload : topicImplType t) : Message :=
    (existT _ t (fromImpl t rospayload), defHdr).

  Require Import MathClasses.interfaces.monads.
  Open Scope mc_scope.

  Instance fsldkjfkdsj  (t:Topic):  ROSMsgType (topicImplType t) := topicImplTypeCorrect t.

  
  Definition subscribeMsgCoList  (t:Topic) : Node (CoList Message) :=
    strmIn  ← (subscribe (rosQualName t));
    ret (coMap (mkMsg t) strmIn). (* Perhaps define an instance of the  Functor typeclass and just say fmap instead of coMap *)
    
    
    
  
  
  Variable (sw: RosSwNode). (** we are supposed to run this agent(node), using the API exported from roshask *)
  Variable tpInfo :  @TopicInfo Topic. (** which topics [sw] subscribes/publishes to*)
    
 
  Definition runSwNode (tp: @TopicInfo Topic): Node unit. Admitted.    
    
End RunSwAgent.
