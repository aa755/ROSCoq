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


Require Import MathClasses.interfaces.monads.

                          
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
    
  Fixpoint subscribeMsgMultiple  (lt: list Topic) : Node (CoList Message) :=
    match lt with
      | nil => ret (cnil Message)
      | h::tl =>
        sh ←  (subscribeMsgCoList h);
        stl ← (subscribeMsgMultiple tl);
        asapMerge sh stl
    end.
                             
  Variable (sw: Process Message (list Message)). (** we are supposed to run this agent(node), using the API exported from roshask *)
    (** move to ROSCOQ.MsgHandler*)

  
  Variable tpInfo :  @TopicInfo Topic. (** which topics [sw] subscribes/publishes to*)

  Require Import decInstances.
  Require Import interfaces.abstract_algebra.
  Require Import RoshaskMsg.

  Definition updateDepMap `{DecEq A} {B: A -> Type} (init : forall a:A, B a) (a:A) (newb : B a) (x:A) : B x.
    destruct (decide (x≡a)).
    - rewrite e. exact newb.
    - exact (init x).
  Defined.

  Definition TopicChannel := forall t:Topic, option (Chan (topicImplType t)).

  (** update if it was none.*)
  Definition lookupChan (tc : TopicChannel) (t:Topic) : Node ((Chan (topicImplType t))  × TopicChannel) :=
        match tc t with
          | Some c => ret (c, tc)
          | None => nc ← advertiseNewChan (rosQualName t);
                    ret (nc, updateDepMap tc t (Some nc))
        end.

  (** there is an unwritten rule that Qden is 10^6. This should be captured in types*)
  Definition delayInMicros (m:Message) : Z := Qnum (delay (snd m)).
                                                  
  
  Definition publishMsgsStep (chans : TopicChannel)(m : Message) : Node TopicChannel :=
        let t := mtopic m in
          p ← lookupChan chans t;
          _ ← publishDelayedMsgOnChan (delayInMicros m) (fst p) (toImpl t (mPayload m));
          ret (snd p).

  Definition initTopicChan : TopicChannel := λ t, None.
  
  Definition publishMsgs (outMsgs: CoList Message) : Node unit :=
    _ ← coFoldLeft publishMsgsStep outMsgs initTopicChan; ret tt.

  Definition filterTopicAux (t:Topic) (retm : CoList (topicImplType t))
             (h : Message) : Node (CoList (topicImplType t)).
    destruct (decide (mtopic h ≡ t));[ | exact (ret retm)].
    rewrite <- e. rewrite <- e in retm. exact (ret (ccons (toImpl (mtopic h)(mPayload h)) retm)).
  Defined.
  
  Definition filterTopic (t:Topic)
             (msgs : CoList Message) : Node (CoList (topicImplType t)) :=
    coFoldLeft (filterTopicAux t) msgs (cnil (topicImplType t)).
  
  Fixpoint publishMsgsNoTiming  (lt: list Topic) (msgs: CoList Message) : Node unit :=
    match lt with
      | nil => ret tt
      | h::tl =>
        sh ←  (filterTopic h msgs);
        _ ← (publish (rosQualName h) sh);
        publishMsgsNoTiming tl msgs
    end.

       

  Definition runSwNode : Node unit :=
  let (subTopics, pubTopics) := tpInfo in
  inMsgs ← subscribeMsgMultiple subTopics;
  outMsgs ← flattenCoListList (procOutMsgs sw inMsgs); (** one can get rid of this flattening (undefineable in Coq) and just make [publishMsgs] a bit complicated. *)
  publishMsgsNoTiming pubTopics outMsgs.
    
End RunSwAgent.
