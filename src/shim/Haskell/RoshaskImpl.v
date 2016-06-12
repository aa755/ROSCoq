Require Import String.
Require Import RoshaskMsg.
Require Import ROSCOQ.message.
Require Import RoshaskTopic.



(** 
To run a ROSCoq CPS using roshask, one has to provide some 
   ROS(hask) specific implementation details.
   One has to map the payload types for ROSCoq topics to actual ROS message types whose
   Haskell and Coq files have already been generated using the roshask utility.
   Ideally, if one directly used ROS message types in ROSCoq, this mapping will be
   an identity function. However, one may wish to reason about a simplified datatype
   in ROSCoq. For examples, while reasoning, it is painful to worry about
   how data is encoded into bytes.
   
   One also has to map each topic to the string that represents the 
   fully qualified name of the actual ROS topic.
  
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

  
  Definition subscribeMsgCoList  (t:Topic) : Node (RTopic Message) :=
    strmIn  ← (subscribe (rosQualName t));
    ret (tmap (mkMsg t) strmIn). (* Perhaps define an instance of the  Functor typeclass and just say fmap instead of coMap *)

  Require Import MCInstances.
  Require Export MathClasses.misc.decision.

  Open Scope nat_scope.
  Require Omega.
  Definition subscribeMsgMultiple  (lt: list Topic) (p: 0 < length lt) : Node (RTopic Message).
    induction lt as [|h tlt]; [simpl in p; omega|].
    destruct tlt.
    - exact (subscribeMsgCoList h).
    - assert (0 < Datatypes.length (t :: tlt)) as pl. simpl. omega.
      apply IHtlt in pl.
      exact   (sh ←  subscribeMsgCoList h;
               stl ←  pl;
                ret (asapMerge sh stl)).
  Defined.
  
                             
  Variable (sw: Process Message (list Message)). (** we are supposed to run this agent(node), using the API exported from roshask *)
    (** move to ROSCOQ.MsgHandler*)

  
  Variable tpInfo :  @TopicInfo Topic. (** which topics [sw] subscribes/publishes to*)

  Require Import decInstances.
  Require Import MathClasses.interfaces.abstract_algebra.
  Require Import RoshaskMsg.

  Definition updateDepMap `{DecEq A} {B: A -> Type} (init : forall a:A, B a) (a:A) (newb : B a) (x:A) : B x.
    destruct (decide (x≡a)).
    - rewrite e. exact newb.
    - exact (init x).
  Defined.

  Definition delayInMicros (m:Message) : Z :=
    let (num,den) := (delay (snd m)) * delayResolutionSecInv  in
     Zdiv num den.
    

  Definition delayMessages (rt: RTopic Message) : RTopic Message :=
    delayMsgsRoshask delayInMicros rt.
                     
    
  (*  Definition TopicChannel := forall t:Topic, option (Chan (topicImplType t)).

  (** update if it was none.*)
  Definition lookupChan (tc : TopicChannel) (t:Topic) : Node ((Chan (topicImplType t))  × TopicChannel) :=
        match tc t with
          | Some c => ret (c, tc)
          | None => nc ← advertiseNewChan (rosQualName t);
                    ret (nc, updateDepMap tc t (Some nc))
        end.
                                                  
  
  Definition publishMsgsStep (chans : TopicChannel)(m : Message) : Node TopicChannel :=
        let t := mtopic m in
          p ← lookupChan chans t;
          _ ← publishDelayedMsgOnChan (delayInMicros m) (fst p) (toImpl t (mPayload m));
          ret (snd p).

  Definition initTopicChan : TopicChannel := λ t, None.
  
  Definition publishMsgs (outMsgs: CoList Message) : Node unit :=
    _ ← coFoldLeft publishMsgsStep outMsgs initTopicChan; ret tt.
*)

  Definition filterTopic (t:Topic)
             (msgs : RTopic Message) : (RTopic (topicImplType t)).
    apply tfilter with (f:= fun m => bool_decide (mtopic m ≡ t));[ | exact msgs].
    intros a p.
    apply bool_decide_true in p.
    rewrite <- p. exact (toImpl (mtopic a) (mPayload a)).
  Defined.
  
  Fixpoint publishMsgsNoTiming  (lt: list Topic) (msgs: RTopic Message) : Node unit :=
    match lt with
      | nil => ret tt
      | h::tl =>
        _ ← (publish (rosQualName h) ((filterTopic h msgs)));
        publishMsgsNoTiming tl msgs
    end.

  Definition swap {A B: Type} (p: A * B) : B* A := (snd p, fst p).
  
  Definition procOutMsgs {I O : Type} (p : Process I O)
           (ins : RTopic I) : RTopic O :=
  @foldMapL (State p) I O (curState p) (fun s i => swap (handler p s i)) ins.

  Variable prf : (0 < Datatypes.length (fst tpInfo))%nat.
  
  Definition runSwNode : Node unit :=
    let (_, pubTopics) := tpInfo in
  inMsgs ← subscribeMsgMultiple (fst tpInfo) prf;
  publishMsgsNoTiming pubTopics (delayMessages (flattenTL (procOutMsgs sw inMsgs))).
    
End RunSwAgent.
