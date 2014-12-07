Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export core.



Set Implicit Arguments.
Class RosTopicType (RT : Type) {deq : DecEq RT}
:=
{
    (** each topic is associated with a type of messages *)
    topicType : RT -> Type
}.

(** the [RosTopic] "selfTCP" is reserved.
    it is subscribed by only the node with that
    TCP adress and anyone can write to it *)

Section RosCore.

Context  `{rtopic : RosTopicType RosTopic}.

Definition Message := sigT topicType.
(* string could be rrplaced by a list bool to indicate a binary blob *)


Require Export Process.

(*
Definition ProcessTiming 
  (p : Process Message (list Message)) :=
  Message -> QTime.
*)

(** needs to be made more general. 
    previously it used to depend on a proces
    but a process will change to sth else in next step *)
Definition ProcessTiming :=
  Message -> QTime.

Set Implicit Arguments.

Record TopicInfo :=
{
    subscribeTopics : list RosTopic;
    publishTopics : list RosTopic
}.

Record RosSwNode :=
{
    process :> Process Message (list Message);


    (** The following is only for reasoning purposes
      and will not be extracted *)

    pTiming : QTime
  
}.


Definition SimplePureProcess (inT outT : RosTopic)
  := (topicType inT) -> (topicType outT).

Definition transport {T:Type} {a b:T} {P:T -> Type} (eq:a=b) (pa: P a) : (P b):=
@eq_rect T a P pa b eq.


Definition getPayLoad  (topic : RosTopic) (m : Message) :
option (topicType topic) :=
match m with
| existT tp pl => match (eqdec  tp topic) with
                  | left peq =>  Some (@transport _ _ _ (fun tpp => ( (topicType tpp))) peq pl)
                  | right _ => None
                  end
end.

Definition liftToMesg {InTopic OutTopic} 
  (f : SimplePureProcess InTopic OutTopic) 
    : Message -> (list Message) :=
( fun inpMesg : Message => 
match (getPayLoad InTopic inpMesg ) with
| Some tmesg => cons (existT  _ _ (f tmesg)) nil
| None => nil
end).


Definition mtopic (m : Message) :=
(proj1_sigT _ _ m).

Require Export Coq.Unicode.Utf8.

Definition validRecvMesg (rn : TopicInfo) (lm : list Message) :=
∀ m, In m lm -> In (mtopic m) (subscribeTopics rn).

Definition validSendMesg (rn : TopicInfo) (lm : list Message) :=
∀ m, In m lm -> In (mtopic m) (publishTopics rn).


Definition makeTopicMesg (outTopic : RosTopic)
  (payload : ( (topicType outTopic))) : Message.
econstructor; eauto. 
  (* in this context, there is only one possible message *)
Defined.

Definition filterMegsByTopic (lm : list Message) 
  (topic : RosTopic) : list ( (topicType topic)) :=
flat_map (fun m => op2List (getPayLoad topic m)) lm.

End RosCore.

