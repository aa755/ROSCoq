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

Record Header := mkHeader
{
  (** how much should message be delayed from the soonest time it can be sent
    If it is the first message resulting from processing of an event,
    the soonest time is the time when the processing was compete.
    If this is a later message, then the soonest time is the time 
    when the provious message was sent *)
    
  delay : Q
}.

Section RosCore.

Context  `{RosTopicType RosTopic}.

Definition Message := (sigT topicType) × Header .
(* string could be rrplaced by a list bool to indicate a binary blob *)


Require Export Process.


(** needs to be made more general. 
    previously it used to depend on a proces
    but a process will change to sth else in next step *)
Definition ProcessTiming :=
  Message -> QTime.

Set Implicit Arguments.

Require Export Coq.Unicode.Utf8.

Definition TopicInfo := (list RosTopic) × (list RosTopic).

Definition  subscribeTopics (t: TopicInfo ):= fst t.
Definition  publishTopics (t: TopicInfo ):= snd t.

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


Definition getPayLoadR  (topic : RosTopic) (m : sigT topicType) :
option (topicType topic) :=
match m with
| (existT tp pl) => match (eqdec  tp topic) with
                  | left peq =>  Some (@transport _ _ _ (fun tpp => ( (topicType tpp))) peq pl)
                  | right _ => None
                  end
end.

Definition getPayLoad  (topic : RosTopic) (m : Message) :
option (topicType topic) := getPayLoadR topic (fst m).

Definition defHdr :=  mkHeader 0.

Definition mkImmMesg (outTopic : RosTopic)
  (payload : ( (topicType outTopic))) : Message.
econstructor; eauto;[].
exact defHdr.
  (* in this context, there is only one possible message *)
Defined.

Definition liftToMesg {InTopic OutTopic} 
  (f : SimplePureProcess InTopic OutTopic) 
    : Message -> (list Message) :=
( fun inpMesg : Message => 
match (getPayLoad InTopic inpMesg ) with
| Some tmesg => cons ((mkImmMesg _ (f tmesg))) nil
| None => nil
end).


Definition mtopicR (m : sigT topicType) :=
(proj1_sigT _ _  m).

Definition mtopic (m : Message) := 
mtopicR (fst m).

Definition mPayLoad (m : Message) : topicType (mtopic m) :=
(proj2_sigT _ _ (fst m)).

Definition validRecvMesg (rn : TopicInfo) (lm : list Message) :=
∀ m, In m (map fst lm) -> In (mtopicR m) (subscribeTopics rn).

Definition validSendMesg (rn : TopicInfo) (lm : list Message) :=
∀ m, In m (map fst lm) -> In (mtopicR m) (publishTopics rn).


Definition mkMesg (outTopic : RosTopic)
  (payload : ( (topicType outTopic))) : (sigT topicType).
econstructor; eauto.
  (* in this context, there is only one possible message *)
Defined.


Definition mkDelayedMesg {outTopic : RosTopic}
  (delay : Q) (payload : ( (topicType outTopic))) : Message.
econstructor; eauto;[].
exact (mkHeader 0).
  (* in this context, there is only one possible message *)
Defined.

Definition filterMegsByTopic (lm : list Message) 
  (topic : RosTopic) : list ( (topicType topic)) :=
flat_map (fun m => op2List (getPayLoad topic m)) lm.

Lemma moveMapInsideFst : forall tp lm,
  opBind (getPayLoad tp)  (head lm)
  = opBind (getPayLoadR tp) (head (map fst lm)).
Proof.
  intros ?. destruct lm; reflexivity.
Qed.


Definition PureProcWDelay (inT outT : RosTopic)
  := (topicType inT) -> list (Q * (topicType outT)).

Definition delayedLift2Mesg {InTopic OutTopic} 
  (f : PureProcWDelay InTopic OutTopic) 
   (inpMesg : Message) : (list Message) :=
  match (getPayLoad InTopic inpMesg ) with
  | Some tmesg => map (λ p, (mkDelayedMesg (π₁ p) (π₂ p))) (f tmesg)
  | None => nil
  end.


End RosCore.

