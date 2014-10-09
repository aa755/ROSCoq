Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export core.


(*
Class RosMesgType (T : Type) {unm: UniqueNames T} := {
    payLoadType : T -> Type
}.
  {unm : UniqueNames MT}
  {rmt : RosMesgType MT}
    masterAndName : RT -> TCP * string;
    rtInj : InjectiveFun masterAndName;
  {deqtcp : DecEq TCP}
  {tcpad : TCPAddressType TCP} 

Class TCPAddressType (T : Type) {deq : DecEq T}:= {
}.

*)

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

Variable RosTopic : Type.
Variable tdeq : DecEq RosTopic.
Variable rtopic : @RosTopicType RosTopic _.

Inductive Message :=
| topicM :  forall (r :RosTopic), topicType r -> Message.
(* string could be rrplaced by a list bool to indicate a binary blob *)


Require Export Process.

Definition ProcessTiming 
  (p : Process Message (list Message)) :=
  forall (m: Message),
    {tl : list Time | length tl = length (getOutput p m) }.



Record RosSwNode :=
{
    process :> Process Message (list Message);

(* 
    privateTopic : RosTopic;

    subscribedTopics : list RosTopic;
    publishTopics : list RosTopic;

    need to ensure that when processes are give
    inputs in topics [subscribedTopics] the outputs
    are only in [publishTopics].
    the implementation subscribes to these topics
*)

    (** The following is only for reasoning purposes
      and will not be extracted *)

    pTiming : ProcessTiming process
  
}.

(** There is no code to extract for devices
    These are here to model environment *)

Record RosInpDevNode (Env : Type) :=
{
  (*  IDnodeName : string; *)
    outTopic : RosTopic; 
    idev :> InpDev Env  (topicType outTopic)
}.

Definition makeTopicMesg {outTopic : RosTopic}
  (payload : ( (topicType outTopic))) : Message.
econstructor; eauto. 
  (* in this context, there is only one possible message *)
Defined.

Definition substIDev {Env : Type} (rid : RosInpDevNode Env)
  (newd : InpDev Env ((topicType (outTopic rid))))
  : RosInpDevNode Env :=
Build_RosInpDevNode 
                    (outTopic rid)
                    newd.


Record RosOutDevNode (Env : Type) :=
{
    (* ODMasterAddress : TCPAddress;
    ODnodeName : string; *)
    inpTopic : RosTopic;
    odev :> OutDev Env ((topicType inpTopic))
}.


  
(** Implementing this will need simplification of topic definitions.
  We need decidable equality on topics, which is not currently true.
  Also, one could have 2 topics with same string name and different
  payload types

 *)
Definition transport {T:Type} {a b:T} {P:T -> Type} (eq:a=b) (pa: P a) : (P b):=
@eq_rect T a P pa b eq.


Definition getPayLoad  (topic : RosTopic) (m : Message) :
list ( (topicType topic)) :=
match m with
| topicM tp pl => match (eqdec  tp topic) with
                  | left peq =>  @transport _ _ _ (fun tpp => list ( (topicType tpp))) peq (pl::nil) 
                  | right _ => nil
                  end
end.


Definition filterMegsByTopic (lm : list Message) 
  (topic : RosTopic) : list ( (topicType topic)) :=
flat_map (getPayLoad topic) lm.


  
Definition getRosOutDevBhv  {Env : Type}
    (p: RosOutDevNode Env )
    (allInputs : list Message)  : OutDevBehaviour Env :=
    let filterMsgs := filterMegsByTopic allInputs (inpTopic p) in
    match filterMsgs with
    | nil => fst (odev p)
    | last :: rest => getLastOutput (snd (odev p)) rest last
    end.

Set Implicit Arguments.

Inductive RosNode : Type := 
| rsw : RosSwNode -> RosNode
| rhi : forall {Env : Type}, 
        RosInpDevNode Env -> RosNode
| rho : forall {Env : Type}, 
        RosOutDevNode Env -> RosNode.

Open Scope list_scope.
End RosCore.

(*
Definition IncomingTopics  (rn : RosNode) : list RosTopic
  :=
match rn with
| rsw rsn => subscribedTopics rsn
| rhi _ _ => nil
| rho _ rout =>  cons (inpTopic rout) nil
end.
*)
