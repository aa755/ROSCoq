Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)

Require Export ROSCyberPhysicalSystem.
Require Export Vector.

Definition isVecDerivativeOf 
    {n : nat} (f f' : Vector n TContR) : Type.
  revert f f'.
  induction n as [| np Hind]; intros f f';[exact unit|].
  destruct f as [fv ft].
  destruct f' as [fv' ft'].
  exact ((isDerivativeOf ft ft') × (Hind fv fv')).
Defined.

(** CatchFileBetweenTagsStartCreate *)

Record iCreate : Type := {
  position :> Vector 2 TContR;          (* x, y co-ordinates *)
  theta : TContR;                       (* orientation *)
  transVel : Vector 2 TContR;             (* x, y velocity of center *)
  omega : TContR;

  derivRot : isDerivativeOf omega theta;
  derivTrans : isVecDerivativeOf transVel position
}.

(** CatchFileBetweenTagsEndCreate *)


Inductive Topic :=  VELOCITY. (* similar to CMD_VEL *)

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


(** When adding a nrew topic, add cases of this function *)
Definition topic2Type (t : Topic) : Type :=
match t with
| MOTORVEL => (Q × Q)
end.


Instance  ttttt : @RosTopicType Topic _.
  constructor. exact topic2Type.
Defined.

Inductive RosLoc :=  MOVABLEBASE.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.

Close Scope Q_scope.


Definition getVelM  : Message -> option (Q × Q) :=
  getPayLoad VELOCITY.


Section iCREATECPS.

(** To define IO devices, we already need
    an Event type *)
Context  
  (minGap : Q)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


(** In some cases, the equations might invove transcendental 
  functions like sine, cos which can output 
  irrationals even on rational *)



Definition getVelEv (e : Event) : option (Q × Q)  :=
  getPayloadFromEv VELOCITY e.

Definition getVelOEv : (option Event) ->  option (Q × Q)  :=
getPayloadFromEvOp VELOCITY.


Definition getVelAndTime (oev : option Event) 
    : option ((Q × Q) * Event)  :=
getPayloadAndEv VELOCITY oev.


Definition inIntervalDuring
  (interval: interval) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  Cast (forall t : QTime, ( tStart <= t <= tEnd   -> (interval) (f t)))%Q.
  
Definition isEqualDuring
  (vel: Q) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  (forall t : QTime, ( tStart <= t <= tEnd   -> (f t) [=] vel))%Q.

Variable reactionTime : Q.
Variable velAccuracy : Q.
Variable transitionValues : interval.


  
Close Scope Q_scope.


(** all velocity messages whose index  < numPrevEvts .
    the second item is the time that messsage was dequed.
    last message, if any  is the outermost (head)
    Even though just the last message is needed,
    this list is handy for reasoning; it is a convenient
    thing to do induction over
 *)

Definition velocityMessages (t : QTime) :=
  (filterPayloadsUptoTime VELOCITY (localEvts MOVABLEBASE) t).

Variable initialVel : (Q × Q).
Variable initialPos : Q.

Definition lastVelAndTime
  (t : QTime) : ((Q × Q) * QTime) :=
  lastPayloadAndTime VELOCITY (localEvts MOVABLEBASE) t initialVel.

Definition changesTo (f : TContR)
  (atTime uptoTime : QTime)
  (toValue : ℝ)
  (reactionTime eps : Q) :=
(exists  (qt : QTime), 
  atTime <= qt <= (atTime + reactionTime)
  /\ ((forall t : QTime, 
          (qt <= t <= uptoTime -> AbsIR ({f} t [-] toValue) [<=] eps)))
  /\ (forall t : QTime, (atTime <= t <= qt)  
          -> (between ({f} t) ({f} atTime) toValue)))%Q.
  
Definition correctVelDuring
  (lastVelCms : (Q × Q)) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (velAtTime: Time -> ℝ) :=


Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime)
  (velAtTime: Time -> ℝ) :=
  let (lastVel, lastTime) := lastVelAndTime uptoTime in
  correctVelDuring lastVel lastTime uptoTime velAtTime.


Definition SlowMotorQ 
   : Device ℝ :=
fun  (velAtTime: Time -> ℝ) (evs : nat -> option Event) 
  => forall t: QTime, corrSinceLastVel evs t velAtTime.

*)

End iCREATECPS.
