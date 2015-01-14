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

(* 
  Axiom TCRing : TContR -> CRing.
  Coercion TCRing :  TContR >-> CRing. *)


(** CatchFileBetweenTagsStartCreate *)

Record iCreate : Type := {
  position :> Vec2D TContR;          (* x, y co-ordinates*)
  theta : TContR;                       (* orientation *)
  transVel : TContR;             (* translation vel (along orientation), can be negative *)
  omega : TContR;

  derivRot : isDerivativeOf omega theta;
  derivX : isDerivativeOf (transVel [*] (CFCos theta)) (X position);
  derivY : isDerivativeOf (transVel [*] (CFSine theta)) (Y position)
}.

(** CatchFileBetweenTagsEndCreate *)


Definition unitVec (theta : TContR)  : Vec2D TContR :=
  {|X:= CFCos theta; Y:=CFSine theta|}.


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

Variable reacTime : Q.
Variable tVelPrec : Q.
Variable omegaPrec : Q.


  
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
  (t : QTime) : ((Q × Q) × QTime) :=
  lastPayloadAndTime VELOCITY (localEvts MOVABLEBASE) t initialVel.

Definition correctVelDuring
  (lastVelCmd : (Q × Q)) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (robot: iCreate) :=

changesTo (transVel robot) lastTime uptoTime (π₁ lastVelCmd) reacTime tVelPrec 
∧ changesTo (omega robot) lastTime uptoTime (π₂ lastVelCmd) reacTime omegaPrec.


Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime)
  (robot: iCreate) :=
let (lastVel, lastTime) := lastVelAndTime uptoTime in
correctVelDuring lastVel lastTime uptoTime robot.


Definition BaseMotors  : Device iCreate :=
fun  (robot: iCreate) (evs : nat -> option Event) 
  => forall t: QTime, corrSinceLastVel evs t robot.

(** It would be quite complicated to maintain bounds on position when both
    [omega] and [speed] are nonzero. derivative on [X position] depends on
    all of [speed] and [theta] and [omega] *)

Require Export CoRN.ftc.IntegrationRules.

(*
Lemma TBarrowPos : forall rob (a b : Time),
       CIntegral a b ((transVel rob) [*] CFCos (theta rob)) 
       [=] {X (position rob)} b [-] {X (position rob)} a.
  intros. apply TBarrow with (pItvl := I).
  apply derivX.
Qed.
*)
(** The integral is too complicated for the general case. Handle the
    case we want in the application. Given a rough estimate of current
    position (received by Vicon )and an idea about the goal, what
    message should we send to iCreate? what can we prove
    about how the robot will react to that message? *)


(** for rotation, it is easy. for the change of position, we can bound
    Cos and Sin by 1 and hence the maximal change in X/Y coordinate per second
      is [tVelPrec] *)

(** For translation. things are complicated. Ideally, done in the frame from
    robot's position which is still not well known, such that the Y axis is
    in the direction of the target. *)

(** It seems that [CoRN.ftc.IntegrationRules.IntegrationBySubstition] would be
    useful. however, the head of the integral is a multiplication and only then
    we have a composition in the RHS of the multiplication *)
End iCREATECPS.
