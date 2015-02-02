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
  position :> Cart2D TContR;          (* x, y co-ordinates*)
  theta : TContR;                       (* orientation *)
  transVel : TContR;             (* translation vel (along orientation), can be negative *)
  omega : TContR;

  derivRot : isDerivativeOf omega theta;
  derivX : isDerivativeOf (transVel [*] (CFCos theta)) (X position);
  derivY : isDerivativeOf (transVel [*] (CFSine theta)) (Y position)
}.

(** CatchFileBetweenTagsEndCreate *)


Definition unitVec (theta : TContR)  : Cart2D TContR :=
  {|X:= CFCos theta; Y:=CFSine theta|}.


Require Export CartCR.
(** Robot is asked to go to the  [target] relative to current position.
    This function defines the list of messages that the robot will send to
    the motor so that it will go to the target position.
    [X] axis of target points towards the direction that robot will move
    and [Y] points to its left side. it might be better to make Y
    point in robot's direction. Then add 90 in cartesian <-> polar conversion. *)

Section RobotProgam.
Variables   rotspeed speed anglePrec distPrec delay : Qpos.

Definition robotPureProgam 
      (target : Cart2D Q) : list (Q × Polar2D Q):=
    let polarTarget : Polar2D CR := Cart2Polar target in
    let approxTheta : Q := approximate (θ polarTarget) anglePrec in
    let approxDist : Q := approximate (rad polarTarget) distPrec in
    let rotDuration : Q :=  approxTheta / (QposAsQ rotspeed) in
    let translDuration : Q :=  approxDist / (QposAsQ speed) in
    [ (0,{|rad:= 0 ; θ := QposAsQ rotspeed |}) 
        ; (rotDuration, {|rad:= 0 ; θ := 0 |}) 
        ; (QposAsQ delay , {|rad:= QposAsQ speed ; θ := 0 |}) 
        ; (translDuration , {|rad:= 0 ; θ := 0 |}) 
    ].


Inductive Topic :=  VELOCITY | TARGETPOS. (* similar to CMD_VEL *)

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


(** When adding a nrew topic, add cases of this function *)
Definition topic2Type (t : Topic) : Type :=
match t with
| VELOCITY => Polar2D Q
| TARGETPOS => Cart2D Q 
end.


Instance  ttttt : @RosTopicType Topic _.
  constructor. exact topic2Type.
Defined.

Inductive RosLoc :=  MOVABLEBASE | EXTERNALCMD | SWNODE.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
  constructor. exact RosLoc_eq_dec.
Defined.

Close Scope Q_scope.


Definition getVelM  : Message -> option (Polar2D Q) :=
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



Definition getVelEv (e : Event) : option (Polar2D Q)  :=
  getPayloadFromEv VELOCITY e.

Definition getVelOEv : (option Event) ->  option (Polar2D Q)  :=
getPayloadFromEvOp VELOCITY.


Definition getVelAndTime (oev : option Event) 
    : option ((Polar2D Q) * Event)  :=
  getPayloadAndEv VELOCITY oev.


Definition inIntervalDuring
  (interval: interval) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  Squash (forall t : QTime, ( tStart <= t <= tEnd   -> (interval) (f t)))%Q.
  
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

Variable initialVel : (Polar2D Q).
Variable initialPos : Q.

Definition lastVelAndTime
  (t : QTime) : ((Polar2D Q) × QTime) :=
  lastPayloadAndTime VELOCITY (localEvts MOVABLEBASE) t initialVel.

Definition correctVelDuring
  (lastVelCmd : (Polar2D Q)) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (robot: iCreate) :=

changesTo (transVel robot) lastTime uptoTime (rad lastVelCmd) reacTime tVelPrec 
∧ changesTo (omega robot) lastTime uptoTime (θ lastVelCmd) reacTime omegaPrec.
(** TODO : second bit of conjunction is incorrect it will force the
   orientation in [iCreate] to jump from [2π] to [0] while turning.
   changes_to is based on a notion of distance or norm. we need to generalize 
    it to use the norm typeclass and then define appropriate notion for distance
    for angles*)

Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime)
  (robot: iCreate) :=
let (lastVel, lastTime) := lastVelAndTime uptoTime in
correctVelDuring lastVel lastTime uptoTime robot.


Definition BaseMotors  : Device iCreate :=
λ (robot: iCreate) (evs : nat -> option Event) ,
  (∀ t: QTime, corrSinceLastVel evs t robot).



Definition PureSwProc (speed: Qpos):
  PureProcWDelay TARGETPOS VELOCITY:=
  robotPureProgam.


(** The software could reply back to the the external agent saying "done".
    Then the s/w will output messages to two different topics
    In that case, change the [SWNODE] claue *)
Definition locTopics (rl : RosLoc) : TopicInfo :=
match rl with
| MOVABLEBASE => ((VELOCITY::nil), nil)
| SWNODE => ((TARGETPOS::nil), (VELOCITY::nil))
| EXTERNALCMD => (nil, (TARGETPOS::nil))
end.

Instance Equiv_instance_event : Equiv Event := eq.
Instance Equiv_instance_option_event : Equiv (option Event) := eq.
Instance Equiv_instance_option_message : Equiv (option Message) := eq.

Variable targetPos : Cart2D Q.

(** 10 should be replaced by something which is a function of 
    velocity accuracy, angle accuracy, max velocity etc *)
Definition externalCmdSemantics {Phys : Type} 
 : @NodeSemantics Phys Event :=
  λ _ evs , ∀ n, match n with
                 | 0 => {m : Message | isSendEvtOp (evs n) (*∧
                                      getPayLoad
                                          TARGETPOS
                                          m
                                      = (Some targetPos) *)} 
                 | S _ => evs n = None
                 end.


Definition locNode (rl : RosLoc) : NodeSemantics :=
match rl with
| MOVABLEBASE => DeviceSemantics (λ ts,  ts) BaseMotors
| SWNODE => DeviceSemantics (λ ts,  ts) BaseMotors (* FIX *)
| EXTERNALCMD  => externalCmdSemantics
end.

Instance rllllfjkfhsdakfsdakh : @RosLocType iCreate Topic Event  RosLoc _.
  apply Build_RosLocType.
  - exact locNode.
  - exact locTopics.
  - exact (fun srs dest => Some (mkQTime 1 I)).
Defined.


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
End RobotProgam.
