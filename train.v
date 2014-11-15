Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Add LoadPath "../../../nuprl/coq".

Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Instance stringdeceqdsjfklsajlk : DecEq string.
constructor. exact string_dec.
Defined.

Inductive Topic :=  MOTOR | PSENSOR.

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


Inductive Void :=.


(** When adding a nrew topic, add cases of this function *)
Definition topic2Type (t : Topic) : Type :=
match t with
| MOTOR => Q
| PSENSOR => bool
end.


Instance  ttttt : @RosTopicType Topic _.
  constructor. exact topic2Type.
Defined.

Inductive RosLoc := 
 BASEMOTOR | LEFTPSENSOR | RIGHTPSENSOR | SWCONTROLLER.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.


(** it is a pure function that repeatedly
   reads a message from the [PSENSOR] topic
   and publish on the [MOTOR] *)
Definition SwControllerProgram :
  SimplePureProcess PSENSOR MOTOR :=
fun side  => match side with
            | true => 0 - 1
            | false => 1
            end.

Definition SwProcess := 
  liftToMesg SwControllerProgram.

Definition digiControllerTiming : 
  ProcessTiming (SwProcess) :=
 fun m => (N2QTime 1).

Definition ControllerNodeAux : RosSwNode :=
  Build_RosSwNode digiControllerTiming.


 

Record TrainState := mkSt {
  posX : TimeFun;
  velX : TimeFun;
  deriv : isDerivativeOf velX posX
}.


Definition getVelM (m : Message ) : option Q :=
getPayLoad MOTOR m.


Section Train.

(** To define IO devices, we already need
    an Event type *)
Context  
  (minGap : Qpos)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


Definition ControllerNode :  @RosNode _ _ _ Event.
  constructor.
  - exact (Build_TopicInfo (PSENSOR::nil) (MOTOR::nil)).
  - left. exact ControllerNodeAux.
Defined.

(** In some cases, the equations might invove transcendental 
  functions like sine, cos which can output 
  irrationals even on rational *)


Definition getVel (e : Event) : option Q :=
match (eKind e) with
| deqEvt => getVelM (eMesg e)
| _ => None
end.



Definition getVelFromMsg (oev : option Event) : option Q  :=
(opBind getVel oev).

Definition getVelAndTime (oev : option Event) 
    : option (Q * QTime)  :=
match oev with
| Some ev => match getVel ev with
             | Some vq => Some (vq, eTime ev)
             | None => None
             end
| None => None
end.

Definition ProximitySensor (alertDist maxDelay: R) (side : bool)
  : @Device Event R :=
fun  (distanceAtTime : Time -> R)  
     (evs : nat -> option Event) 
    =>
      (forall t:Time,
       (distanceAtTime t  [>]  alertDist)
       -> exists n,
            match (evs n) with
            | Some ev => Cast (Q2R (eTime ev) [<] (t [+] maxDelay)) 
                  /\ isSendOnTopic PSENSOR (fun b => b = side) ev
            | None => False
            end).


Definition inIntervalDuringInterval
  (interval intervalT: interval)  (f : Time -> R) : Prop
      :=
 Cast (forall t : Time, intervalT t  -> (interval) (f t)).
  
Require Export Coq.Unicode.Utf8.

Variable reactionTime : Q.
Variable velAccuracy : R.
Variable initialVel : Q.
Variable initialPos : Q.
Variable transitionValues : interval.
Definition correctVelDuring
  (lastVel : Q) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (velAtTime: Time -> R) :=
    exists  qt : QTime, 
      lastTime <= qt <= (lastTime + reactionTime)
      /\(inIntervalDuringInterval 
                          transitionValues
                          (clcr (Q2R lastTime) (Q2R qt))
                          velAtTime)
      /\ (inIntervalDuringInterval 
                          (nbdAround (Q2R lastVel) velAccuracy) 
                          (clcr  (Q2R qt) (Q2R uptoTime))
                          velAtTime).

Close Scope Q_scope.


(** let k geatest m much that m < n 
   and (evs m) is a velocity message.
   this returns the vlocity and time of (evs k) *)
Fixpoint lastVelAndTimeAux (evs : nat -> option Event) 
    (n : nat) : (Q * QTime):=
match n with
| 0 => (initialVel,N2QTime 0)
| S n' => match getVelAndTime (evs n') with
          | Some pr => pr
          | None => lastVelAndTimeAux evs n'
           end
end.
  

Definition lastVelAndTime (evs : nat -> option Event)
  (t : QTime) : (Q * QTime) :=
lastVelAndTimeAux evs (lastEvtIndex evs t) .


Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime) 
  (velAtTime: Time -> R) :=
  let (lastVel, lastTime) := lastVelAndTime evs uptoTime in
  correctVelDuring lastVel lastTime uptoTime velAtTime.


Definition SlowMotorQ 
   : @Device Event R :=
fun  (velAtTime: Time -> R) (evs : nat -> option Event) 
  => forall t: QTime, corrSinceLastVel evs t velAtTime.


Variable boundary : R.

Definition rboundary : R := (boundary).
Definition lboundary : R := ([0] [-] boundary).

Variable alertDist : R.
Variable safeDist : R.
Variable maxDelay : R.
Variable hwidth : R. (* half of width *)

Open Scope Q_scope.

Variable reactionTimeGap : reactionTime < minGap.
Definition lEndPos (ts : TrainState) (t : Time) : R :=
(getF (posX ts) t [-]  hwidth).

Definition transitionInterval : interval :=
(clcr ([0] [-] [1]) [1]).


Definition rEndPos (ts : TrainState) (t : Time) : R :=
(getF (posX ts) t [+]  hwidth).

Definition locNode (rl : RosLoc) : RosNode :=
match rl with
| BASEMOTOR =>
     {| topicInf:=
        (Build_TopicInfo (MOTOR::nil) nil);
        rnode := (inr  (existT  _ _ 
                (SlowMotorQ))) |}
| LEFTPSENSOR => 
     {| topicInf:=
          (Build_TopicInfo nil (PSENSOR::nil));
           rnode := (inr  (existT  _ _ 
               (ProximitySensor alertDist maxDelay true)))|}
| RIGHTPSENSOR => 
     {| topicInf:=
          (Build_TopicInfo nil (PSENSOR::nil));
           rnode := (inr  (existT  _ _ 
               (ProximitySensor alertDist maxDelay false)))|}

| SWCONTROLLER => ControllerNode
end.

Instance rllllfjkfhsdakfsdakh : 
   @RosLocType _ _ _ Event TrainState RosLoc _.
apply (Build_RosLocType _ _ _ 
         locNode (fun srs dest => Some (N2QTime 1))).
 intros ts rl. remember rl as rll. destruct rll; simpl; try (exact tt);
  unfold TimeValuedPhysQType; simpl.
  - exact (getF (velX ts)).
  - intro t. exact (AbsIR ((lEndPos ts t) [-] lboundary)).
  - intro t. exact (AbsIR ((rEndPos ts t) [-] rboundary)).
Defined.

Open Scope R_scope.

Variable tstate : TrainState.
Variable eo : (@PossibleEventOrder _  tstate minGap _ _ _ _ _ _ _ _ _).

Definition  TrainSpec (t:Time) : Prop :=
    ((lEndPos tstate t) [-] safeDist [>=] lboundary )
    /\((rEndPos tstate t) [+] safeDist [<=] rboundary ).

Definition motorEvents : nat -> option Event 
   := localEvts BASEMOTOR.

(** if there is no next event, then it holds forever *)

Lemma velMessages : 
  forall n : nat,
     match getVelFromMsg (motorEvents n) with
     | Some v => v = 1 \/ v = (0-1)
     | None => False
     end.
Abort.
  

Close Scope R_scope.
Close Scope Q_scope.
Add LoadPath "../../../nuprl/coq".
Require Import UsefulTypes.
(* Close Scope NupCoqScope. *)



Open Scope R_scope.
Close Scope Q_scope.




End Train.

(** To begin with, let the VelControl device control position
    make it exact if needed *)

(** need to add sequence numbers in timer messages and keep
    track of it in the controller sw *)

(** N2R commuted with addition *)
