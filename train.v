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

Definition nextInterval (tstart : QTime) 
    (nextMesgTime : option QTime) : interval :=
match nextMesgTime with
| Some tm => clcr (QT2R tstart) (QT2R tm)
| None => closel (QT2R tstart)
end.


Definition nbdAround ( radius center : R) :=
clcr (radius [-] center) (radius [+] center).

Definition SlowMotorQ 
  (reactionTime : Q) (accuracy : R)
  (transitionValues : interval)
   : @Device Event R :=
fun  (velAtTime: Time -> R) (evs : nat -> option Event) 
  => (forall n:nat,
          let ovn := getVelFromMsg (evs n) in
          let otn := option_map eTime (evs n) in
          let otsn := option_map eTime (evs (S n)) in
          match (ovn, otn) with
          | (Some vn, Some tn) => exists  qt : QTime,
              let Tintvl := nextInterval qt otsn in
              tn < qt 
              /\ qt < tn + reactionTime 
              /\ (inIntervalDuringInterval 
                          transitionValues
                          (clcr (Q2R tn) (Q2R qt))
                          velAtTime)
              /\ (inIntervalDuringInterval 
                          (nbdAround (Q2R vn) accuracy) 
                          Tintvl
                          velAtTime)
          | _ => True
          end).

Variable boundary : R.

Definition rboundary : R := (boundary).
Definition lboundary : R := ([0] [-] boundary).

Variable reactionTime : Q.
Variable alertDist : R.
Variable safeDist : R.
Variable maxDelay : R.
Variable velAccuracy : R.
Variable hwidth : R. (* half of width *)

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
                (SlowMotorQ reactionTime velAccuracy transitionInterval))) |}
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
