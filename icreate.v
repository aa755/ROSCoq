Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)
(** printing ≡ $\equiv$ #≡# *)
(** printing [*] $*$ #*# *)
(** printing ∧ $\wedge$ #∧# *)
(** printing ∀ $\forall$ #∀# *)
(** printing → $\rightarrow$ #→# *)
(** printing ∃ $\exists$ #∃# *)
(** printing ≤ $\le$ #≤# *)
(** printing θ $\theta$ #θ# *)
(** printing eeev $\epsilon_v$ #∊ᵥ# *)
(** printing eeew $\epsilon_w$ #∊w# *)
(** printing tm $t_m$ #tm# *)
(** printing IR $\mathbb{R}$ #IR# *)
(** printing CR $\mathbb{R}$ #CR# *)
(** printing tr $t_r$ #tr# *)
(** printing θErrTurn $\theta ErrTurn$ #θErrTurn# *)
(** remove printing * *)
(** printing θErrTrans $\theta ErrTrans$ #θErrTrans# *)
(** printing polarθSign $polar \theta Sign$ #polarθSign# *)
(** printing idealθ $ideal \theta$ #idealθ# *)

(** printing ' $ $ #'# *)

Require Export Vector.
Require Export ROSCyberPhysicalSystem.

Require Export MathClasses.interfaces.canonical_names.
Require Export MCInstances.
Require Export CartCR.

Definition initialVel : (Polar2D Q) := {|rad:=0; θ:=0|}.

Require Export CartIR.


Notation FConst := ConstTContR.
Notation FSin:= CFSine.
Notation FCos:= CFCos.


Record iCreate : Type := {
  position :> Cart2D TContR;          (* x, y co-ordinates*)
  theta : TContR;                       (* orientation *)
  transVel : TContR;             (* translation vel (along [theta]) *)
  omega : TContR;

  (** derivatives *)
  derivRot : isDerivativeOf omega theta;
  derivX : isDerivativeOf (transVel * (FCos theta)) (X position);
  derivY : isDerivativeOf (transVel * (FSin theta)) (Y position);

  (** Initial (at time:=0) Conditions *)  

  initPos:  ({X position} 0) ≡ 0 ∧ ({Y position} 0) ≡ 0;
  initTheta:  ({theta} 0) ≡ 0;
  initTransVel : ({transVel} 0) ≡ (rad initialVel);
  initOmega : ({omega} 0) ≡ (θ initialVel)
}.



(** Robot is asked to go to the  [target] relative to current position.
    This function defines the list of messages that the robot will send to
    the motor so that it will go to the target position.
    [X] axis of target points towards the direction that robot will move
    and [Y] points to its left side. it might be better to make Y
    point in robot's direction. Then add 90 in cartesian <-> polar conversion. *)


Section HardwareAgents.

Context 
  `{rtopic : RosTopicType RosTopic} 
  `{dteq : Deq RosTopic}
  `{etype : @EventType _ _ _ Event LocT minGap tdeq}.
  
Variable VELOCITY : RosTopic.
Hypothesis VelTOPICType : (topicType VELOCITY ≡ Polar2D Q).

(*
Definition getVelM   (m: Message) : option (Polar2D Q) :=
  transport VelTOPICType (getPayload VELOCITY m).


Definition getVelEv (e : Event) : option (Polar2D Q)  :=
  getRecdPayload VELOCITY e.

Definition getVelOEv : (option Event) ->  option (Polar2D Q)  :=
getRecdPayloadOp VELOCITY.

Definition getVelAndTime (oev : option Event) 
    : option ((Polar2D Q) * Event)  :=
  getPayloadAndEv VELOCITY oev.


Definition inIntervalDuring
  (interval: interval) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  Squash (forall t : QTime, ( tStart <= t <= tEnd   -> (interval) (f t)))%Q.
  
Definition isEqualDuring
  (vel: Q) (tStart tEnd : QTime)  (f : Time -> ℝ) : Prop :=
  (forall t : QTime, ( tStart <= t <= tEnd   -> (f t) [=] vel))%Q.
*)

Variable reacTime : QTime.
(** It is more sensible to change the type to [QNonNeg]
    as the value certainly does not represent time.
    However, the coercion QT2Q does not work then *)
Variable motorPrec : Polar2D Q → Polar2D QTime.

Hypothesis motorPrec0 : motorPrec {| rad :=0 ; θ :=0 |} ≡ {| rad :=0 ; θ :=0 |}.
  
Close Scope Q_scope.


(*
Definition velocityMessages (t : QTime) :=
  (filterPayloadsUptoTime VELOCITY (localEvts MOVABLEBASE) t).
*)

Definition latestVelPayloadAndTime
  (evs : nat -> option Event) (t : QTime) : ((Polar2D Q) × QTime) :=
(@transport _ _ _ (λ t, t -> t ** QTime) VelTOPICType 
   (lastPayloadAndTime VELOCITY evs t)) initialVel.



Definition correctVelDuring
  (lastVelCmd : (Polar2D Q)) 
  (lastTime: QTime)
  (uptoTime : QTime) 
  (robot: iCreate) :=

  changesTo 
    (transVel robot) 
    lastTime uptoTime 
    (rad lastVelCmd) 
    reacTime 
    (rad  (motorPrec lastVelCmd))
  ∧ 
  changesTo 
    (omega robot) 
    lastTime uptoTime 
    (θ lastVelCmd) 
    reacTime 
    (θ (motorPrec lastVelCmd)).

Definition corrSinceLastVel
  (evs : nat -> option Event)
  (uptoTime : QTime)
  (robot: iCreate) :=
let (lastVel, lastTime) := latestVelPayloadAndTime evs uptoTime in
correctVelDuring lastVel lastTime uptoTime robot.


Definition HwAgent  : Device iCreate :=
λ (robot: iCreate) (evs : nat -> option Event) ,
  (∀ t: QTime, corrSinceLastVel evs t robot)
  ∧ ∀ n:nat, isDeqEvtOp (evs n).

(* move to ROSCps*)
Definition onlyRecvEvts (evs : nat -> option Event) : Prop :=
∀ n:nat, isDeqEvtOp (evs n).

(* delete the next 2 definitions *)
Definition eeev  a b : Q  :=
 (rad (motorPrec {|rad:= a; θ:= b|})).

Definition eeew  a b : Q :=
 (θ (motorPrec {|rad:= a; θ:= b|})).

(** partial simplified definition shown in the paper : *)
Definition HwAgentP (ic: iCreate) (evs : nat -> option Event): Prop :=
onlyRecvEvts evs ∧ ∀ t: QTime,
  let (lastCmd, tm ) := latestVelPayloadAndTime evs t in 
  let a : Q := rad (lastCmd) in
  let b : Q := θ (lastCmd) in
  ∃ tr : QTime, (tm ≤ tr ≤ tm + reacTime)
    ∧ (∀ t' : QTime, (tm ≤ t' ≤ tr) 
        → (Min ({transVel ic} tm) (a - eeev a b) 
            ≤ {transVel ic} t' ≤ Max ({transVel ic} tm) (a+ eeev a b)))
    ∧ (∀ t' : QTime, (tr ≤ t' ≤ t) → |{transVel ic} t' - a | ≤ Q2R (eeev a b)).

Lemma HwAgentPCorr1 :
  ∀ icr evs,
  HwAgent icr evs ->  HwAgentP icr evs.
Proof.
  intros ? ? H.
  destruct H as [Hr H].
  split; [assumption|]. clear H.
  intros t.
  specialize (Hr t).
  unfold corrSinceLastVel in Hr.
  destruct (latestVelPayloadAndTime evs t) as [lc lt].
  apply proj1 in Hr.
  destruct Hr as [qtrans Hr].
  exists qtrans.
  unfold le, Le_instance_QTime.
  autounfold with IRMC. unfold Plus_instance_QTime.
  unfoldMC. repnd.
  split; auto.
  unfold eeev.
  destruct lc.
  simpl Vector.rad.
  simpl Vector.rad in Hrrl, Hrrr.
  unfold Q2R. setoid_rewrite inj_Q_inv.
  split; auto.
  unfold between, Q2R in Hrrr.
  intros ? H.
  apply Hrrr in H.
  autorewrite with QSimpl in H.
  exact H.
Qed.
End HardwareAgents.
