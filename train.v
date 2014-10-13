Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Instance stringdeceqdsjfklsajlk : DecEq string.
constructor. exact string_dec.
Defined.

Open Scope string_scope.

Inductive Void :=.

(** When adding a nrew topic, add cases of this function *)
Definition stringTopic2Type (s : string) : Type :=
if (eqdec s "motorRecv") then Q else
if (eqdec s "timerSend") then nat else Void.


Instance  ttttt : @RosTopicType string _.
constructor. exact stringTopic2Type.
Defined.

Inductive RosLoc := baseMotor | timerNode | digiController.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.

CoFixpoint digiControllerProgram (state : bool): Process Message (list Message).
  constructor. intro m.
  destruct m as [topicName payLoad].
  case (eqdec topicName "timerSend"); intro Hc; subst.
  - split. 
    + exact (digiControllerProgram (negb state)).
    + apply cons;[ | exact nil]. exists "motorRecv".
      simpl. unfold stringTopic2Type. simpl.
      destruct state ;[exact 1 | exact (0-1)].
  - exact (digiControllerProgram state,nil).
Defined.


Definition digiControllerTiming : ProcessTiming (digiControllerProgram true) :=
 fun m => (N2T 1).

Definition ControllerNodeAux : RosSwNode :=
  Build_RosSwNode digiControllerTiming.

    


Section Train.
Context  
  (minGap : Qpos)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


Definition ControllerNode :  @RosNode _ _ _ Event.
  constructor.
  - exact (Build_TopicInfo ("timerSend"::nil) ("motorRecv"::nil)).
  - left. exact ControllerNodeAux.
Defined.

Definition TimerMesg (n : nat) : Message :=
  existT _ "timerSend" n.

Definition isTimerEvtNth (n : nat) (oe : option Event) : Prop :=
  match oe with
  | Some ev => (eKind ev) = sendEvt /\ (eMesg ev) = TimerMesg n
  | None => False
  end.


Definition TimerDev : @Device Event unit :=
  fun tp (evs : nat -> option Event) => forall n, isTimerEvtNth n (evs n).

Definition TimerNode :  @RosNode _ _ _ Event.
  constructor.
  - exact (Build_TopicInfo ("timerSend"::nil) nil).
  - right. exists unit. exact TimerDev.
Defined.

(** in some cases, the equations might invove transcendental 
  functions like sine, cose which can output 
  irrationals even on rational *)

Record TrainState := {
  posX : Q;
  velX : Q
}.

Definition getVelM (m : Message ) : option Q :=
match (eqdec (proj1_sigT _ _ m) "motorRecv") with
| _ => None
end.

Definition getVel (e : Event) : option Q :=
match (eKind e, eMesg e) with
| (deqEvt, existT "motorRecv" q) => None
| _ => None
end.


Definition TrainDev : @Device Event TrainState.
  intros tp evs.
  

(* Build_RosOutDevNode "motorRecv" VelOutDevice *)

Definition locNode (rl : RosLoc) : RosNode :=
match rl with
| baseMotor => ControllerNode
| timerNode => TimerNode
| digiController => BaseMotorNode
end.

Instance rllllfjkfhsdakfsdakh : RosLocType TrainState RosLoc.
apply (Build_RosLocType _ _ _ locNode (fun srs dest => Some t1)).
 intros ts rl. destruct rl; simpl; try (exact tt).
  - exact (fun t => tt).
  - exact (fun t => vX (ts t)).
Defined.

Context  (physics : Time -> TrainState).


Open Scope R_scope.

Section CorrProof.

Variable eo : (@PossibleEventOrder _  physics minGap _ _ _ _ _ _ _ _ _).

Definition  TrainSpec : Prop :=
  forall  (t:Time), ([0]  <= (posX (physics t)) <= [1]).

Definition timerEvts : nat -> option Event :=
localEvts timerNode.

Close Scope R_scope.
Close Scope Q_scope.
Add LoadPath "../../../nuprl/coq".
Require Import UsefulTypes.
Close Scope NupCoqScope.

Open Scope R_scope.
Close Scope Q_scope.


Lemma N2R_add_commute : forall (n1 n2 : nat),
  N2R n1 [+] N2R n2 = N2R (n1 + n2).
Admitted.



Lemma timerEventsSpec : forall n:nat,  
match timerEvts n with
| Some ev  => ( realV _ (eTime ev) =  (N2R (S n)))
| _ => False 
end.
Proof.
  intro n. simpl. 
  (* remember (timerEvts n) as tn.
  remember (timerEvts (S n)) as tsn. *)
  pose proof (corr eo) as Hc.
  destruct Hc as [Hcl Hcr].
  specialize (Hcr timerNode).
  unfold NodeBehCorrect in Hcr. simpl in Hcr.
  induction n as [| n' Hind].
  - specialize (Hcr 1).
    unfold InpDevBehaviourCorrectAux in Hcr.
    simpl in Hcr. unfold nextMessageAtTime in  Hcr.
    rewrite prevEventsIndex0 in Hcr.
    fold timerEvts in Hcr. 
    unfold ConjL in Hcr. destruct (timerEvts 0); simpl in Hcr; [| repnd; contradiction].
    repnd. rewrite Hcr1. unfold N2R. apply N2R_add_commute.
  - specialize (Hcr (S(S n'))). unfold InpDevBehaviourCorrectAux in Hcr.
    simpl in Hcr. unfold nextMessageAtTime in  Hcr.
    rewrite prevEventsIndex0 in Hcr.
    fold timerEvts in Hcr. 


  - specialize (Hcr (S (S n'))).
    unfold InpDevBehaviourCorrectAux in Hcr.
    simpl in Hcr. unfold nextMessageAtTime in  Hcr.
    rewrite prevEventsIndex0 in Hcr.
    fold timerEvts in Hcr. rewrite <- Heqtn in Hcr.
    unfold ConjL in Hcr. destruct tn; simpl in Hcr; [| repnd; contradiction].
    repnd. admit.
Admitted.


End CorrProof.

(** To begin with, let the VelControl device control position
    make it exact if needed *)

(** need to add sequence numbers in timer messages and keep
    track of it in the controller sw *)

(** N2R commuted with addition *)
