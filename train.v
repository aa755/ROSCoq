
Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Require Export ROSCyberPhysicalSystem.
Require Export String.
Require Export trainDevs.
(* Require Export CoRN.ode.SimpleIntegration. *)

Instance stringdeceqdsjfklsajlk : DecEq string.
constructor. exact string_dec.
Defined.

Open Scope string_scope.

Inductive Void :=.

(** When adding a nrew topic, add cases of this function *)
Definition stringTopic2Type (s : string) : Type :=
if (eqdec s "motorRecv") then Q else
if (eqdec s "timerSend") then unit else Void.


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

Definition t1 : Time.
exists [1]. unfold iprop.
eauto with *.
Defined.

Definition digiControllerTiming : ProcessTiming (digiControllerProgram true) :=
 fun m => t1.


Definition ControllerNode : RosSwNode :=
Build_RosSwNode ("timerSend"::nil) ("motorRecv"::nil) digiControllerTiming.

Definition TimerNode : RosInpDevNode unit:=
Build_RosInpDevNode "timerSend" (Timer 1).

Definition BaseMotorNode : RosOutDevNode R :=
(Build_RosOutDevNode "motorRecv" VelOutDevice).

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

Section Train.
Context  
  (physics : Time -> TrainState)
  (minGap : RPos)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq }.

Open Scope R_scope.

Section CorrProof.

Variable eo : (@PossibleEventOrder _  physics minGap _ _ _ _ _ _ _ _ _).

Definition  TrainSpec : Prop :=
  forall  (t:Time), ([0]  <= (posX (physics t)) <= [1]).

Definition timerEvts : nat -> option Event :=
localEvts timerNode.

(* Add LoadPath "../../../nuprl/coq". *)

Close Scope R_scope.
Close Scope Q_scope.
Lemma timerEventsSpec : forall n:nat,  
match timerEvts n with
| Some ev  => ( realV _ (eTime ev) =  (N2R (S n)))
| _ => False 
end.
Proof.
  intro n. simpl. remember (timerEvts n) as tn.
  remember (timerEvts (S n)) as tsn.
  pose proof (corr eo) as Hc.
  destruct Hc as [Hcl Hcr].
  specialize (Hcr timerNode).
  unfold NodeBehCorrect in Hcr. simpl in Hcr.
    induction n as [| n' Hind].
  - specialize (Hcr 1).
    unfold InpDevBehaviourCorrectAux in Hcr.
    simpl in Hcr. unfold nextMessageAtTime in  Hcr.
    rewrite prevEventsIndex0 in Hcr.
    fold timerEvts in Hcr. rewrite <- Heqtn in Hcr.
    unfold ConjL in Hcr. destruct tn; simpl in Hcr; try tauto.
    
Admitted.


End CorrProof.

(** To begin with, let the VelControl device control position
    make it exact if needed *)

(** need to add sequence numbers in timer messages and keep
    track of it in the controller sw *)

(** N2R commuted with addition *)
