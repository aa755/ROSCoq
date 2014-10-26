Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.
Add LoadPath "../../../nuprl/coq".

Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Instance stringdeceqdsjfklsajlk : DecEq string.
constructor. exact string_dec.
Defined.

Inductive Topic :=  motorRecv | timerSend.

Scheme Equality for Topic.

Instance ldskflskdalfkTopic_eq_dec : DecEq Topic.
constructor. exact Topic_eq_dec.
Defined.


Inductive Void :=.


(** When adding a nrew topic, add cases of this function *)
Definition stringTopic2Type (t : Topic) : Type :=
match t with
| motorRecv => Q
| timerSend => ( bool)%type
end.


Instance  ttttt : @RosTopicType Topic _.
  constructor. exact stringTopic2Type.
Defined.

Inductive RosLoc := baseMotor | leftProximity | rightProximity | digiController.

Scheme Equality for RosLoc.

Instance rldeqdsjfklsajlk : DecEq RosLoc.
constructor. exact RosLoc_eq_dec.
Defined.

(*
CoFixpoint digiControllerProgram : Process Message (list Message).
  constructor. intro m.
  destruct m as [topicName payLoad]. 
  destruct topicName; simpl.
  - split.
    + exact (digiControllerProgram).
    + apply cons;[ | exact nil]. exists motorRecv.
      simpl. unfold stringTopic2Type. simpl.
      destruct state ;[exact 1 | exact (0-1)].
  - exact (digiControllerProgram state,nil).
Defined.


Definition digiControllerTiming : ProcessTiming (digiControllerProgram true) :=
 fun m => (N2T 1).

Definition ControllerNodeAux : RosSwNode :=
  Build_RosSwNode digiControllerTiming.

*)

Require Export CoRN.ftc.Derivative.   
Record TrainState := mkSt {
  posX : IR;
  velX : IR
}.

Definition initialState : TrainState := (mkSt 3 0).
 
Definition initialPos : Q := posX initialState.
Definition initialVel : Q := velX initialState.

(*
Definition posAfterTime (ist : TrainState)
  (elapsedTime : Time) : Q :=
   posX ist + elapsedTime* (velX ist).
*)
Definition opBind {A B : Type}
  (f : A-> option B) (a : option A) : option B :=
match a with
| Some a' => f a'
| None => None
end. 

Definition opExtract {A : Type}
   (a : option A) (def: A ): A :=
match a with
| Some a' => a'
| None => def
end. 

Definition getVelM (m : Message ) : option Q.
destruct m as [top payl].
destruct (eqdec top "motorRecv").
- subst. simpl in payl. unfold stringTopic2Type in payl.
  simpl in payl. apply Some. exact payl.
- exact None.
Defined.


Section Train.
Definition TimerMesg (n : nat) : Message :=
  existT _ "timerSend" n.

Context  
  (minGap : Qpos)
 `{etype : @EventType _ _ _ Event RosLoc minGap tdeq}.


Definition ControllerNode :  @RosNode _ _ _ Event.
  constructor.
  - exact (Build_TopicInfo ("timerSend"::nil) ("motorRecv"::nil)).
  - left. exact ControllerNodeAux.
Defined.


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



Definition getVel (e : Event) : option Q :=
match (eKind e) with
| deqEvt => getVelM (eMesg e)
| _ => None
end.


Close Scope Q_scope.

Definition getVelFromMsg (oev : option Event) : option Q  :=
(opBind getVel oev).

Definition C := Cast.

Definition ProximitySensor (alertDist maxDelay: R) 
  : @Device Event R :=
fun  (distanceAtTime : Time -> R)  
     (evs : nat -> option Event) 
    =>
      (forall t:Time,
       distanceAtTime t  [>] alertDist
       -> exists n,
            match (evs n) with
            | Some ev => C (eTime ev [<] t [+] maxDelay) 
            | None => False
            end).



Definition SlowMotor (reactionTime : R) : @Device Event R :=
fun  (velAtTime: Time -> R) (evs : nat -> option Event) 
  => (forall n:nat,
          let ovn := getVelFromMsg (evs n) in
          let otn := option_map eTime (evs n) in
          let otsn := option_map eTime (evs (S n)) in
          match (ovn, otn, otsn) with
          | (Some vn, Some tn , Some tsn) => 
              forall t : Time, 
                t [>] tn [+] reactionTime
                -> t [<] tsn
                -> velAtTime t = (Q2R vn)
          | _ => True
          end).

(*

Fixpoint tstateAtN (locEvts: nat -> option Event) (n: nat)
: TrainState :=
let ev := (locEvts n) in
let ovx := opBind getVel ev in
match n with
| 0 => let pos := (posAfterTime initialState (eTime ev)) in
       let vel := opExtract ovx initialVel in
                        mkSt pos vel 
| S n => initialState
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
*)

End Train.

(** To begin with, let the VelControl device control position
    make it exact if needed *)

(** need to add sequence numbers in timer messages and keep
    track of it in the controller sw *)

(** N2R commuted with addition *)
