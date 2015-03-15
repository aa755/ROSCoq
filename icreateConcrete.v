
Require Export icreate.

Definition rotSpeedRadPerSec : Qpos := QposMake 1 2.

Definition speedMetresPerSec : Qpos := QposMake 1 10.

Definition anglePrecRadPerSec : Qpos := QposMake 1 100.

Definition R2QPrec : Qpos := QposMake 1 100.

Definition initDelayLin : Qpos := QposMake 1 1.


Definition robotProgramInstance distSec :  PureProcWDelay TARGETPOS VELOCITY :=
  robotPureProgam 
          rotSpeedRadPerSec 
          speedMetresPerSec
          R2QPrec
          distSec.

Definition SwProcessInstance : Process Message (list Message).
  apply Build_Process with (State := Q).
  exact initDelayLin.
  intros ins inm.
  split.
  - exact (ins * 2).
  - exact ((delayedLift2Mesg (robotProgramInstance (QabsQpos ins))) inm).
Defined.

Definition target1Metres : Cart2D Q 
  := {|X:= - Qmake 1 1 ; Y:=   Qmake 1 1|}.

Definition mkInpMsg (mp : Cart2D Q) : Message := mkTargetMsg mp.

(* 
Definition robotOutput : list (Q ** Polar2D Q).
let t:= (eval vm_compute in (robotProgramInstance target1Metres)) in
exact t.
Defined.
*)

Definition StateType : Type.
  let t := eval vm_compute in (State SwProcessInstance) in exact t.
Defined.
Definition state0 := curState SwProcessInstance.

(*
Definition roboOut1 : 
   StateType * (list Message).
  let t := eval vm_compute in 
     ((handler SwProcessInstance) state0 (mkInpMsg target1Metres)) in
  exact t.
Defined.

Definition state1 : StateType.
  let t := eval vm_compute in (fst roboOut1) in
  exact t.
Defined.

Definition outMsgs1 : list Message.
  let t := eval vm_compute in (snd roboOut1) in
  exact t.
Defined.
*)

Definition milliSeconds (q : Q) : Z :=
Zdiv ((Qnum q) * 1000) (Qden q).

Definition milliSecondsQ (q : Q) : Q :=
(milliSeconds q)# 1000.

Definition nthMsgPayload (lm : list Message) 
  (tp : Topic) (n:nat) : option (topicType tp) :=
   getPayloadOp tp (nth_error lm n).

Definition nthVelMsgPayload (lm : list Message) 
   (n:nat) : option (Polar2D Q) :=
   nthMsgPayload lm VELOCITY n.

Definition nthDelay (resp : list Message) (n:nat) : option Q :=
  option_map (milliSecondsQ ∘ delay ∘ snd) (nth_error resp n).

Definition nthLinVel (resp : list Message) (n:nat) : option Q :=
  option_map ((@rad _)) (nthVelMsgPayload resp n).

Definition nthTheta (resp : list Message) (n:nat) : option Q :=
  option_map ((@θ _)) (nthVelMsgPayload resp n).

Definition QNumOp  : option Q -> option Z :=
  option_map Qnum.

Definition QDenOp  : option Q -> option positive :=
  option_map Qden.

(*
Definition approxTime (lm: list (Q ** Polar2D Q)) : list (Z ** Polar2D Q) := 
map (λ p, ((microSeconds (fst p)), snd p)) lm.

Lemma trial1 : approxTime (robotProgramInstance target1Metres) ≡ [].
vm_compute.
Abort.
*)