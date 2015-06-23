
Require Export iCreateMoveToLoc.

Definition rotSpeedRadPerSec : Qpos := QposMake 1 2.

Definition speedMetresPerSec : Qpos := QposMake 1 10.

Definition  delResSecInv :  positive := (1000)%positive.

Definition delEpsSec : Qpos := QposMake 1 10000.

Definition initDelayLin : Qpos := QposMake 1 1.


Definition robotProgramInstance (delayLinSec : Qpos) :  PureProcWDelay TARGETPOS VELOCITY :=
  robotPureProgam 
          rotSpeedRadPerSec 
          speedMetresPerSec
          delayLinSec
          delEpsSec
          delResSecInv.

(** To ensure that the Java shim maintains the state correctly,
   we make this process whose state is non-trivial and
   stores the delay between the "stop-turning" and
   the "start-moving" message.
   At each update, this value is doubled. *)

Definition SwProcessInstance : Process Message (list Message):=
{|
State := Q;
curState := initDelayLin;
handler := λ (ins : Q) (inm : Message),
           (ins * 2,
           delayedLift2Mesg (robotProgramInstance (QabsQpos ins)) inm) |}.

(*
Definition SwProcessInstance2 : Process Message (list Message):=
{|
State := Q;
curState := initDelayLin;
handler := λ (ins : Q) (inm : Message),
           (ins * 2,
           delayedLift2Mesg 
            (robotPureProgam 
          rotSpeedRadPerSec 
          speedMetresPerSec
          (QabsQpos ins)
          delEpsSec
          delResSecInv) inm ) |}.
*)


Definition target1Metres : Cart2D Q 
  := {|X:=  Qmake 1 1 ; Y:=   Qmake 1 1|}.

Definition mkInpMsg (mp : Cart2D Q) : Message := mkTargetMsg mp.

(*
Definition robotOutput : list (Q ** Polar2D Q).
let t:= (eval vm_compute in (robotProgramInstance 
    initDelayLin target1Metres)) in
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


Definition nthMsgPayload (lm : list Message) 
  (tp : Topic) (n:nat) : option (topicType tp) :=
   getPayloadOp tp (nth_error lm n).

Definition nthVelMsgPayload (lm : list Message) 
   (n:nat) : option (Polar2D Q) :=
   nthMsgPayload lm VELOCITY n.

Definition nthDelay (resp : list Message) (n:nat) : option Q :=
  option_map (delay ∘ snd) (nth_error resp n).

Definition nthLinVel (resp : list Message) (n:nat) : option Q :=
  option_map ((@rad _)) (nthVelMsgPayload resp n).

Definition nthTheta (resp : list Message) (n:nat) : option Q :=
  option_map ((@θ _)) (nthVelMsgPayload resp n).

Definition QNumOp  : option Q -> option Z :=
  option_map Qnum.

Definition QDenOp  : option Q -> option positive :=
  option_map Qden.


Require Import ExtrOcamlBigIntConv.

Definition QFromBigInts (num den: bigint) : Q :=
  Qmake (z_of_bigint num) (pos_of_bigint den).

Definition QFromBigInt (num : bigint) : Q :=
  Qmake (z_of_bigint num) 1%positive.

Definition mkInpMsgFromBig (x y : bigint) : Message 
  := mkTargetMsg {|X:= QFromBigInt x; Y:= QFromBigInt y|}.

Extraction "roboExtract.ml" mkInpMsgFromBig 
  robotProgramInstance initDelayLin target1Metres
  rotSpeedRadPerSec 
          speedMetresPerSec
          initDelayLin
          delEpsSec
          delResSecInv.
Definition robotOutput : list (Q ** Polar2D Q).
let t:= (eval vm_compute in (robotProgramInstance 
    initDelayLin target1Metres)) in
exact t.
Defined.
