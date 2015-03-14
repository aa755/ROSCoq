
Require Export icreate.

Definition rotSpeedRadPerSec : Qpos := QposMake 1 2.

Definition speedMetresPerSec : Qpos := QposMake 1 10.

Definition anglePrecRadPerSec : Qpos := QposMake 1 100.

Definition R2QPrec : Qpos := QposMake 1 100.

Definition distSec : Qpos := QposMake 3 1.


Definition robotProgramInstance : Cart2D Q → list (Q ** Polar2D Q) :=
  robotPureProgam 
          rotSpeedRadPerSec 
          speedMetresPerSec
          R2QPrec
          distSec.

Definition SwProcessInstance : Process Message (list Message) :=
  SwProcess
          rotSpeedRadPerSec 
          speedMetresPerSec
          R2QPrec
          distSec.

Definition target1Metres := {|X:= - Qmake 1 1 ; Y:=   Qmake 1 1|}.

Definition robotOutput : list (Q ** Polar2D Q).
let t:= (eval vm_compute in (robotProgramInstance target1Metres)) in
exact t.
Defined.


Definition milliSeconds (q : Q) : Z :=
Zdiv ((Qnum q) * 1000) (Qden q).

Definition milliSecondsQ (q : Q) : Q :=
(milliSeconds q)# 1000.

Definition nthDelay (resp : list (Q ** Polar2D Q)) (n:nat) : option Q :=
  option_map (milliSecondsQ ∘ fst) (nth_error resp n).

Definition nthLinVel (resp : list (Q ** Polar2D Q)) (n:nat) : option Q :=
  option_map ((@rad _) ∘ snd) (nth_error resp n).

Definition nthTheta (resp : list (Q ** Polar2D Q)) (n:nat) : option Q :=
  option_map ((@θ _) ∘ snd) (nth_error resp n).

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