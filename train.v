Require Export Process.

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.QOrderedType.

Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.

(** this is a 1D train between 2 stations
    It has sensors on each side to estimate
    the distance from endpoints.
    The operator directly controls the velocity
    of the train. In ideal world, he/she
    controls the acceleration *)

Record TrainState :=
{
  posX : Q; (* this should really be R *)
  vX : Q
}.

Open Scope Q_scope.

Definition VelOutDevice : 
  MemoryLessOutDev Q Q :=
fun inp tp => (forall t:Time, 
       (inp  < (tp t) < (inp + 1))).

(* MOVE !! *)
Definition Timer (t : Time)
