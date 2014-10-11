
Add LoadPath "../../../ssrcorn" as CoRN.
Add LoadPath "../../../ssrcorn/math-classes/src" as MathClasses.

Require Export Process.


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
  posX : R; (* this should really be R *)
  vX : R
}.

Open Scope Q_scope.

Definition VelExactly  (vel : Q) : OutDevBehaviour R :=
Build_OutDevBehaviour (fun tm rint =>  (forall t, rint t = Q2R vel)).

Definition VelOutDevice : 
  MemoryLessOutDev R Q :=
  (VelExactly 0, fun q => VelExactly q).


(* MOVE !! *)

Require Export model.structures.Qpossec.

Lemma mkTime (qp : Qpos) : Time.
Admitted.


(** outputs a message every [delay] seconds *)
Definition Timer (delay : Qpos) : InpDev unit unit.
cofix.
  constructor. right.
  split.
  - split; [constructor|].
    exact (mkTime delay). 
  - exact Timer.
Defined.


(** To model randomness, the device can
  take a stream of random bits as input 
  This randomness source can be a part of the environment.*)