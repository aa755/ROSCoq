Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)

Require Export ROSCyberPhysicalSystem.
Require Export Vector.

Definition isVecDerivativeOf 
    {n : nat} (f f' : Vector n TContR) : Type.
  revert f f'.
  induction n as [| np Hind]; intros f f';[exact unit|].
  destruct f as [fv ft].
  destruct f' as [fv' ft'].
  exact ((isDerivativeOf ft ft') × (Hind fv fv')).
Defined.

(** CatchFileBetweenTagsStartCreate *)

Record iCreate : Type := {
  position :> Vector 2 TContR;          (* x, y co-ordinates *)
  theta : TContR;                       (* orientation *)
  transVel : Vector 2 TContR;             (* x, y velocity of center *)
  omega : TContR;

  derivRot : isDerivativeOf omega theta;
  derivTrans : isVecDerivativeOf transVel position
}.

(** CatchFileBetweenTagsEndCreate *)
