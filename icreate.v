Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)

Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Fixpoint Vector (n:nat) (T : Type)  : Type :=
match n with
| 0 => unit
| S n => (Vector n T) × T
end.

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
