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

Fixpoint isVecDerivativeOf {n : nat} (f f' : Vector n TContR) : Type :=
match (f, f') as x in (Vector n TContR × Vector n TContR) with
| 0 => unit
| S n => (Vector n T) × T
end.

  isDerivativeOf (fst f) (fst f') 
  × isDerivativeOf (snd f) (snd f').

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
