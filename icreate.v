Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)

Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

(*
Definition dotProduct (v1 v2 : TContR × TContR) : TContR :=
  λ t, {fst v1} t [*] {fst v2} t  [+] {snd v1} t [*] {snd v2} t.
*)

Definition project2D  (vec :TContR × TContR) (angle : TContR) : TContR.
Admitted.

Definition isDerivativeOf2D  (f f' :TContR × TContR) : Type :=
  isDerivativeOf (fst f) (fst f') 
  × isDerivativeOf (fst f) (fst f').

(** CatchFileBetweenTagsStartCreate *)

Record iCreate : Type := {
  position :> TContR × TContR;          (* x, y co-ordinates *)
  theta : TContR;                       (* orientation *)
  transVel : TContR × TContR;             (* x, y velocity of center *)
  omega : TContR;

  derivRot : isDerivativeOf omega theta;
  derivTrans : isDerivativeOf2D transVel position
}.

(** CatchFileBetweenTagsEndCreate *)
