Add LoadPath "../../../nuprl/coq".
Require Export Coq.Program.Tactics.
Require Export LibTactics.

Require Export ROSCyberPhysicalSystem.
Require Export String.
(* Require Export CoRN.ode.SimpleIntegration. *)

Definition dotProduct (v1 v2 : TContR × TContR) : TContR :=
  λ t, {fst v1} t [*] {fst v2} t  [+] {snd v1} t [*] {snd v2} t.

Record iCreate : Type := {
  (* x, y co-ordinates *)
  position :> TContR × TContR;
  (* orientation *)
  theta : TContR;
  linVel : TContR × TContR;
  omega : TContR;

  derivRot : isDerivativeOf omega theta;
  derivTrans : isDerivativeOf linVel 
}.

