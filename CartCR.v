
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.

Section Programs.

Definition QSignHalf (q: Q) : Q :=
  if (decide (q < 0)) then ((-1)#2) else (1#2).

Require Export Vector.

Definition polarAngle (cart :Vec2D Q) : CR.
  pose proof (decide ((X cart) = 0)) as Hdec.
  destruct Hdec as [Hdec| Hdec].
- exact (CRpi * (AQSignHalf (Y cart))).
- apply aq_trivial_apart in Hdec.
  assert (AQ ₀) as Haq by (exists (X cart);auto).
Abort.

End Programs.
