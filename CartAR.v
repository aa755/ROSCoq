
Require Export CoRN.reals.faster.ARtrans.
Require Export CoRN.reals.fast.CRtrans.
Require Export CoRN.reals.faster.ARbigD.
Require Export CoRN.ftc.IntegrationRules.
(*bigD_approx*)
Require Export Coq.Program.Tactics.

Section Programs.

Definition R2QPrec : Qpos := QposMake 1 100.

Definition threeBy2 : bigD .
exact ((inject_Z_bigD 3) ≪ (-1)).
Defined.


Definition val : ARbigD .
exact ('threeBy2*ARpi).
Defined.

Eval vm_compute in (cast bigD Q (approximate val R2QPrec)).

Definition crNum : CR := ((('(3#2)%Q)*CRpi)).
Eval vm_compute in (approximate crNum R2QPrec).
Eval vm_compute in (cast bigD Q (approximate (cast CR ARbigD crNum) R2QPrec)).


Definition ARhalf : ARbigD := '((inject_Z_bigD 1) ≪ (-1)).

(*
Definition AQSignHalf (q: Q) : AR :=
  if (decide (q < 0)) then (-ARhalf) else ARhalf.

(** CRlt_Qlt *)
Definition ap0 {x : AQ} (p : apart x 0) : AR ₀.
unfold ApartZero.
  simpl.
  exists (cast AQ AR x).
  eauto with *.
  simpl. 
Abort.

Require Export Vector.

Definition polarAngle (cart :Cart2D AQ) : AR.
  pose proof (decide ((X cart) = 0)) as Hdec.
  destruct Hdec as [Hdec| Hdec].
- exact (ARpi * (AQSignHalf (Y cart))).
- apply aq_trivial_apart in Hdec.
  assert (AQ ₀) as Haq by (exists (X cart);auto).
Abort.
*)

End Programs.
