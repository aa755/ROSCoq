
Require Export CoRN.reals.faster.ARtrans.
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
Require Export CoRN.ftc.IntegrationRules.

Require Export Coq.Program.Tactics.

Section Programs.
Context `{AppRationals AQ}.



Definition ARhalf : AR := (cast CR AR (cast Q CR (1#2)%Q)).

Definition AQSignHalf (q: AQ) : AR :=
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

Definition polarAngle (cart :Vec2D AQ) : AR.
  pose proof (decide ((X cart) = 0)) as Hdec.
  destruct Hdec as [Hdec| Hdec].
- exact (ARpi * (AQSignHalf (Y cart))).
- apply aq_trivial_apart in Hdec.
  assert (AQ ₀) as Haq by (exists (X cart);auto).
Abort.

End Programs.
