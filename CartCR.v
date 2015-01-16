
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
Local Notation yes := left.
Local Notation no := right.

Definition polarTheta (cart :Cart2D Q) : CR :=
match (decide ((X cart) = 0)) with
| yes _ => CRpi * ' QSignHalf (Y cart)
| no Hdec =>
    let angle := (rational_arctan (Y cart // (X cart ↾ Hdec))) in
    if decide (X cart < 0) then CRpi + angle else angle
end.

Definition polarRad (cart : Cart2D Q) : CR :=
  rational_sqrt ((X cart) * (X cart) +  (Y cart) * (Y cart)).

Definition Cart2Polar (cart :Cart2D Q) : Polar2D CR :=
  {|rad := polarRad cart 
  ; θ := polarTheta cart |}.

Definition Polar2Cart (pol : Polar2D CR) : Cart2D CR :=
  {|X := (rad pol) * (cos (θ pol)) 
  ; Y := (rad pol) * (sin (θ pol)) |}.

Instance castCartQ2CR : Cast (Cart2D Q) (Cart2D CR) :=
  fun c => {|X := cast Q CR (X c) ;  Y := cast Q CR (X c) |}.

Instance EquivCart  `{Equiv A} : Equiv (Cart2D A) :=
fun ca cb => (X ca = X cb /\ Y ca = Y cb).

(** lets first port lemmas about IR sin cos
    to a separate file and then use them separately here *)
Lemma Cart2Polar2CartID : forall (c :Cart2D Q),
  ' c = Polar2Cart (Cart2Polar c).
Proof.
  intros c.
  unfold Cart2Polar, Polar2Cart.
  simpl. destruct c as [cx cy].
  unfold polarTheta. simpl.
  destruct (decide (cx = 0)) as [Hcx0 | Hcx0].
- split; simpl.
Abort.
End Programs.
