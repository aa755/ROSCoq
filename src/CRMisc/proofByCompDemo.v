Require Import IRLemmasAsCR.

Lemma demo :  √((cos ½)) < exp (cos (sin (arctan π))).
Proof.
  exists 1%nat.  vm_compute.
  reflexivity.
Qed.


