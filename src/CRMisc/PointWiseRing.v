
Require Export IRLemmasAsCR.
Section FunRing.

Open Scope uc_scope.


Instance Plus_instance_QposInf : Plus QposInf := QposInf_plus.
Instance Plus_instance_CR_uc_CR : Plus  (CR --> CR).
  intros f g.
  econstructor.
  instantiate (2:= λ x, f x + g x).
  instantiate (1:= λ x, (mu f x)  + (mu g x)).
  intros ? ? ? Hb.
  (* apply ball_triangle. *)
Abort.
End FunRing.
