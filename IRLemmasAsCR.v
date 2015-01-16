
Require Export CoRN.reals.fast.CRtrans.
(* Require Export CoRN.reals.faster.ARbigD. *)
(* Require Export CoRN.ftc.IntegrationRules. *)

Require Export Coq.Program.Tactics.
Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.
Require Export MathClasses.interfaces.abstract_algebra.

Instance castCRIR : Cast CR IR := CRasIR.

Instance inj_CRasIR : Injective  CRasIR.
  constructor.
- intros ? ? Heq. apply (fun_strext_imp_wd _ _ IRasCR) in Heq;
    [ | apply R_morphism.map_strext].
  rewrite CRasIRasCR_id in Heq.
  rewrite CRasIRasCR_id in Heq.
  exact Heq.
- constructor; eauto 2 with *.
  exact CRasIR_wd.
Qed.







