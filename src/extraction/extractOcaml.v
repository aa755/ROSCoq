Require Import CRexp.


Definition answer (n:positive) (r:CR) : Z :=
 let m := (iter_pos n  _(Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.


Extraction Language Ocaml.

Definition test := answer 3 (exp (1))%CR.

Eval vm_compute in test. (** immediately produces the correct answer (2718) *)


Require Import ExtrOcamlZBigInt.
Extraction "OCamlExtract.ml" test.
