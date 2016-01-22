(* 
  Author : Abhishek Anand
  email : abhishek.anand.iitg@gmail.com
*)

Require Export QArith.

(* only available after Coq 8.5 *)
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellZNum.

Extract Inlined Constant Pplus => "(Prelude.+)".
Extract Inlined Constant Psucc => "(Prelude.succ)".
Extract Inlined Constant Ppred => "(Prelude.pred)".
Extract Inlined Constant Pminus => "(Prelude.-)".
Extract Inlined Constant Pmult => "(Prelude.*)".
Extract Inlined Constant Pmin => "(Prelude.min)".
Extract Inlined Constant Pmax => "(Prelude.max)".
(* Extract Inlined Constant Pcompare => "Prelude.compare".*)
Extract Inlined Constant positive_eq_dec => "(Prelude.==)".
(** Although the definition of Haskell's Ratio is 
  quite similar to Coq.QArith.QArith_base.Q ,
  the haskell version has useful utilities like conversion
  to and from floats *)

Extract Inductive Q => "(Data.Ratio.Ratio Prelude.Integer)" ["(\x y -> (Data.Ratio.%) x y)"]
  "(\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))".
