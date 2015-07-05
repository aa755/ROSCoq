(* 
  Author : Abhishek Anand
  email : abhishek.anand.iitg@gmail.com
*)

Require Export QArith.

(* run getExtractionFiles.sh and then scons -k in ../
   if the line below fails *)
Require Import ExtrHaskellZInteger.

(** Although the definition of Haskell's Ratio is 
  quite similar to Coq.QArith.QArith_base.Q ,
  the haskell version has useful utilities like conversion
  to and from floats *)

Extract Inductive Q => "(Ratio Prelude.Integer)" ["(\x y -> x % y)"]
  "(\fp qn -> fp (numerator qn) (denominator qn))".
