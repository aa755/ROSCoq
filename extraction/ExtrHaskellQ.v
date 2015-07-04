(* 
  Author : Abhishek Anand
  email : abhishek.anand.iitg@gmail.com
*)

Require Export QArith.
Require Import ExtrHaskellZInteger.

(** Although the definition of Haskell's Ratio is 
  quite similar to Coq.QArith.QArith_base.Q ,
  the haskell version has useful utilities like conversion
  to and from floats *)

Extract Inductive Q => "HQ" ["(\x y -> mkQ x y)"]
  "(\fp qn -> fp (hQnum qn) (hQden qn))".
