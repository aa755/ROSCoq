(* 
  Author : Abhishek Anand
  email : abhishek.anand.iitg@gmail.com
*)

Require Export QArith.

(* only available after Coq 8.5 *)
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellZNum.

(*copied from CoRN.util.Extract.*)
Extract Inductive comparison => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].

Extract Inlined Constant Psucc => "(Prelude.succ)".
Extract Inlined Constant Ppred => "(Prelude.pred)".
Extract Inlined Constant Pplus => "(Prelude.+)".
Extract Inlined Constant Pminus => "(Prelude.-)".
Extract Inlined Constant Pmult => "(Prelude.*)".
Extract Inlined Constant Pmin => "(Prelude.min)".
Extract Inlined Constant Pmax => "(Prelude.max)".
Extract Inlined Constant Pos.compare => "(Prelude.compare)".

(**
sudo apt-get install ghc-prof  
ghc simulator.hs -main-is Simulator -o Simulator -prof -fprof-auto  
time ./Simulator +RTS -p  
vim Simulator.prof  
 
 
        Fri Jan 22 20:10 2016 Time and Allocation Profiling Report  (Final)  
 
          Simulator +RTS -p -RTS  
 
       total time  =      222.64 secs   (222638 ticks @ 1000 us, 1 processor)  
       total alloc = 238,092,222,376 bytes  (excludes profiling overheads)  
 
COST CENTRE      MODULE    %time %alloc  
 
compare_cont.\   Simulator  45.5   48.6  
compare_cont.\.\ Simulator  24.1   24.3  
compare_cont.\.\ Simulator  23.9   24.3  
compare_cont     Simulator   1.3    0.0  

*)

(**
Clearly compare_cont was the bottleneck in the above application.
It operates using the binary representation, which is costly to simulate
over machine big integers. So, we redefine it as below, so that
it only uses the above fast operations.
*)
Definition  posCompareContAbstract43820948120402312 
(c: comparison) (x y: positive) :comparison :=
Pos.switch_Eq c (Pos.compare x y).

(*posCompareContAbstract43820948120402312 has to be extracted as well
in any project. Coq doesn't know that it is supposed to extracted
posCompareContAbstract43820948120402312 when Pos.compare_cont
is supposed to be extracted.*)
Extract  Constant Pos.compare_cont => "(posCompareContAbstract43820948120402312)".

(**
In one application (animating the car's motion), 
the above directive cut down the cost from 3 minutes
to 3 seconds.

The proof below justifies the above directive.
*)

Lemma PosCompareContAbstract43820948120402312Correct
(c: comparison) (x y: positive) :
Pos.compare_cont c x y
= posCompareContAbstract43820948120402312 c x y.
Proof using.
  apply Pos.compare_cont_spec.
Qed.




Extract  Constant positive_eq_dec => "(Prelude.==)".
(** Although the definition of Haskell's Ratio is 
  quite similar to Coq.QArith.QArith_base.Q ,
  the haskell version has useful utilities like conversion
  to and from floats *)

Extract Inductive Q => "(Data.Ratio.Ratio Prelude.Integer)" ["(\x y -> (Data.Ratio.%) x y)"]
  "(\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))".
