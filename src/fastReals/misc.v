Require Import fastReals.interface.
Require Import Coq.ZArith.BinInt.

(*Coq.Numbers.BinNums.*)
Global Instance MinClassZ : MinClass Z := Zmin.
Global Instance MaxClassZ : MaxClass Z := Zmax.
