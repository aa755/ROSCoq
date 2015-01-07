Require Export Fin.

Fixpoint Vector (n:nat) (T : Type)  : Type :=
match n with
| 0 => unit
| S n => (Vector n T) × T
end.

