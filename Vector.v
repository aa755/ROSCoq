Require Export Fin.

Set Implicit Arguments.


(*
Require Export PointWiseRing.
  FS_as_CSetoid (Fin n) T.
*)
Fixpoint Vector (n:nat) (T : Type)  : Type :=
match n with
| 0 => unit
| S n => (Vector n T) × T
end.

Definition VectInd {T} {P : forall n, Type}
 (bas: P 0)
 (rect: forall {n}, Vector n T -> P n ->  T -> P (S n)) 
 {m} (v : Vector m T): P m.
  induction m.
  - exact bas.
  - simpl in v. destruct v as [v t].
    exact (rect m v (IHm v) t).
Defined.


Definition vnth {T : Type} {m:nat} (v : Vector m T) (n : Fin m) : T.
  induction m;[apply f0; trivial| ].
  simpl in v. destruct n as [n np].
  destruct n; simpl in np.
  - exact (snd v).
  - apply fst in v. apply IHm;[exact v| ].
    exists n. apply sdjflksdjsdlkf3. trivial.
Defined.

Record Cart2D (T : Type) : Type := mkCart2D {X : T; Y: T}.
Record Polar2D (T : Type) : Type := mkPolar2D {rad : T; θ : T}.

Definition fromVec2D {T:Type}  (v2: Cart2D T) : Vector 2 T := (tt, X v2, Y v2).

Definition toVec2D {T:Type}  (v2: Vector 2 T) : Cart2D T  
  := {|X := snd (fst v2); Y:= (snd v2) |}.

(* copied from https://coq.inria.fr/library/Coq.Logic.ExtensionalityFacts.html#is_inverse *)
Definition is_inverse A B (f : A->B) (g : B -> A) 
  := (forall a:A, g (f a) = a) /\ (forall b:B, f (g b) = b).

Lemma toFromVecInv {T:Type}: @is_inverse (Cart2D T) _ fromVec2D toVec2D.
Proof.
  split; intro t; destruct t as [X Y];[reflexivity|].
  destruct X as [X XU]. destruct X.
  simpl. reflexivity.
Qed.

Coercion fromVec2D : Cart2D >-> Vector.
Coercion toVec2D : Vector >-> Cart2D.

Require Export CoRN.algebra.CRings.

Definition dotProduct {n:nat} {T : CRing} (vl vr : Vector n T) : T :=
@VectInd _ (fun n =>  Vector n T -> T) 
  (fun vr => [0]) 
  (fun  b _ rec tl vr =>  
              (tl [*]snd vr) [+] rec (fst vr)) n vl vr.
