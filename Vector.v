Require Export Fin.

Set Implicit Arguments.

Fixpoint Vector (n:nat) (T : Type)  : Type :=
match n with
| 0 => unit
| S n => (Vector n T) × T
end.

Definition VectInd {T A} 
 (bas: A)
 (rect: forall {n}, Vector n T -> A ->  T -> A) 
 {m} (v : Vector m T): A.
  induction m.
  - exact bas.
  - simpl in v. destruct v as [v t].
    exact (rect m v (IHm v) t).
Defined.

(*
Definition VectInd2 {T A} 
 (bas: A)
 (rect: forall {n}, Vector n T -> A ->  T -> A) 
 {m} (v : Vector m T): A.
  induction m.
  - exact bas.
  - simpl in v. destruct v as [v t].
    exact (rect m v (IHm v) t).
Defined.
*)




Definition vnth {T : Type} {m:nat} (v : Vector m T) (n : Fin m) : T.
  induction m;[apply f0; trivial| ].
  simpl in v. destruct n as [n np].
  destruct n; simpl in np.
  - exact (snd v).
  - apply fst in v. apply IHm;[exact v| ].
    exists n. apply sdjflksdjsdlkf3. trivial.
Defined.

Record Vec2D (T : Type) : Type := mk2D {X : T; Y: T}.

Definition fromVec2D {T:Type}  (v2: Vec2D T) : Vector 2 T := (tt, X v2, Y v2).

Definition toVec2D {T:Type}  (v2: Vector 2 T) : Vec2D T  
  := {|X := snd (fst v2); Y:= (snd v2) |}.

(* copied from https://coq.inria.fr/library/Coq.Logic.ExtensionalityFacts.html#is_inverse *)
Definition is_inverse A B (f : A->B) (g : B -> A) 
  := (forall a:A, g (f a) = a) /\ (forall b:B, f (g b) = b).

Lemma toFromVecInv {T:Type}: @is_inverse (Vec2D T) _ fromVec2D toVec2D.
Proof.
  split; intro t; destruct t as [X Y];[reflexivity|].
  destruct X as [X XU]. destruct X.
  simpl. reflexivity.
Qed.

Coercion fromVec2D : Vec2D >-> Vector.
Coercion toVec2D : Vector >-> Vec2D.

Require Export CoRN.algebra.CRings.
Require Export CoRN.ftc.MoreIntervals.

(*
Fixpoint dotProduct {n:nat} {T : CRing} (vl vr : Vector n T)  : T :=
match (vl,vr) with
| (tt,tt) => [0]
| ((ta,ha),(tb,hb)) => (ta [*] tb) [+] dotProduct ta tb
end.

*)
