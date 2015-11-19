Require Export Coq.Program.Tactics.
Require Export LibTactics.
(** printing × $\times$ #×# *)
(** printing :> $:$ #:># *)
(** printing ≡ $\equiv$ #≡# *)
(** printing [*] $*$ #*# *)
(** printing ∧ $\wedge$ #∧# *)
(** printing ∀ $\forall$ #∀# *)
(** printing → $\rightarrow$ #→# *)
(** printing ∃ $\exists$ #∃# *)
(** printing ≤ $\le$ #≤# *)
(** printing θ $\theta$ #θ# *)
(** printing eeev $\epsilon_v$ #∊ᵥ# *)
(** printing eeew $\epsilon_w$ #∊w# *)
(** printing tm $t_m$ #tm# *)
(** printing IR $\mathbb{R}$ #IR# *)
(** printing CR $\mathbb{R}$ #CR# *)
(** printing tr $t_r$ #tr# *)
(** remove printing * *)

(** printing ' $ $ #'# *)

Require Import Vector.
Require Import CPS.
Require Import CPSUtils.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.
Require Import CartCR.
Require Export ackermannSteering.
Require Export ackermannSteeringProp.

  Add Ring RisaRing: (CRing_Ring IR).

Require Export CartIR.

  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Set Implicit Arguments.
Record Rigid2DState (A:Type): Type :=
{
  pos2D : Cart2D A;  
  θ2D :  A
}.

(** enough data to render a car in a picture, which will be a part of an animation*)
Record carState (A:Type) : Type :=
{
  csrigid2D : Rigid2DState A;  
  cs_tc :  A (*turn curvatire, determines the position of steering wheel*)
}.

Open Scope CR_scope.


(** with some effort, it should be possible to get rid of the 
   second component of the dependent pair, because of continuity.*)
Definition DAtomicMove := {am : AtomicMove 
    | (am_tc am = 0 or (am_tc am) >< 0) }.

Definition unitVecCR (θ : CR) : Cart2D CR := {| X := cos θ; Y := sin θ |}.
Open Scope mc_scope.

Close Scope CR_scope.

Typeclasses  eauto := 100.

Global Instance castCRCart2DCR : Cast CR (Cart2D CR) := sameXY.

Definition stateAfterAtomicMove 
  (cs : carState CR) (dm : DAtomicMove): carState CR:=
  
  let tc : CR := (am_tc (projT1 dm)) in
  let dist : CR := (am_distance (projT1 dm)) in
  let θInit :CR := (θ2D (csrigid2D cs)) in
  let θf :CR := θInit + tc*dist in
  let posInit : Cart2D CR := (pos2D (csrigid2D cs)) in
  let posDelta := 
    match (projT2 dm) with
    | inl _ =>  ('dist) * (unitVecCR θInit)
    | inr p => {|X:= (sin θf - sin θInit) * (CRinvT tc p) ; 
                Y:= (cos θInit - cos θf) * (CRinvT tc p)|}
    end in  
  {|csrigid2D := {|pos2D := posInit + posDelta; θ2D := θf|} 
    ; cs_tc :=tc |}.


Record Line2D (A:Type):=
{
  lstart : Cart2D A;
  lend : Cart2D A
}.

Fixpoint linesConsecutive {A:Type}
   (pts : list (Cart2D A)): list (Line2D A) :=
match pts with
| nil => []
| h1::tl => match tl with
            | nil => []
            | h2::_ =>  {|lstart := h1 ; lend := h2|}::(linesConsecutive tl)
            end
end.

Section LineRounding.
(** A perfect rouding from a real to an integer is undecidable.
  This value is an upper bound on suboptimality. e.g. values between
   1.5-eps and 1.5+eps may be rounded to 1 or 2. *)
Variable eps: Qpos.

Definition roundPointRZ (p: Cart2D CR) : Cart2D Z :=
{|X:= R2ZApprox (X p) eps; Y:=R2ZApprox (Y p) eps |}.

Definition roundLineRZ (p: Line2D CR) : Line2D Z :=
{|lstart := roundPointRZ (lstart p); lend:=roundPointRZ (lend p) |}.

End LineRounding.

Extraction Language Haskell.
Require Import ExtrHaskellBasic.
Require Import String.
Require Import ExtrHaskellString.
Require Import ExtrHaskellQ.
Require ExtrHaskellNatInteger.
Require ExtrHaskellNatNum.

Axiom ZtoString : Z -> string.
(** [Z] maps to [Prelude.Integer] and [string] map to Prelude.?? . 
  So Prelude.show works *)
Extract Constant ZtoString => "Prelude.show".

Definition sconcat (l:list string) : string :=
  List.fold_left append  l EmptyString.


Definition newLineChar : Ascii.ascii := Ascii.ascii_of_nat 10.
Definition newLineString : string := String newLineChar EmptyString.

SearchPattern string.
Definition tikZPoint (p: Cart2D Z) : string := 
  "(" ++ ZtoString (X p) ++ "," ++ ZtoString (Y p) ++ ")".

Definition tikZLine (l: Line2D Z) : string :=
  "\draw" ++ tikZPoint (lstart l) ++ "--" ++ tikZPoint (lend l) ++ ";" ++
  newLineString.

Definition tikZLines (l: list (Line2D Z)) : string :=
  sconcat  (List.map tikZLine l).

Definition tikZOptions : string :=
 "[scale=0.02,overlay,shift={(current page.center)}]".
 
Definition tikZHeaderFooter (contents : string) : string :=
  "\begin{tikzpicture}"++tikZOptions++newLineString++contents++newLineString
  ++ "\end{tikzpicture}".

Definition beamerFrameHeaderFooter (title contents : string) : string :=
  "\begin{frame}{"++title++"}"++newLineString++contents++newLineString
    ++ "\end{frame}"++newLineString.

Definition tikZPicLines (l: list (Line2D Z)) : string :=
  tikZHeaderFooter (tikZLines l).

Definition beamerFrameLines (title: string) 
    (l: list (Line2D Z)) : string :=
  beamerFrameHeaderFooter title (tikZPicLines l).

(** position of the 4 corners of the car *)

Section CornerPos.
Variable eps:Qpos.
Variable cd :CarDimensions CR.
Variable cs :Rigid2DState CR.

Definition frontUnitVec : Cart2D CR := unitVecCR (θ2D cs).
Definition rightSideUnitVec : Cart2D CR := unitVecCR ((θ2D cs) - (½ * π)).

Definition frontRight : Cart2D CR := 
  (pos2D cs) 
    + frontUnitVec* '(lengthFront cd)
    + rightSideUnitVec * '(width cd).

Definition frontLeft : Cart2D CR := 
  (pos2D cs) 
    + frontUnitVec* '(lengthFront cd)
    - rightSideUnitVec * '(width cd).

Definition backLeft : Cart2D CR := 
  (pos2D cs) 
    - frontUnitVec* '(lengthBack cd)
    - rightSideUnitVec * '(width cd).

Definition backRight : Cart2D CR := 
  (pos2D cs) 
    - frontUnitVec* '(lengthBack cd)
    + rightSideUnitVec * '(width cd).


Definition carBoundingBox : list (Line2D CR) := 
  {|lstart := frontRight ; lend := backRight|}
  ::(linesConsecutive [frontRight;frontLeft;backLeft;backRight]).

Definition carBoundingBoxZ  : list (Line2D Z):=
  List.map (roundLineRZ eps) carBoundingBox.

Definition carBoundingBoxTikZ : string := 
  tikZLines (carBoundingBoxZ).

Definition carBoundingBoxBeamer : string := 
  beamerFrameLines "hello" (carBoundingBoxZ).
  
End CornerPos.

Section DrawCar.
Variable eps:Qpos.
Variable cd :CarDimensions CR.
Variable cs :carState CR.

Definition carBeamer : string := 
  beamerFrameLines "hello" (carBoundingBoxZ eps cd (csrigid2D cs)).

End DrawCar.

Global Instance  CastZCR : Cast Z CR := fun x => inject_Q_CR (inject_Z x).

(**lets compute a concrete bounding box*)
Open Scope Z_scope.
(** A perfect rouding from a real to an integer is undecidable.
  This value is an upper bound on suboptimality. e.g. values between
   1.5-1/100 and 1.5+1/100 may be rounded to 1 or 2. *)
Local Definition eps : Qpos := QposMake 1 100.

Definition myCarDim : CarDimensions CR :=
{|lengthFront := cast Z CR 100; lengthBack :=  cast Z CR 15;
 width := cast Z CR 25|}.
 
Close Scope Z_scope.

Definition initSt : carState CR :=
 {| csrigid2D := {|pos2D := 0; θ2D := 0|}; cs_tc :=0 |} .

Definition mkStraightMove (d:CR): DAtomicMove.
 exists {|am_distance :=d; am_tc :=0|}.
 simpl. left. reflexivity.
Defined.

Global Instance  CastQposCR : Cast Qpos CR := fun x => inject_Q_CR (QposAsQ x).

Definition mkQTurnMove (t:Qpos) (d:CR): DAtomicMove.
 exists {|am_distance := d ; am_tc := 't|}.
 simpl. right. right. clear.
 apply CRlt_Qlt. destruct t. simpl. assumption.
Defined.

Typeclasses eauto := 10.

Definition mkNegQTurnMove (t:Qpos) (d:CR): DAtomicMove.
 exists {|am_distance := d ; am_tc := -'t|}.
 simpl. right. left. clear. eapply CRltT_wdl;[
  symmetry; apply CRopp_Qopp|].
 apply CRlt_Qlt. destruct t. simpl. lra.
Defined.

  
Local Definition straightMove : DAtomicMove :=
  (mkStraightMove (cast Z CR 100))%Z.

Local Definition turnMove : DAtomicMove :=
  (mkQTurnMove (QposMake 100 1) (cast Z CR 100))%Z.

Definition carStatesFrames  (l:list (carState CR)) : string :=
 sconcat (List.map (carBeamer eps myCarDim) l).

Fixpoint movesStates (l:list DAtomicMove) (init : carState CR) : 
  list (carState CR) :=
match l with
| [] => [init]
| hm::t => let midState := stateAfterAtomicMove init hm in
      init::(movesStates t midState)
end.

Definition DAtomicMoves := list DAtomicMove.

Definition getAtomicMove (d: DAtomicMove) : AtomicMove := projT1 d.


Definition DWriggle (t:Qpos) (d:CR) : DAtomicMoves 
    :=  [mkQTurnMove t d; mkNegQTurnMove t (-d)].

Lemma DWriggleSame : forall (t:Qpos) (d:CR), 
  List.map getAtomicMove (DWriggle t d) = Wriggle ('t) d.
Proof.
  intros. reflexivity.
Qed.

Local Definition wriggleMove : DAtomicMoves :=
  (DWriggle (QposMake 100 1) (cast Z CR 100))%Z.
  
Definition toPrint : string := carStatesFrames 
  (movesStates wriggleMove initSt).


Extraction "simulator.hs" toPrint.