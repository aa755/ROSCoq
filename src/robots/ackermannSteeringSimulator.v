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
(** position of the 4 corners of the car *)

Section CornerPos.
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

End CornerPos.

Global Instance  CastZCR : Cast Z CR := fun x => inject_Q_CR (inject_Z x).

SearchPattern (Cast Q CR).
(**lets compute a concrete bounding box*)
Open Scope Z_scope.
Definition myCarDim : CarDimensions CR :=
{|lengthFront := cast Z CR 20; lengthBack :=  cast Z CR 3; width := cast Z CR 5|}.
Close Scope Z_scope.

Definition initSt : Rigid2DState CR :=
 {|pos2D := 0; θ2D := 0|}.

(** A perfect rouding from a real to an integer is undecidable.
  This value is an upper bound on suboptimality. e.g. values between
   1.5-1/100 and 1.5+1/100 may be rounded to 1 or 2. *)
Local Definition eps : Qpos := QposMake 1 100.

Definition myCarBoundingBoxZ : list (Line2D Z):=
  List.map (roundLineRZ eps) (carBoundingBox myCarDim initSt).

Open Scope Z_scope.
Eval native_compute in myCarBoundingBoxZ.


