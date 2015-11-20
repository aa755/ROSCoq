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

Definition centredLineAtAngle  (angle halfLength : CR) (p: Cart2D CR)
   : (Line2D CR) := 
   let v := 'halfLength * (unitVecCR angle) in
   {| lstart := p-v ; lend := p+v |}.

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

Definition tikZPoint (p: Cart2D Z) : string := 
  "(" ++ ZtoString (X p) ++ "," ++ ZtoString (Y p) ++ ")".

Definition tikZLine (l: Line2D Z) : string :=
  "\draw" ++ tikZPoint (lstart l) ++ "--" ++ tikZPoint (lend l) ++ ";" ++
  newLineString.

Definition tikZFilledRect (color : string) (l: Line2D Z) : string :=
  "\draw[fill=" ++ color  ++ "," ++ color ++ "]" ++ tikZPoint (lstart l) 
  ++ " rectangle " ++ tikZPoint (lend l) ++ ";" ++ newLineString.

Definition tikZColoredLine (color : string) (l: Line2D Z) : string :=
  "\draw[" ++ color ++ "]" ++ tikZPoint (lstart l) ++ "--" ++ tikZPoint (lend l) ++ ";" ++
  newLineString.

Definition tikZLines (l: list (Line2D Z)) : string :=
  sconcat  (List.map tikZLine l).

Definition tikZOptions : string :=
 "[scale=0.02]".
 
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


(**[lstart] represents min x y*)
Definition BoundingRectangle := Line2D CR.



Definition minCart (a b : Cart2D CR) := 
  {|X:= CRmin (X a) (X b); Y:= CRmin (Y a) (Y b)|}.

Definition maxCart (a b : Cart2D CR) := 
  {|X:= CRmax (X a) (X b); Y:= CRmax (Y a) (Y b)|}.

Definition boundingUnion (a b : BoundingRectangle) : BoundingRectangle :=
  {|lstart := minCart (lstart a) (lstart b); 
    lend := maxCart  (lend a) (lend b)|}.

Fixpoint computeBoundingRect (pt : Cart2D CR) 
  (otherpts : list (Cart2D CR)) : BoundingRectangle :=
match otherpts with
| [] => {|lstart := pt; lend := pt|}
| h::tl => let b := computeBoundingRect pt tl in
        boundingUnion b {|lstart := h; lend := h|}
end.
        
Section CornerPos.
(** position of the 4 corners of the car *)
Variable eps:Qpos.

Definition tikZBoundingClip (l: BoundingRectangle) : string :=
  let maxtoDim := {|lstart := lstart l; lend := lend l - lstart l|} in
  let l := (roundLineRZ eps maxtoDim) in   
  "\clip" ++ tikZPoint (lstart l) ++ " rectangle " ++ tikZPoint (lend l) ++ ";" ++
  newLineString.


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

Global Instance  CastQCartCR : Cast Q (Cart2D CR) 
  := fun x => sameXY (inject_Q_CR x).

Definition carBoundingRect : BoundingRectangle :=
computeBoundingRect frontRight [frontLeft;backLeft;backRight].

Definition leftWheelCenter : Cart2D CR := 
  (pos2D cs) + 
  '(Qmake 3 4) 
    * (frontUnitVec* '(lengthFront cd)
        + rightSideUnitVec * '(width cd)).

Definition rightWheelCenter : Cart2D CR := 
  (pos2D cs) + 
  '(Qmake 3 4) 
    * (frontUnitVec* '(lengthFront cd)
        - rightSideUnitVec * '(width cd)).

Definition carBoundingBox : list (Line2D CR) := 
  {|lstart := frontRight ; lend := backRight|}
  ::(linesConsecutive [frontRight;frontLeft;backLeft;backRight]).

Definition carWheels (θ : CR) : list (Line2D CR) := 
  List.map 
    (centredLineAtAngle θ ((lengthFront cd) * '(Qmake 1 8)))
    [leftWheelCenter; rightWheelCenter].

Definition drawCarZ  (θ : CR) : list (Line2D Z):=
  List.map (roundLineRZ eps) (carBoundingBox++carWheels θ).

Definition drawCarTikZ (θ : CR) : string := 
  tikZLines (drawCarZ θ).
  
End CornerPos.

Definition  comparisonAsZ  (c : Datatypes.comparison) : Z :=
match c with
| Datatypes.Eq => 0
| Datatypes.Lt => -1
| Datatypes.Gt => 1
end.


Global Instance  CastZCR : Cast Z CR := fun x => inject_Q_CR (inject_Z x).
Section DrawCar.
Variable eps:Qpos.
Variable cd :CarDimensions CR.
Variable cs :carState CR.

Local Definition wheelAngle :CR := 
  (θ2D (csrigid2D cs)) +
  '(comparisonAsZ (CR_epsilon_sign_dec (QposMake 1 10000) (cs_tc cs))) 
  * '(Qmake 1 6) * π.
  
Definition carBeamer (preface :string): string := 
beamerFrameHeaderFooter "hello"
  (tikZHeaderFooter 
    (preface ++ (drawCarTikZ eps cd (csrigid2D cs) wheelAngle))).

End DrawCar.



(**lets compute a concrete bounding box*)
Open Scope Z_scope.
(** A perfect rouding from a real to an integer is undecidable.
  This value is an upper bound on suboptimality. e.g. values between
   1.5-1/100 and 1.5+1/100 may be rounded to 1 or 2. *)
Local Definition eps : Qpos := QposMake 1 100.

Definition myCarDimZ : CarDimensions Z :=
{|lengthFront :=  100; lengthBack :=  15;
 width := 25|}.
Close Scope Z_scope.

Global Instance CastCarDimZCR : Cast  (CarDimensions Z) (CarDimensions CR) :=
fun c => {|lengthFront := cast Z CR (lengthFront c);
         lengthBack :=  cast Z CR (lengthBack c);
         width := cast Z CR (width c)|}.


Definition myCarDim : CarDimensions CR := 'myCarDimZ.
 

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


Definition carStatesFrames  (l:list (string * carState CR)) : string :=
 sconcat (List.map (fun p=> carBeamer eps myCarDim (snd p) (fst p)) l).


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
    


Definition DAtomicMoveInv (m : DAtomicMove) : DAtomicMove:=
  existT _ (AtomicMoveInv (getAtomicMove m)) (projT2 m).

Definition DAtomicMovesInv (ms : DAtomicMoves) : DAtomicMoves
      := rev (List.map DAtomicMoveInv ms).
      
Definition DSideways (t:Qpos) (dw ds:CR) : DAtomicMoves 
    := (DWriggle t dw) ++ [mkStraightMove ds] 
        ++ (DAtomicMovesInv (DWriggle t dw))
        ++ [mkStraightMove (- ds * cos (2 * 't * dw))].

Lemma DSidewaysSame : forall (t:Qpos) (dw ds :CR), 
  List.map getAtomicMove (DSideways t dw ds) = SidewaysMove ('t) dw ds.
Proof.
  intros. reflexivity.
Qed.

(** turn radius, which is inverse of turn curvature, is 200*)
Local Definition sidewaysMove : DAtomicMoves :=
(DWriggle (QposMake 1 200) (cast Z CR 100))%Z
(*  (DSideways (QposMake 1 200) (cast Z CR 100) (cast Z CR 100))%Z*) . 

Open Scope string_scope.
Definition moveNames : list string := 
  ["\hl{(c,d)}; (-c,-d)" ;"(c,d); \hl{(-c,-d)}"].

Definition initStName : string := 
  "(c,d); (-c,-d)".

Close Scope string_scope.
  

Definition NameDAtomicMove := prod string  DAtomicMove.

Fixpoint firstNPos (n:nat) : list nat:=
match n with
| O => [] 
| 1 => [] 
| S n' => n'::(firstNPos n')
end.

(** [1/d; 2/d ; ...; (d-1)/d]*)
Definition equiMidPoints (d:Z⁺) : list Q:=
  List.map (fun m => Qmake (Z.of_nat m) d) (rev (firstNPos (Pos.to_nat d))).

Definition scaleAtomicMove (m: AtomicMove) (s:CR): AtomicMove :=
 {|am_tc := am_tc m; am_distance := s*(am_distance m) |}.
 
Definition DscaleAtomicMove  (m: DAtomicMove) (s:Q) : DAtomicMove :=
  existT _ (scaleAtomicMove (getAtomicMove m) (inject_Q_CR s)) (projT2 m).
 
Definition finerAtomicMoves (d:Z⁺) (m: DAtomicMove) : list DAtomicMove :=
  List.map (DscaleAtomicMove m) (equiMidPoints d).

Definition NamedCarState := prod string  (carState CR).

Definition finerStates (d:Z⁺) (dm : NameDAtomicMove) (init : carState CR) : 
  NamedCarState * list NamedCarState :=
  let (name,dm) := dm in
  ((name,stateAfterAtomicMove init dm),
    List.map (fun m => (name,stateAfterAtomicMove init m)) (finerAtomicMoves d dm)).

Fixpoint finerMovesStates (d:Z⁺) (l:list NameDAtomicMove) (init : NamedCarState) : 
  BoundingRectangle * list NamedCarState :=
match l with
| [] => ((carBoundingRect myCarDim (csrigid2D (snd init))) , [init])
| hm::t => let (midState,interS) := finerStates d hm (snd init) in
           let (fb,fs) := (finerMovesStates d t midState) in
           let nb := boundingUnion 
                        fb 
                        (carBoundingRect myCarDim (csrigid2D (snd init))) in
          (nb  , ([init]++(interS)++fs))
end.

Definition epsd : Z := 3.
Definition textHt : Z := 20.

Definition Rect2D := Line2D.

(*
Definition sideCars (b:BoundingRectangle) (init : carState CR) : list (Rect2D Z) :=
  let initb := roundLineRZ eps (carBoundingRect myCarDim (csrigid2D init)) in
  let b := roundLineRZ eps b in
  let cardim : Cart2D Z  := {|X:= (lengthFront myCarDimZ) ; Y:= 2 * (width myCarDimZ) |} in
  let ymax := Y (lend initb) in
  let lcarMaxXY : Cart2D Z := {|X:= X (lstart b) - epsd ; Y:= ymax |}  in
  let rcarMinXY : Cart2D Z := {|X:= X (lend b) + epsd ; Y:= ymax - (Y cardim) |}  in
  [
    {|lstart := lcarMaxXY - cardim; lend := lcarMaxXY |} ;
    {|lstart := rcarMinXY ; lend := rcarMinXY + cardim |}
  ].
*)
Definition sideCars (b:BoundingRectangle) (init : carState CR) : BoundingRectangle * list (Rect2D CR) :=
  let initb := (carBoundingRect myCarDim (csrigid2D init)) in
  let cardim : Cart2D CR  := {|X:= (lengthFront myCarDim) ; Y:= 2 * (width myCarDim) |} in
  let ymax := Y (lend initb) in
  let lcarMaxXY : Cart2D CR := {|X:= X (lstart b) - 'epsd ; Y:= ymax |}  in
  let rcarMinXY : Cart2D CR := {|X:= X (lend b) + 'epsd ; Y:= ymax - (Y cardim) |}  in
  (boundingUnion b {|lstart := lcarMaxXY - cardim; lend := rcarMinXY + cardim |},
    [
      {|lstart := lcarMaxXY - cardim; lend := lcarMaxXY |} ;
      {|lstart := rcarMinXY ; lend := rcarMinXY + cardim |}
    ]).

Definition extendRectForText (b:BoundingRectangle)  : BoundingRectangle :=
  {|lstart := (lstart b) - {|X:= 0 ; Y:= 'textHt  |}; lend := (lend b) + {|X:= 0 ; Y:= 'textHt  |} |}.
  
Open Scope string_scope.
Definition drawEnv (b:BoundingRectangle) (init : carState CR) (label : string) : string :=
  let (bc, sc) := sideCars b init in
  let bf := extendRectForText bc in
  let textPos := roundPointRZ eps (lstart bc) in
  let bottomLineStart := {| X := X (lstart bc); Y := Y (lstart bc) - 'epsd |} in
  let bottomLineEnd := {| X := X (lend bc); Y := Y (lstart bc) - 'epsd |} in
  let bottomLineZ   :=  roundLineRZ eps {|lstart := bottomLineStart; lend := bottomLineStart|} in
  let scz  :=  List.map  (roundLineRZ eps) sc in
  let clip : string :=  tikZBoundingClip eps bf in
  let sideCars : list string :=  List.map  (tikZFilledRect "red") scz in
  let bottomLine : string :=  tikZColoredLine "red" bottomLineZ in 
  let text := "\node[below,right] at " ++ tikZPoint textPos ++ "{" ++ label ++ "};" in
  sconcat (sideCars ++ [clip;bottomLine]).
  
Close Scope string_scope.

Definition toPrint : string := 
let sidewaysMove := List.zip moveNames sidewaysMove  in
let initStp := (initStName,initSt) in
let (b,cs) := (finerMovesStates 3 sidewaysMove initStp) in
let clip : string := tikZBoundingClip eps b in
carStatesFrames 
  (List.map (fun x => (drawEnv b initSt (fst x),snd x)) 
      (cs ++ [initStp])).

Extraction "simulator.hs" toPrint.