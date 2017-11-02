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
Require Import car.errorBounds.
Require Export ackermannSteeringProp.

  Require Import IRMisc.LegacyIRRing.

Require Import atomicMoves.

Require Export CartIR.

Require Import String.

Require Import haskellExtractionDirectives.
(*Require Import ocamlExtractionDirectives.*)
  
Local Opaque CSine.
Local Opaque CCos.
Local Opaque Sine.
Local Opaque Cosine.
Local Opaque Sin.
Local Opaque Cos.

Set Implicit Arguments.
Require Import geometry2D.

(** enough data to render a car in a picture, which will be a part of an animation*)
Record carState (A:Type) : Type :=
{
  csrigid2D : Rigid2DState A;  
  cs_tc :  A (*turn curvatire, determines the position of steering wheel*)
}.

Open Scope CR_scope.


Open Scope mc_scope.

Close Scope CR_scope.

Typeclasses  eauto := 100.


Require Import fastReals.misc.
Require Import fastReals.interface.
Require Import fastReals.implCR.

Require Import MathClasses.interfaces.functors.


Definition carStateAfterAtomicMove 
  (cs : carState CR) (dm : @DAtomicMove CR _ _ _): carState CR:=
  {|csrigid2D := (*sfmap compress*) (stateAfterAtomicMove (csrigid2D cs) dm)
    ; cs_tc := (am_tc (projT1 dm)) |}.


Section LineRounding.
(** A perfect rouding from a real to an integer is undecidable.
  This value is an upper bound on suboptimality. e.g. values between
   1.5-eps and 1.5+eps may be rounded to 1 or 2. *)
Variable eps: Qpos.

Global Instance  CastZCR : Cast Z CR := fun x => inject_Q_CR (inject_Z x).

Definition finerRes : Z := 100.

Definition roundPointRZ (p: Cart2D CR) : Cart2D Z :=
{|X:= R2ZApprox ('finerRes * (X p)) eps; Y:=R2ZApprox ('finerRes * (Y p)) eps |}.

Definition roundLineRZ (p: Line2D CR) : Line2D Z :=
{|lstart := roundPointRZ (lstart p); lend:=roundPointRZ (lend p) |}.

End LineRounding.


Axiom ZtoString : Z -> string.
(** [Z] maps to [Prelude.Integer] and [string] map to Prelude.?? . 
  So Prelude.show works *)
Extract Constant ZtoString => "PleaseFixMe".
Definition sconcat (l:list string) : string :=
  List.fold_left append  l EmptyString.


Definition newLineChar : Ascii.ascii := Ascii.ascii_of_nat 10.
Definition newLineString : string := String newLineChar EmptyString.


Definition tikZPoint (p: Cart2D Z) : string := 
  "(" ++ ZtoString ((X p)) ++ "," ++ ZtoString (Y p) ++ ")".

Definition tikZLine (l: Line2D Z) : string :=
  "\draw" ++ tikZPoint (lstart l) ++ "--" ++ tikZPoint (lend l) ++ ";" ++
  newLineString.

Definition tikZLineStyled (s:string) (l: Line2D Z) : string :=
  sconcat ["\draw[";s;"]"; tikZPoint (lstart l) ; "--"; tikZPoint (lend l); ";";
            newLineString]%string.


Definition tikZFilledRect (color : string) (l: Line2D Z) : string :=
  "\draw[fill=" ++ color  ++ "," ++ color ++ ", fill opacity=0.3]" ++ tikZPoint (lstart l) 
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





Definition computeBoundingRectLines `{MinClass A}`{MaxClass A} `{Zero A}
  (ll : list (Line2D A)) : BoundingRectangle A :=
computeBoundingRect (List.map (@lstart _) ll ++ List.map (@lend _) ll).
        
Section CornerPos.
(** position of the 4 corners of the car *)
Variable eps:Qpos.

Definition tikZBoundingClip (l: BoundingRectangle Z) : string :=
  let maxtoDim := {|lstart := lstart l; lend := lend l - lstart l|} in
  "\clip" ++ tikZPoint (lstart l) ++ " rectangle " ++ tikZPoint (lend l) ++ ";" ++
  newLineString.


Global Instance  CastQCartCR : Cast Q (Cart2D CR) 
  := fun x => sameXY (inject_Q_CR x).


Variable cd :CarDimensions CR.
Variable cs :Rigid2DState CR.

Definition carBoundingRectCR : BoundingRectangle CR :=
  carMinMaxXY cd cs.

Definition leftWheelCenter : Cart2D CR := 
  (pos2D cs) + 
  '(Qmake 3 4) 
    * ((frontUnitVec cs)* '(lengthFront cd)
        + (rightSideUnitVec cs) * '(width cd)).

Definition rightWheelCenter : Cart2D CR := 
  (pos2D cs) + 
  '(Qmake 3 4) 
    * ((frontUnitVec cs)* '(lengthFront cd)
        - (rightSideUnitVec cs) * '(width cd)).

Definition carWheels (α : CR) : list (Line2D CR) := 
  List.map 
    (centredLineAtAngle α ((lengthFront cd) * '(Qmake 1 8)))
    [leftWheelCenter; rightWheelCenter].

Definition drawCarZAux  (α : CR) : list (Line2D Z):=
  List.map (roundLineRZ eps) ((carOutline cd cs)++carWheels α).


Definition drawCarTikZOld (θ : CR) : string := 
  tikZLines (drawCarZAux θ).

(** illustrate the current angle *)  
Definition angleLineLength : CR := '(Qmake 4 3) * (totalLength cd).

Definition angleLineXLength : CR := angleLineLength.

Definition Pair (T:Type) : Type := T*T.

Definition angleLines : Pair (Line2D CR) := 
let ls := (pos2D cs) - ('lengthBack cd) * (frontUnitVec cs) in
({|
  lstart := ls;
  lend := ls + ('(angleLineLength))*(frontUnitVec cs)
|},
{|
  lstart := ls;
  lend := ls + {|X:=angleLineXLength; Y:=0|}
|}
).

Definition textPos : Cart2D CR := (pos2D cs) 
  + ('totalLength cd) * (unitVec (½*(θ2D cs))).

Definition angleLabel (label:string) :=
sconcat ["\node[right] at "; tikZPoint (roundPointRZ eps textPos)
            ; "{" ; label ; "};"]%string.
            
Definition illustrateAngle (alabel: string): string :=
sconcat[
  tikZLineStyled "dashed" (roundLineRZ eps (fst angleLines));
  tikZLineStyled "dotted" (roundLineRZ eps (snd angleLines));
  angleLabel alabel
   ].

End CornerPos.

Definition  comparisonAsZ  (c : Datatypes.comparison) : Z :=
match c with
| Datatypes.Eq => 0
| Datatypes.Lt => -1
| Datatypes.Gt => 1
end.

Record CarStateRenderingInfo :=
{
  frameLabel : string;
  drawAngle : bool;
  angleString : string;
  pauseBefore : bool;
  emphBackRightCorner : bool
}.

Definition mkRenderingInfo (name: Pair string):CarStateRenderingInfo :=
{|
  frameLabel := fst name;
  angleString := snd name;
  drawAngle := false;
  pauseBefore := false;
  emphBackRightCorner := false
|}.

Definition mkTransitionRenderingInfo (name: Pair string):CarStateRenderingInfo :=
{|
  frameLabel := fst name;
  angleString := snd name;
  drawAngle := false; (* may want to set this true to true*)
  pauseBefore := true;
  emphBackRightCorner := false
|}.


Section DrawCar.
Variable eps:Qpos.
Variable cd :CarDimensions CR.
Variable cs :carState CR.

Local Definition wheelAngle :CR := 
  (θ2D (csrigid2D cs)) +
  '(comparisonAsZ (CR_epsilon_sign_dec (QposMake 1 10000) (cs_tc cs))) 
  * '(Qmake 1 6) * π.
  
Definition drawCarZ : list (Line2D Z) := 
drawCarZAux eps cd (csrigid2D cs) wheelAngle.

End DrawCar.



(**lets compute a concrete bounding box*)
Open Scope Z_scope.
(** A perfect rouding from a real to an integer is undecidable.
  This value is an upper bound on suboptimality. e.g. values between
   1.5-1/100 and 1.5+1/100 may be rounded to 1 or 2. *)
Local Definition eps : Qpos := QposMake 1 100.

Definition imaginaryCarDimZ : CarDimensions Z :=
{|lengthFront :=  60; lengthBack :=  15;
 width := 25|}.

Require Import exampleDimensions.

Extract Inlined Constant cbvApply => "(Prelude.$!)".

Axiom showQQQQ : (list (Z ** (list Z))) -> string.
Axiom showZZ : (Z ** Z) -> string.
Axiom showN : (nat) -> string.
Axiom showZ : Z -> string.
Extract Constant showQQQQ => "(Prelude.show)".
Extract Constant showZZ => "(Prelude.show)".
Extract Constant showN => "(Prelude.show)".
Extract Constant showZ => "(Prelude.show)".

Section simulator.
Variable carGeo : CarGeometry Z.


Definition myCarDimZ : CarDimensions Z := carDim carGeo.
Close Scope Z_scope.



Definition myCarDim : CarDimensions CR := 'myCarDimZ.

Definition initSt : carState CR :=
 {| csrigid2D := {|pos2D := 0; θ2D := 0|}; cs_tc :=0 |} .

Global Instance  CastQposCR : Cast Qpos CR := fun x =>  '(`x).

Require Import MathClasses.interfaces.orders.

Typeclasses eauto := 10.

(* Move *)

Local Definition straightMove : DAtomicMove CR :=
  (mkStraightMove (cast Z CR 100))%Z.



Definition NamedCarState := prod CarStateRenderingInfo  (carState CR).

Definition drawCarFrameZ (ns : NamedCarState) : ((string * string) * list (Line2D Z))
:=
let newF : string := 
  (if (pauseBefore (fst ns)) then "\newframe*" else "\newframe")%string in
let angle : string :=
  illustrateAngle eps myCarDim (csrigid2D (snd ns)) (angleString (fst ns)) in
let angle : string :=
  if (drawAngle (fst ns)) then angle else EmptyString in
(frameLabel (fst ns), sconcat [angle; newF; newLineString],
   drawCarZ eps myCarDim (snd ns)).


Require Import sidewaysMoveImpl.

Definition drawCarFrameZPicture (ns : NamedCarState) : string  :=
  let cs := (csrigid2D (snd ns)) in
	(sconcat [ ("\node at ");
             tikZPoint (roundPointRZ eps  (pos2D cs));
             "{\includegraphics[width=4cm, angle=";
             (showZ ((R2ZApprox (angleAsDegrees (θ2D cs))) eps- 45));
             ", origin=c]{car.pdf}};"])%string.

    
Definition carStatesFrames  (l:list NamedCarState) 
: list ((string * string) * list (Line2D Z))  :=
List.map (drawCarFrameZ) l.


Fixpoint movesStates (l:list (DAtomicMove CR)) (init : carState CR) : 
  list (carState CR) :=
match l with
| [] => [init]
| hm::t => let midState := carStateAfterAtomicMove init hm in
      init::(movesStates t midState)
end.

Definition DAtomicMoves := list (DAtomicMove CR).

Definition getAtomicMove (d: (DAtomicMove CR)) : AtomicMove CR := projT1 d.

(*
*)  


Fixpoint mapDiagonal  `(f: A->A) (prefix tail: list A) : list (list A) :=
match tail with
| [] => []
| h::tl => (prefix ++ ((f h)::tl))::(mapDiagonal f (prefix++[h]) tl)
end.



(*
Local Definition wriggleMove : DAtomicMoves :=
  (DWriggle (QposMake 1 150) ('(Qmake 32799 822050))).
*)

Definition totalAvailXExtraSpace : Qpos := (QposMake 35 1). 

Local Definition sidewaysMoveAndRightShift :  CR * DAtomicMoves :=
  optimalSidewaysMoveMazda totalAvailXExtraSpace.


Open Scope string_scope.
Definition moveNamesWriggle : list string := 
  ["\hll{($\alpha$,d)}; (-$\alpha$,-d)" ;"($\alpha$,d); \hll{(-$\alpha$,-d)}"].

Definition initStNameWriggle : string := 
  "($\alpha$,d); (-$\alpha$,-d)".

Definition atomicMoveNamesSideways : list string := 
  ["($\alpha$,d)"; "(-$\alpha$,-d)"; "$\;$(0,d')" ; "$\;$(-$\alpha$,d)" ; "($\alpha$,-d)"].

Local Definition spacedMoves := List.map (fun x => x++" ")atomicMoveNamesSideways.

Definition moveNamesSideways : list string := 
  List.map sconcat (mapDiagonal (fun x => sconcat ["\hll{";x;"}"]) [] spacedMoves).

Definition angleLabelsSideways : list string := 
  ["$\theta$"; "$2\theta$"; "$2\theta$"; "$\theta$"; "0"].

Definition sidewaysMovesInfo : list ( (Pair string)) :=
  List.zip moveNamesSideways angleLabelsSideways.

Close Scope string_scope.

Definition NameDAtomicMove := prod (Pair string)  (DAtomicMove CR).


Definition scaleAtomicMove (m: AtomicMove CR) (s:CR): AtomicMove CR:=
  {|am_tc := am_tc m; am_distance := s*(am_distance m) |}.

Definition DscaleAtomicMove  (m: (DAtomicMove CR)) (s:Q) : (DAtomicMove CR) :=
  existT _ (scaleAtomicMove (getAtomicMove m) (inject_Q_CR s)) (projT2 m).

Definition finerAtomicMoves (d:Z⁺) (m: (DAtomicMove CR)) : list (DAtomicMove CR) :=
  List.map (DscaleAtomicMove m) (equiMidPoints d).


Definition finerStates (d:Z⁺) (dm : NameDAtomicMove) (init : carState CR) : 
  NamedCarState * list NamedCarState :=
  let (name,dm) := dm in
  ((mkTransitionRenderingInfo name,carStateAfterAtomicMove init dm),
    List.map 
      (fun m => (mkRenderingInfo name,carStateAfterAtomicMove init m)) 
      (finerAtomicMoves d dm)).

Fixpoint finerMovesStates (d:Z⁺) (l:list NameDAtomicMove) (init : NamedCarState) : 
   list NamedCarState :=
match l with
| [] => ( [init])
| hm::t => let (midState,interS) := finerStates d hm (snd init) in
          ([init]++(interS)++(finerMovesStates d t midState))
end.

Definition textHt : Z := 25*finerRes.

Definition Rect2D := Line2D.

Definition sideCars (global init :BoundingRectangle Z): (BoundingRectangle Z) * list (Rect2D Z) :=
  let cardim : Cart2D Z  := (sameXY finerRes)*{|X:= (lengthFront myCarDimZ) ; Y:= 2 * (width myCarDimZ) |} in
  let ymax := Y (lend init) in
  let lcarMaxXY : Cart2D Z := {|X:= X (lstart global) ; Y:= ymax |}  in
  let rcarMinXY : Cart2D Z := {|X:= X (lend global) ; Y:= ymax - (Y cardim) |}  in
  (boundingUnion global {|lstart := lcarMaxXY - cardim; lend := rcarMinXY + cardim |},
    [
      {|lstart := lcarMaxXY - cardim; lend := lcarMaxXY |} ;
      {|lstart := rcarMinXY ; lend := rcarMinXY + cardim |}
    ]).


Definition extendRectForText (b:BoundingRectangle Z)  : BoundingRectangle Z :=
  {|lstart := (lstart b) - {|X:= 0 ; Y:= textHt  |}; 
    lend := (lend b) + {|X:= 0 ; Y:= textHt  |} |}.


Open Scope string_scope.

Definition drawEnv (global init:BoundingRectangle Z)  : string * Cart2D Z:=
  let (bc, sc) := sideCars global init in
  let textPos := lstart bc in
  let bf := extendRectForText bc in
  let bottomLineStart := {| X := X (lstart bc); Y := Y (lstart bc) |} in
  let bottomLineEnd := {| X := X (lend bc); Y := Y (lstart bc) |} in
  let bottomLineZ   := {|lstart := bottomLineStart; lend := bottomLineEnd|} in
  let clip : string :=  tikZBoundingClip bf in
  let sideCars : list string :=  List.map  (tikZFilledRect "red") sc in
  let bottomLine : string :=  tikZColoredLine "red" bottomLineZ in 
  (sconcat (sideCars ++ [clip;bottomLine]), textPos).


Definition frameWithLines (suffix:string) (lines : list (Line2D Z)) : string :=
    sconcat [newLineString; tikZLines lines; newLineString; suffix; newLineString].

  Local Notation minxy := (lstart).
  Local Notation maxxy := (lend).

Definition globalBound (initb :  BoundingRectangle Z) (rightExtra upExtra downExtra : CR ): BoundingRectangle Z := 
let rightExtraZ  :=  roundPointRZ eps {| X:= rightExtra; Y:= upExtra|} + {| X:= 1; Y:= 0|} in 
let leftExtra : CR :=  'totalAvailXExtraSpace - rightExtra in
let leftExtraZ   :=  roundPointRZ eps {| X:= leftExtra; Y:=downExtra|} + {| X:= 1; Y:=0|} in
initb + {| minxy := -leftExtraZ ; maxxy := rightExtraZ|}.





Definition animation (n: Z⁺): string := 
  let (rs, sidewaysMove) := sidewaysMoveAndRightShift in
  let sidewaysMove := List.zip sidewaysMovesInfo sidewaysMove  in
  let initStp : NamedCarState := 
    (mkRenderingInfo ((sconcat spacedMoves),EmptyString),initSt) in
  let cs : list NamedCarState := (finerMovesStates n sidewaysMove initStp) in
  let namedLines : list ((string * string) * list (Line2D Z)) 
    := carStatesFrames  cs in
  let allLines : list (Line2D Z) :=  (*cbvApply*) (flat_map snd) namedLines in
  match namedLines return string with
  | [] => ""
  | h::tl => 
      let initb := computeBoundingRectLines (snd h) in
      (* the 2 items below are just guesses. TODO : compute them from the bounds derived in sidewaysMove.v *)
      let upExtra :  CR := '(Zdiv (width (myCarDimZ)) (5%Z)) in
      let downExtra : CR := '(Zdiv (width (myCarDimZ)) (5%Z)) in
      let globalB : BoundingRectangle Z := globalBound initb rs upExtra downExtra  in
      let (preface, textPos) := drawEnv globalB initb in 
      let textTikZ  : string -> string  
        := fun label => "\node[below right] at " ++ tikZPoint textPos 
            ++ "{" ++ label ++ "};" ++ newLineString in
      let frames := 
        List.map (fun p => 
          frameWithLines 
            (sconcat [ preface ; textTikZ (fst (fst p)); snd (fst p)])
            (snd p)) 
          namedLines in
      sconcat frames
  end.

Fixpoint  fold_left_inter {A B : Type} (f : A → B → A) (l : list B) 
  (a0 : A) {struct l} : list A := 
  match l with
  | [] => [a0]
  | b :: t => (f a0 b)::(fold_left_inter f t (f a0 b))
  end.

Definition animateSpaceReqOptimalMove (n: Z⁺) : string := 
  let (_, sidewaysMove) := sidewaysMoveAndRightShift in
  let sidewaysMove := List.zip sidewaysMovesInfo sidewaysMove  in
  let initStp := (mkRenderingInfo ((sconcat spacedMoves),EmptyString),initSt) in
  let cs := (finerMovesStates n sidewaysMove initStp) in
  let namedLines : list ((string * string) * list (Line2D Z)) 
      := carStatesFrames cs in
  let boundRects : list (Line2D Z) 
    :=  List.map (computeBoundingRectLines∘snd) namedLines in
  let boundRectsCum : list (Line2D Z) 
    := fold_left_inter boundingUnion  boundRects 0 in
  let globalB :  (Line2D Z) 
    := last boundRectsCum 0 in
  let lineRects
    := List.zip namedLines  boundRectsCum in
  match lineRects return string with
  | [] => ""
  | (h,_)::tl => 
      let initb := computeBoundingRectLines (snd h) in
      let (pp, textPos) := drawEnv globalB initb in 
      let textTikZ  : string -> string  
        := fun label => "\node[below right] at " ++ tikZPoint textPos 
            ++ "{" ++ label ++ "};" ++ newLineString in
      let frames :=
        List.map (fun p => 
        let bnd := snd p in
        let p := fst p in
        let preface :=  sconcat [pp;tikZFilledRect "green" bnd] in
          frameWithLines 
            (sconcat [ preface ; textTikZ (fst (fst p)); snd (fst p)])
            (snd p)) 
          lineRects in
      sconcat frames
  end.

(* Move *)
Definition mkDAtomicMoveQ (qa: AtomicMove Q) : (DAtomicMove CR).
  destruct qa.
  exists (@mkAtomicMove  CR ('am_distance) ('am_tc)).
  remember (Qeq_bool am_tc 0)%Q as qd. destruct qd; symmetry in Heqqd; simpl.
- left.  simpl. apply Qeq_bool_iff in Heqqd.
  rewrite Heqqd.
  apply preserves_0.
- right. apply Qeq_bool_neq in Heqqd. apply Qap_CRap. assumption.
Qed.


Definition mkRelativeMove (rel : Q*Q) : DAtomicMove CR :=
  let (turnCurv, distance) := rel in
  mkDAtomicMoveQ  (mkAtomicMove (Qmult distance (width myCarDimZ)) (Qdiv turnCurv (minTR carGeo))).

Definition mkNamedRelativeMove (rel : Q*Q) :NameDAtomicMove :=
  ((EmptyString (* convert rel to string*) , EmptyString), mkRelativeMove rel).

Require Import ROSCOQ.geometry2D.
Definition relGlobalBound (initb :  BoundingRectangle Z) (extra : BoundingRectangle Q) : BoundingRectangle Z := 
let extra := (''' finerRes) * extra in
let rightExtraZ  := sfmap Qround.Qfloor ({|X:=' totalLength myCarDimZ; Y:=' width myCarDimZ|} * (maxxy extra)) in 
let leftExtraZ  :=  sfmap Qround.Qfloor ({|X:=' totalLength myCarDimZ; Y:=' width myCarDimZ|} * (minxy extra)) in 
initb + {| minxy := -leftExtraZ ; maxxy := rightExtraZ|}.

Definition animateSpaceReq 
   (moves : list (Q*Q))
   (extraSpace : BoundingRectangle Q)
   (framesPerMove : Z⁺) : string := 
  let sidewaysMove : list NameDAtomicMove := List.map mkNamedRelativeMove moves  in
  let initStp := (mkRenderingInfo (EmptyString,EmptyString),initSt) in
  let cs := (finerMovesStates framesPerMove sidewaysMove initStp) in
  let namedLines : list ((string * string) * list (Line2D Z)) 
      := carStatesFrames cs in
  let boundRects : list (Line2D Z) 
    :=  List.map (computeBoundingRectLines∘snd) namedLines in
  let boundRectsCum : list (Line2D Z) 
    := fold_left_inter boundingUnion  boundRects 0 in
  let lineRects
    := List.zip namedLines  boundRectsCum in
  match lineRects return string with
  | [] => ""
  | (h,_)::tl => 
      let initb := computeBoundingRectLines (snd h) in
      let globalB :  (Line2D Z) 
        := relGlobalBound initb extraSpace in
      let (pp, textPos) := drawEnv globalB initb in 
      let textTikZ  : string -> string  
        := fun label => "\node[below right] at " ++ tikZPoint textPos 
            ++ "{" ++ label ++ "};" ++ newLineString in
      let frames :=
        List.map (fun p => 
        let bnd := snd p in
        let p := fst p in
        let preface :=  sconcat [pp;tikZFilledRect "green" bnd] in
          frameWithLines 
            (sconcat [ preface ; textTikZ (fst (fst p)); snd (fst p)])
            (snd p)) 
          lineRects in
      sconcat frames
  end.

Definition animateMoves
   (moves : list (Q*Q))
   (extraSpace : BoundingRectangle Q)
   (framesPerMove : Z⁺) : string := 
  let sidewaysMove : list NameDAtomicMove := List.map mkNamedRelativeMove moves  in
  let initStp := (mkRenderingInfo (EmptyString,EmptyString),initSt) in
  let cs := (finerMovesStates framesPerMove sidewaysMove initStp) in
  let namedLines : list ((string * string) * list (Line2D Z)) 
      := carStatesFrames cs in
      let frames :=
        List.map (fun p => frameWithLines "\newframe" (snd p))
          namedLines in
      sconcat frames.

Definition clipRect : BoundingRectangle Z :=
({| lstart := {|X:=-10000; Y:=-10000|}; lend := {|X:=10000; Y:=10000|} |})%Z.

Definition header : string :=
  "\begin{frame}\begin{tikzpicture}[scale=0.02]".

Definition footer : string :=
  "\end{tikzpicture}\end{frame}".

Definition animateMovesPic
   (moves : list (Q*Q))
   (extraSpace : BoundingRectangle Q)
   (framesPerMove : Z⁺) : string := 
  let sidewaysMove : list NameDAtomicMove := List.map mkNamedRelativeMove moves  in
  let initStp := (mkRenderingInfo (EmptyString,EmptyString),initSt) in
  let cs := (finerMovesStates framesPerMove sidewaysMove initStp) in
  let frame (rs:NamedCarState) :=
      sconcat [
          header; newLineString;
            tikZBoundingClip clipRect; newLineString;
              drawCarFrameZPicture rs; newLineString;
                footer
        ] in
  sconcat (List.map frame cs).


Definition extra :BoundingRectangle Q :=
{| minxy := {|X:=Qmake 1 5; Y:= Qmake 1 10|}; maxxy := {|X:=Qmake 1 5; Y:= Qmake 1 1|} |}.


Definition moves : (list (Q*Q)) :=
[(1, Qmake 1 3); (-1, Qmake 1 3) ].

(*
Definition animationAutoBounding : string := 
  let (rs, sidewaysMove) := sidewaysMoveAndRightShift in
  let sidewaysMove := List.zip moveNamesSideways sidewaysMove  in
  let initStp := (mkRenderingInfo (sconcat spacedMoves),initSt) in
  let cs := (finerMovesStates 3 sidewaysMove initStp) in
  let namedLines : list ((string * string) * list (Line2D Z)) 
      := carStatesFrames cs in
  let allLines : list (Line2D Z) :=  (*cbvApply*) (flat_map snd) namedLines in
  let globalB : BoundingRectangle Z := computeBoundingRectLines allLines in
  match namedLines return string with
  | [] => ""
  | h::tl => 
      let initb := computeBoundingRectLines (snd h) in
      let (preface, textPos) := drawEnv globalB initb in 
      let textTikZ  : string -> string  
        := fun label => "\node[below right] at " ++ tikZPoint textPos 
            ++ "{" ++ label ++ "};" ++ newLineString in
      let frames := List.map (fun p => frameWithLines 
          (preface ++ textTikZ (fst p))  (snd p)) namedLines in
      sconcat frames
  end.
*)


(*
Definition fstMoveOnlyAnimation : string := 
  let (rs, sidewaysMove) := sidewaysMoveAndRightShift in
  let sidewaysMove := List.zip [EmptyString] [mazdaMaxCurvTurnMove ('singleMoveDistance)] in
  let initStp : string * carState CR := (EmptyString,initSt) in
  let cs : list NamedCarState := (finerMovesStates 10 sidewaysMove initStp) in
  let namedLines : list (string * list (Line2D Z)) := carStatesFrames  cs in
  let allLines : list (Line2D Z) :=  (*cbvApply*) (flat_map snd) namedLines in
  match namedLines return string with
  | [] => ""
  | h::tl => 
      let initb := computeBoundingRectLines (snd h) in
      (* the 2 items below are just guesses. TODO : compute them from the bounds derived in sidewaysMove.v *)
      let upExtra :  CR := '(Zdiv (width (myCarDimZ)) (5%Z)) in
      let downExtra : CR := '(Zdiv (width (myCarDimZ)) (5%Z)) in
      let globalB : BoundingRectangle Z := globalBound initb rs upExtra downExtra  in
      let (preface, textPos) := drawEnv globalB initb in 
      let textTikZ  : string -> string  
        := fun label => "\node[below right] at " ++ tikZPoint textPos 
            ++ "{" ++ label ++ "};" ++ newLineString in
      let frames := List.map (fun p => frameWithLines 
          (preface ++ textTikZ (fst p))  (snd p)) namedLines in
      sconcat frames
  end.
*)



Definition numXspaceSamples : positive := (60)%positive.

(** Hakell normaizes rationals whenever it wants. So ensuring that
the denominator is 100 in Coq is not sufficient after extraction.
We are extracting (just the type) of Coq rationals to Haskell rationals,
just to access printing, and conversion to/from floats.
*)
Definition spaceXplot : (list (Z ** (list Z))) :=
  let QtoZ q := Qround.Qfloor (q*(100)%Z) in
  let mf (p:(Q ** (list Q)))
     := let (a,b) := p in (QtoZ a, List.map QtoZ b) in
    (List.map mf (plotOptimalSidewaysMoveShiftMazdaQ eps eps numXspaceSamples)).

Definition spaceXplotn (n:nat) : list (Z*Z):=
  List.map 
    (fun (p:(Z ** (list Z))) => let (a,b) := p in (fst p, nth n b 0%Z)) 
    spaceXplot.

Definition endLine (s:string) : string := sconcat [s; newLineString].

Definition colorAndNames : (list (string * string )) :=
[
  ("red" , "angle (degrees)");
  ("green" , "upward shift");
  ("blue" , "straight distance");
  ("magenta" , "wriggle X space");
  ("yellow" , "straight X space")
].

(*Definition singleMoveDistance :Z :=25. *)


Definition spaceXplotnStr (n:nat) : string :=
  let (color, name) := nth n colorAndNames ("exception","garbage") in
  let preamble n :=
    sconcat ["\addplot[color="; color ; "] coordinates {"] in
  let cs:=
    (sconcat (List.map 
            (fun p => endLine (showZZ p)) 
            (spaceXplotn n))) in
    sconcat [preamble n; cs ; "}; \addlegendentry{";name;"}" 
      ; newLineString; newLineString].
End simulator.

Definition spaceXplotStr : string := sconcat (List.map  spaceXplotnStr (seq 0 5)).


(*
Definition toPrint : string := animateSpaceReqOptimalMove Mazda3Sedan2014sGT (4)%positive. *)



Print extra.
Definition toPrint : string := animateMovesPic Mazda3Sedan2014sGT moves extra (4)%positive.

Close Scope string_scope.
Locate posCompareContAbstract43820948120402312.
Extraction "simulator.hs"  (*animation spaceXplot *) toPrint 
  ExtrHaskellQ.posCompareContAbstract43820948120402312.