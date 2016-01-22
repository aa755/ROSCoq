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

  Require Import IRMisc.LegacyIRRing.

Require Import atomicMoves.

Require Export CartIR.

Require Import String.

(*Require Import haskellExtractionDirectives.*)
Require Import ocamlExtractionDirectives.
  
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

Definition carStateAfterAtomicMove 
  (cs : carState CR) (dm : @DAtomicMove CR _ _ _): carState CR:=
  {|csrigid2D := stateAfterAtomicMove (csrigid2D cs) dm
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

Definition tikZFilledRect (color : string) (l: Line2D Z) : string :=
  "\draw[fill=" ++ color  ++ "," ++ color ++ "]" ++ tikZPoint (lstart l) 
  ++ " rectangle " ++ tikZPoint (lend l) ++ ";" ++ newLineString.

Definition tikZColoredLine (color : string) (l: Line2D Z) : string :=
  "\draw[" ++ color ++ "]" ++ tikZPoint (lstart l) ++ "--" ++ tikZPoint (lend l) ++ ";" ++
  newLineString.

Definition tikZLines (l: list (Line2D Z)) : string :=
  sconcat  (List.map tikZLine l).

Definition tikZOptions : string :=
 "[scale=0.03]".
 
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

Definition carWheels (θ : CR) : list (Line2D CR) := 
  List.map 
    (centredLineAtAngle θ ((lengthFront cd) * '(Qmake 1 8)))
    [leftWheelCenter; rightWheelCenter].

Definition drawCarZAux  (θ : CR) : list (Line2D Z):=
  List.map (roundLineRZ eps) ((carOutline cd cs)++carWheels θ).


Definition drawCarTikZOld (θ : CR) : string := 
  tikZLines (drawCarZAux θ).
  
End CornerPos.

Definition  comparisonAsZ  (c : Datatypes.comparison) : Z :=
match c with
| Datatypes.Eq => 0
| Datatypes.Lt => -1
| Datatypes.Gt => 1
end.


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

Definition myCarDimZ : CarDimensions Z :=
{|lengthFront :=  60; lengthBack :=  15;
 width := 25|}.
Close Scope Z_scope.



Definition myCarDim : CarDimensions CR := 'myCarDimZ.
 

Definition initSt : carState CR :=
 {| csrigid2D := {|pos2D := 0; θ2D := 0|}; cs_tc :=0 |} .


Global Instance  CastQposCR : Cast Qpos CR := fun x => inject_Q_CR (QposAsQ x).

Require Import MathClasses.interfaces.orders.

Definition mkQTurnMove (t:Qpos) (d:CR): DAtomicMove CR.
  exists {|am_distance := d ; am_tc := 't|}.
  simpl. right. right. clear.
  exists t. simpl. 
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  rewrite minus_0_r.
  reflexivity.
Defined.

Typeclasses eauto := 10.

Definition mkNegQTurnMove (t:Qpos) (d:CR): DAtomicMove CR.
  exists {|am_distance := d ; am_tc := -'t|}.
  simpl. right. left. clear.
  exists t. simpl. 
  fold (CRopp).
  fold (CRplus).
  fold (@negate CR _).
  fold (@plus CR _).
  rewrite negate_involutive.
  rewrite plus_0_l.
  reflexivity.
Defined.  

  
Local Definition straightMove : DAtomicMove CR :=
  (mkStraightMove (cast Z CR 100))%Z.


Definition carStatesFrames  (l:list (string * carState CR)) : list (string * list (Line2D Z)) :=
(List.map (fun p=> (fst p, drawCarZ eps myCarDim (snd p))) l).


Fixpoint movesStates (l:list (DAtomicMove CR)) (init : carState CR) : 
  list (carState CR) :=
match l with
| [] => [init]
| hm::t => let midState := carStateAfterAtomicMove init hm in
      init::(movesStates t midState)
end.

Definition DAtomicMoves := list (DAtomicMove CR).

Definition getAtomicMove (d: (DAtomicMove CR)) : AtomicMove CR := projT1 d.


Definition DWriggle (t:Qpos) (d:CR) : DAtomicMoves 
    :=  [mkQTurnMove t d; mkNegQTurnMove t (-d)].

(*
Lemma DWriggleSame : forall (t:Qpos) (d:CR), 
  List.map getAtomicMove (DWriggle t d) = Wriggle ('t) d.
Proof.
  intros. reflexivity.
Qed.
*)  


      
Definition DSideways (t:Qpos) (dw ds:CR) : DAtomicMoves 
    := (DWriggle t dw) ++ [mkStraightMove ds] 
        ++ (DAtomicMovesInv (DWriggle t dw))
        ++ [mkStraightMove (- ds * cos (2 * 't * dw))].

(*
Lemma DSidewaysSame : forall (t:Qpos) (dw ds :CR), 
  List.map getAtomicMove (DSideways t dw ds) = SidewaysMove ('t) dw ds.
Proof.
  intros. reflexivity.
Qed.
*)

Fixpoint mapDiagonal  `(f: A->A) (prefix tail: list A) : list (list A) :=
match tail with
| [] => []
| h::tl => (prefix ++ ((f h)::tl))::(mapDiagonal f (prefix++[h]) tl)
end.

Local Definition wriggleMove : DAtomicMoves :=
(DWriggle (QposMake 1 200) (cast Z CR 30))%Z.


(** turn radius, which is inverse of turn curvature, is 200*)
Local Definition sidewaysMove : DAtomicMoves :=
  (DSideways (QposMake 1 50) (cast Z CR 15) (cast Z CR 10))%Z . 

Open Scope string_scope.
Definition moveNamesWriggle : list string := 
  ["\hll{(c,d)}; (-c,-d)" ;"(c,d); \hll{(-c,-d)}"].

Definition initStNameWriggle : string := 
  "(c,d); (-c,-d)".

Definition atomicMoveNamesSideways : list string := 
  ["(c,d)"; "(-c,-d)"; "$\;$(0,d')" ; "$\;$(-c,d)" ; "(c,-d)"; "$\;$(0,d'cos 2cd)"].

Local Definition spacedMoves := List.map (fun x => x++" ")atomicMoveNamesSideways.

Definition moveNamesSideways : list string := 
  List.map sconcat (mapDiagonal (fun x => sconcat ["\hll{";x;"}"]) [] spacedMoves).

Close Scope string_scope.

Definition NameDAtomicMove := prod string  (DAtomicMove CR).


Definition scaleAtomicMove (m: AtomicMove CR) (s:CR): AtomicMove CR:=
 {|am_tc := am_tc m; am_distance := s*(am_distance m) |}.
 
Definition DscaleAtomicMove  (m: (DAtomicMove CR)) (s:Q) : (DAtomicMove CR) :=
  existT _ (scaleAtomicMove (getAtomicMove m) (inject_Q_CR s)) (projT2 m).
 
Definition finerAtomicMoves (d:Z⁺) (m: (DAtomicMove CR)) : list (DAtomicMove CR) :=
  List.map (DscaleAtomicMove m) (equiMidPoints d).

Definition NamedCarState := prod string  (carState CR).

Definition finerStates (d:Z⁺) (dm : NameDAtomicMove) (init : carState CR) : 
  NamedCarState * list NamedCarState :=
  let (name,dm) := dm in
  ((name,carStateAfterAtomicMove init dm),
    List.map (fun m => (name,carStateAfterAtomicMove init m)) (finerAtomicMoves d dm)).

Fixpoint finerMovesStates (d:Z⁺) (l:list NameDAtomicMove) (init : NamedCarState) : 
   list NamedCarState :=
match l with
| [] => ( [init])
| hm::t => let (midState,interS) := finerStates d hm (snd init) in
          ([init]++(interS)++(finerMovesStates d t midState))
end.

Definition epsd : Z := 3*finerRes.
Definition textHt : Z := 25*finerRes.

Definition Rect2D := Line2D.

Definition sideCars (b init :BoundingRectangle Z): (BoundingRectangle Z) * list (Rect2D Z) :=
  let cardim : Cart2D Z  := (sameXY finerRes)*{|X:= (lengthFront myCarDimZ) ; Y:= 2 * (width myCarDimZ) |} in
  let ymax := Y (lend init) in
  let lcarMaxXY : Cart2D Z := {|X:= X (lstart b) - epsd ; Y:= ymax |}  in
  let rcarMinXY : Cart2D Z := {|X:= X (lend b) + epsd ; Y:= ymax - (Y cardim) |}  in
  (boundingUnion b {|lstart := lcarMaxXY - cardim; lend := rcarMinXY + cardim |},
    [
      {|lstart := lcarMaxXY - cardim; lend := lcarMaxXY |} ;
      {|lstart := rcarMinXY ; lend := rcarMinXY + cardim |}
    ]).
    


Definition extendRectForText (b:BoundingRectangle Z)  : BoundingRectangle Z :=
  {|lstart := (lstart b) - {|X:= 0 ; Y:= textHt  |}; lend := (lend b) + {|X:= 0 ; Y:= textHt  |} |}.
  
Open Scope string_scope.

Definition drawEnv (b init:BoundingRectangle Z)  : string * Cart2D Z:=
  let (bc, sc) := sideCars b init in
  let textPos := lstart bc in
  let bf := extendRectForText bc in
  let bottomLineStart := {| X := X (lstart bc); Y := Y (lstart bc) - epsd |} in
  let bottomLineEnd := {| X := X (lend bc); Y := Y (lstart bc) - epsd |} in
  let bottomLineZ   := {|lstart := bottomLineStart; lend := bottomLineEnd|} in
  let clip : string :=  tikZBoundingClip bf in
  let sideCars : list string :=  List.map  (tikZFilledRect "red") sc in
  let bottomLine : string :=  tikZColoredLine "red" bottomLineZ in 
  (sconcat (sideCars ++ [clip;bottomLine]), textPos).
  

Definition frameWithLines (preface:string) (lines : list (Line2D Z)) : string :=
  beamerFrameHeaderFooter "hello"
    (tikZHeaderFooter (preface ++ (tikZLines lines))).


Extract Inlined Constant cbvApply => "(Prelude.$!)".  

Definition animation : string := 
  let sidewaysMove := List.zip moveNamesSideways sidewaysMove  in
  let initStp := (sconcat spacedMoves,initSt) in
  let cs := (finerMovesStates 3 sidewaysMove initStp) in
  let namedLines : list (string ** list (Line2D Z)) := carStatesFrames  cs in
  let allLines : list (Line2D Z) :=  cbvApply (flat_map snd) namedLines in
  let globalB := computeBoundingRectLines allLines in
  match namedLines with
  | [] => ""
  | h::tl => 
      let initb := computeBoundingRectLines (snd h) in
      let (preface, textPos) := drawEnv globalB initb in 
      let textTikZ  : string -> string  
        := fun label => "\node[below right] at " ++ tikZPoint textPos 
            ++ "{" ++ label ++ "};" ++ newLineString in
      let frames := List.map (fun p => frameWithLines (preface ++ textTikZ (fst p)) (snd p)) namedLines in
      sconcat frames
  end.

Require Import sidewaysMoveImpl.

Axiom oQtoString : option Q -> string.
(** [Z] maps to [Prelude.Integer] and [string] map to Prelude.?? . 
  So Prelude.show works *)
Extract Constant oQtoString => "(Prelude.show)".

Definition optimalParam : string := oQtoString finalSoln.

(*
Eval vm_compute in finalSoln.
*)

Example ex1 : (131196 # 3288200 == 32799 # 822050)%Q.
vm_compute. reflexivity.
Abort.

Definition toPrint : string := optimalParam.
  
Close Scope string_scope.

Extraction "simulator.hs" toPrint.