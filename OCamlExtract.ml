(* scons: Reading SConscript files ...
scons: done reading SConscript files.
scons: Building targets ...
coqc extractOcaml -R . ROSCOQ -R ../../../ssrcorn CoRN -R ../../../ssrcorn/math-classes/src MathClasses
     = 2718%Z
     : Z *)

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val plus : nat -> nat -> nat **)

let rec plus n0 m =
  match n0 with
  | O -> m
  | S p -> S (plus p m)

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  match n0 with
  | O -> x
  | S n' -> f (nat_iter n' f x)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| True -> ReflectT
| False -> ReflectF

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q0 -> XO (succ q0)
       | XO q0 -> XI q0
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q0 ->
    (match q0 with
     | XH -> IsNul
     | _ -> IsPos (pred q0))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont p q0 r
       | XO q0 -> compare_cont p q0 Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont p q0 Lt
       | XO q0 -> compare_cont p q0 r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> eqb p0 q1
       | _ -> False)
    | XO p0 ->
      (match q0 with
       | XO q1 -> eqb p0 q1
       | _ -> False)
    | XH ->
      (match q0 with
       | XH -> True
       | _ -> False)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)
  
  let sqrtrem_step f g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       (match leb s' r' with
        | True -> Pair ((XI s), (sub_mask r' s'))
        | False -> Pair ((XO s), (IsPos r')))
     | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> (positive, mask) prod **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)
  
  let rec ggcdn n0 a b =
    match n0 with
    | O -> Pair (XH, (Pair (a, b)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n1 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI p ->
            let Pair (g, p0) = ggcdn n1 a0 b in
            let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))
  
  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> XI (coq_lor p0 q1)
       | XO q1 -> XI (coq_lor p0 q1)
       | XH -> p)
    | XO p0 ->
      (match q0 with
       | XI q1 -> XI (coq_lor p0 q1)
       | XO q1 -> XO (coq_lor p0 q1)
       | XH -> XI p0)
    | XH ->
      (match q0 with
       | XO q1 -> XI q1
       | _ -> q0)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> coq_Nsucc_double (coq_land p0 q1)
       | XO q1 -> coq_Ndouble (coq_land p0 q1)
       | XH -> Npos XH)
    | XO p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (coq_land p0 q1)
       | XO q1 -> coq_Ndouble (coq_land p0 q1)
       | XH -> N0)
    | XH ->
      (match q0 with
       | XO q1 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (ldiff p0 q1)
       | XO q1 -> coq_Nsucc_double (ldiff p0 q1)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (ldiff p0 q1)
       | XO q1 -> coq_Ndouble (ldiff p0 q1)
       | XH -> Npos p)
    | XH ->
      (match q0 with
       | XO q1 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (coq_lxor p0 q1)
       | XO q1 -> coq_Nsucc_double (coq_lxor p0 q1)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q0 with
       | XI q1 -> coq_Nsucc_double (coq_lxor p0 q1)
       | XO q1 -> coq_Ndouble (coq_lxor p0 q1)
       | XH -> Npos (XI p0))
    | XH ->
      (match q0 with
       | XI q1 -> Npos (XO q1)
       | XO q1 -> Npos (XI q1)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> True
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> False
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> True
       | S n1 -> False)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> True
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> False
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> True
       | Npos p0 -> False)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q0 -> XO (succ q0)
       | XO q0 -> XI q0
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q0 ->
    (match q0 with
     | XH -> IsNul
     | _ -> IsPos (pred q0))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont p q0 r
       | XO q0 -> compare_cont p q0 Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont p q0 Lt
       | XO q0 -> compare_cont p q0 r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> eqb p0 q1
       | _ -> False)
    | XO p0 ->
      (match q0 with
       | XO q1 -> eqb p0 q1
       | _ -> False)
    | XH ->
      (match q0 with
       | XH -> True
       | _ -> False)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)
  
  let sqrtrem_step f g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       (match leb s' r' with
        | True -> Pair ((XI s), (sub_mask r' s'))
        | False -> Pair ((XO s), (IsPos r')))
     | _ -> Pair ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> (positive, mask) prod **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)
  
  let rec ggcdn n0 a b =
    match n0 with
    | O -> Pair (XH, (Pair (a, b)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n1 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI p ->
            let Pair (g, p0) = ggcdn n1 a0 b in
            let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n1 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))
  
  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> XI (coq_lor p0 q1)
       | XO q1 -> XI (coq_lor p0 q1)
       | XH -> p)
    | XO p0 ->
      (match q0 with
       | XI q1 -> XI (coq_lor p0 q1)
       | XO q1 -> XO (coq_lor p0 q1)
       | XH -> XI p0)
    | XH ->
      (match q0 with
       | XO q1 -> XI q1
       | _ -> q0)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> coq_Nsucc_double (coq_land p0 q1)
       | XO q1 -> coq_Ndouble (coq_land p0 q1)
       | XH -> Npos XH)
    | XO p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (coq_land p0 q1)
       | XO q1 -> coq_Ndouble (coq_land p0 q1)
       | XH -> N0)
    | XH ->
      (match q0 with
       | XO q1 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (ldiff p0 q1)
       | XO q1 -> coq_Nsucc_double (ldiff p0 q1)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (ldiff p0 q1)
       | XO q1 -> coq_Ndouble (ldiff p0 q1)
       | XH -> Npos p)
    | XH ->
      (match q0 with
       | XO q1 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q0 =
    match p with
    | XI p0 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (coq_lxor p0 q1)
       | XO q1 -> coq_Nsucc_double (coq_lxor p0 q1)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q0 with
       | XI q1 -> coq_Nsucc_double (coq_lxor p0 q1)
       | XO q1 -> coq_Ndouble (coq_lxor p0 q1)
       | XH -> Npos (XI p0))
    | XH ->
      (match q0 with
       | XI q1 -> Npos (XO q1)
       | XO q1 -> Npos (XI q1)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> True
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> False
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> True
       | S n1 -> False)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> True
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 ->
         False
       | Npos n1 ->
         testbit
           p0
           (pred_N
             n1))
    | XH ->
      (match n0 with
       | N0 ->
         True
       | Npos p0 ->
         False)
  
  (** val iter_op :
      ('a1
      ->
      'a1
      ->
      'a1)
      ->
      positive
      ->
      'a1
      ->
      'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 ->
      op
        a
        (iter_op
          op
          p0
          (op
            a
            a))
    | XO p0 ->
      iter_op
        op
        p0
        (op
          a
          a)
    | XH ->
      a
  
  (** val to_nat :
      positive
      ->
      nat **)
  
  let to_nat x =
    iter_op
      plus
      x
      (S
      O)
  
  (** val of_nat :
      nat
      ->
      positive **)
  
  let rec of_nat = function
  | O ->
    XH
  | S x ->
    (match x with
     | O ->
       XH
     | S n1 ->
       succ
         (of_nat
           x))
  
  (** val of_succ_nat :
      nat
      ->
      positive **)
  
  let rec of_succ_nat = function
  | O ->
    XH
  | S x ->
    succ
      (of_succ_nat
        x)
  
  (** val eq_dec :
      positive
      ->
      positive
      ->
      sumbool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 ->
         eq_dec
           p0
           p1
       | _ ->
         Right)
    | XO p0 ->
      (match y0 with
       | XO p1 ->
         eq_dec
           p0
           p1
       | _ ->
         Right)
    | XH ->
      (match y0 with
       | XH ->
         Left
       | _ ->
         Right)
  
  (** val peano_rect :
      'a1
      ->
      (positive
      ->
      'a1
      ->
      'a1)
      ->
      positive
      ->
      'a1 **)
  
  let rec peano_rect a f p =
    let f2 =
      peano_rect
        (f
          XH
          a)
        (fun p0 x ->
        f
          (succ
            (XO
            p0))
          (f
            (XO
            p0)
            x))
    in
    (match p with
     | XI q0 ->
       f
         (XO
         q0)
         (f2
           q0)
     | XO q0 ->
       f2
         q0
     | XH ->
       a)
  
  (** val peano_rec :
      'a1
      ->
      (positive
      ->
      'a1
      ->
      'a1)
      ->
      positive
      ->
      'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive
     * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1
      ->
      (positive
      ->
      coq_PeanoView
      ->
      'a1
      ->
      'a1)
      ->
      positive
      ->
      coq_PeanoView
      ->
      'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne ->
    f
  | PeanoSucc (p1,
               p2) ->
    f0
      p1
      p2
      (coq_PeanoView_rect
        f
        f0
        p1
        p2)
  
  (** val coq_PeanoView_rec :
      'a1
      ->
      (positive
      ->
      coq_PeanoView
      ->
      'a1
      ->
      'a1)
      ->
      positive
      ->
      coq_PeanoView
      ->
      'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne ->
    f
  | PeanoSucc (p1,
               p2) ->
    f0
      p1
      p2
      (coq_PeanoView_rec
        f
        f0
        p1
        p2)
  
  (** val peanoView_xO :
      positive
      ->
      coq_PeanoView
      ->
      coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne ->
    PeanoSucc
      (XH,
      PeanoOne)
  | PeanoSucc (p0,
               q1) ->
    PeanoSucc
      ((succ
         (XO
         p0)),
      (PeanoSucc
      ((XO
      p0),
      (peanoView_xO
        p0
        q1))))
  
  (** val peanoView_xI :
      positive
      ->
      coq_PeanoView
      ->
      coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne ->
    PeanoSucc
      ((succ
         XH),
      (PeanoSucc
      (XH,
      PeanoOne)))
  | PeanoSucc (p0,
               q1) ->
    PeanoSucc
      ((succ
         (XI
         p0)),
      (PeanoSucc
      ((XI
      p0),
      (peanoView_xI
        p0
        q1))))
  
  (** val peanoView :
      positive
      ->
      coq_PeanoView **)
  
  let rec peanoView = function
  | XI p0 ->
    peanoView_xI
      p0
      (peanoView
        p0)
  | XO p0 ->
    peanoView_xO
      p0
      (peanoView
        p0)
  | XH ->
    PeanoOne
  
  (** val coq_PeanoView_iter :
      'a1
      ->
      (positive
      ->
      'a1
      ->
      'a1)
      ->
      positive
      ->
      coq_PeanoView
      ->
      'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne ->
    a
  | PeanoSucc (p0,
               q1) ->
    f
      p0
      (coq_PeanoView_iter
        a
        f
        p0
        q1)
  
  (** val eqb_spec :
      positive
      ->
      positive
      ->
      reflect **)
  
  let eqb_spec x y =
    iff_reflect
      (eqb
        x
        y)
  
  (** val switch_Eq :
      comparison
      ->
      comparison
      ->
      comparison **)
  
  let switch_Eq c = function
  | Eq ->
    c
  | x ->
    x
  
  (** val mask2cmp :
      mask
      ->
      comparison **)
  
  let mask2cmp = function
  | IsNul ->
    Eq
  | IsPos p0 ->
    Gt
  | IsNeg ->
    Lt
  
  (** val leb_spec0 :
      positive
      ->
      positive
      ->
      reflect **)
  
  let leb_spec0 x y =
    iff_reflect
      (leb
        x
        y)
  
  (** val ltb_spec0 :
      positive
      ->
      positive
      ->
      reflect **)
  
  let ltb_spec0 x y =
    iff_reflect
      (ltb
        x
        y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        positive
        ->
        positive
        ->
        (positive
        ->
        positive
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c =
        compSpec2Type
          n0
          m
          (compare
            n0
            m)
      in
      (match c with
       | CompGtT ->
         compat
           n0
           (max
             n0
             m)
           __
           (hl
             __)
       | _ ->
         compat
           m
           (max
             n0
             m)
           __
           (hr
             __))
    
    (** val max_case :
        positive
        ->
        positive
        ->
        (positive
        ->
        positive
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong
        n0
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val max_dec :
        positive
        ->
        positive
        ->
        sumbool **)
    
    let max_dec n0 m =
      max_case
        n0
        m
        (fun x y _ h0 ->
        h0)
        Left
        Right
    
    (** val min_case_strong :
        positive
        ->
        positive
        ->
        (positive
        ->
        positive
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c =
        compSpec2Type
          n0
          m
          (compare
            n0
            m)
      in
      (match c with
       | CompGtT ->
         compat
           m
           (min
             n0
             m)
           __
           (hr
             __)
       | _ ->
         compat
           n0
           (min
             n0
             m)
           __
           (hl
             __))
    
    (** val min_case :
        positive
        ->
        positive
        ->
        (positive
        ->
        positive
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong
        n0
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val min_dec :
        positive
        ->
        positive
        ->
        sumbool **)
    
    let min_dec n0 m =
      min_case
        n0
        m
        (fun x y _ h0 ->
        h0)
        Left
        Right
   end
  
  (** val max_case_strong :
      positive
      ->
      positive
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong
      n0
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val max_case :
      positive
      ->
      positive
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong
      n0
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val max_dec :
      positive
      ->
      positive
      ->
      sumbool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      positive
      ->
      positive
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong
      n0
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val min_case :
      positive
      ->
      positive
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong
      n0
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val min_dec :
      positive
      ->
      positive
      ->
      sumbool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t
    =
    n
  
  (** val zero :
      n **)
  
  let zero =
    N0
  
  (** val one :
      n **)
  
  let one =
    Npos
      XH
  
  (** val two :
      n **)
  
  let two =
    Npos
      (XO
      XH)
  
  (** val succ_double :
      n
      ->
      n **)
  
  let succ_double = function
  | N0 ->
    Npos
      XH
  | Npos p ->
    Npos
      (XI
      p)
  
  (** val double :
      n
      ->
      n **)
  
  let double = function
  | N0 ->
    N0
  | Npos p ->
    Npos
      (XO
      p)
  
  (** val succ :
      n
      ->
      n **)
  
  let succ = function
  | N0 ->
    Npos
      XH
  | Npos p ->
    Npos
      (Coq_Pos.succ
        p)
  
  (** val pred :
      n
      ->
      n **)
  
  let pred = function
  | N0 ->
    N0
  | Npos p ->
    Coq_Pos.pred_N
      p
  
  (** val succ_pos :
      n
      ->
      positive **)
  
  let succ_pos = function
  | N0 ->
    XH
  | Npos p ->
    Coq_Pos.succ
      p
  
  (** val add :
      n
      ->
      n
      ->
      n **)
  
  let add n0 m =
    match n0 with
    | N0 ->
      m
    | Npos p ->
      (match m with
       | N0 ->
         n0
       | Npos q0 ->
         Npos
           (Coq_Pos.add
             p
             q0))
  
  (** val sub :
      n
      ->
      n
      ->
      n **)
  
  let sub n0 m =
    match n0 with
    | N0 ->
      N0
    | Npos n' ->
      (match m with
       | N0 ->
         n0
       | Npos m' ->
         (match Coq_Pos.sub_mask
                  n'
                  m' with
          | Coq_Pos.IsPos p ->
            Npos
              p
          | _ ->
            N0))
  
  (** val mul :
      n
      ->
      n
      ->
      n **)
  
  let mul n0 m =
    match n0 with
    | N0 ->
      N0
    | Npos p ->
      (match m with
       | N0 ->
         N0
       | Npos q0 ->
         Npos
           (Coq_Pos.mul
             p
             q0))
  
  (** val compare :
      n
      ->
      n
      ->
      comparison **)
  
  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 ->
         Eq
       | Npos m' ->
         Lt)
    | Npos n' ->
      (match m with
       | N0 ->
         Gt
       | Npos m' ->
         Coq_Pos.compare
           n'
           m')
  
  (** val eqb :
      n
      ->
      n
      ->
      bool **)
  
  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 ->
         True
       | Npos p ->
         False)
    | Npos p ->
      (match m with
       | N0 ->
         False
       | Npos q0 ->
         Coq_Pos.eqb
           p
           q0)
  
  (** val leb :
      n
      ->
      n
      ->
      bool **)
  
  let leb x y =
    match compare
            x
            y with
    | Gt ->
      False
    | _ ->
      True
  
  (** val ltb :
      n
      ->
      n
      ->
      bool **)
  
  let ltb x y =
    match compare
            x
            y with
    | Lt ->
      True
    | _ ->
      False
  
  (** val min :
      n
      ->
      n
      ->
      n **)
  
  let min n0 n' =
    match compare
            n0
            n' with
    | Gt ->
      n'
    | _ ->
      n0
  
  (** val max :
      n
      ->
      n
      ->
      n **)
  
  let max n0 n' =
    match compare
            n0
            n' with
    | Gt ->
      n0
    | _ ->
      n'
  
  (** val div2 :
      n
      ->
      n **)
  
  let div2 = function
  | N0 ->
    N0
  | Npos p0 ->
    (match p0 with
     | XI p ->
       Npos
         p
     | XO p ->
       Npos
         p
     | XH ->
       N0)
  
  (** val even :
      n
      ->
      bool **)
  
  let even = function
  | N0 ->
    True
  | Npos p ->
    (match p with
     | XO p0 ->
       True
     | _ ->
       False)
  
  (** val odd :
      n
      ->
      bool **)
  
  let odd n0 =
    negb
      (even
        n0)
  
  (** val pow :
      n
      ->
      n
      ->
      n **)
  
  let pow n0 = function
  | N0 ->
    Npos
      XH
  | Npos p0 ->
    (match n0 with
     | N0 ->
       N0
     | Npos q0 ->
       Npos
         (Coq_Pos.pow
           q0
           p0))
  
  (** val square :
      n
      ->
      n **)
  
  let square = function
  | N0 ->
    N0
  | Npos p ->
    Npos
      (Coq_Pos.square
        p)
  
  (** val log2 :
      n
      ->
      n **)
  
  let log2 = function
  | N0 ->
    N0
  | Npos p0 ->
    (match p0 with
     | XI p ->
       Npos
         (Coq_Pos.size
           p)
     | XO p ->
       Npos
         (Coq_Pos.size
           p)
     | XH ->
       N0)
  
  (** val size :
      n
      ->
      n **)
  
  let size = function
  | N0 ->
    N0
  | Npos p ->
    Npos
      (Coq_Pos.size
        p)
  
  (** val size_nat :
      n
      ->
      nat **)
  
  let size_nat = function
  | N0 ->
    O
  | Npos p ->
    Coq_Pos.size_nat
      p
  
  (** val pos_div_eucl :
      positive
      ->
      n
      ->
      (n,
      n)
      prod **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q0,
                r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        succ_double
          r
      in
      (match leb
               b
               r' with
       | True ->
         Pair
           ((succ_double
              q0),
           (sub
             r'
             b))
       | False ->
         Pair
           ((double
              q0),
           r'))
    | XO a' ->
      let Pair (q0,
                r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        double
          r
      in
      (match leb
               b
               r' with
       | True ->
         Pair
           ((succ_double
              q0),
           (sub
             r'
             b))
       | False ->
         Pair
           ((double
              q0),
           r'))
    | XH ->
      (match b with
       | N0 ->
         Pair
           (N0,
           (Npos
           XH))
       | Npos p ->
         (match p with
          | XH ->
            Pair
              ((Npos
              XH),
              N0)
          | _ ->
            Pair
              (N0,
              (Npos
              XH))))
  
  (** val div_eucl :
      n
      ->
      n
      ->
      (n,
      n)
      prod **)
  
  let div_eucl a b =
    match a with
    | N0 ->
      Pair
        (N0,
        N0)
    | Npos na ->
      (match b with
       | N0 ->
         Pair
           (N0,
           a)
       | Npos p ->
         pos_div_eucl
           na
           b)
  
  (** val div :
      n
      ->
      n
      ->
      n **)
  
  let div a b =
    fst
      (div_eucl
        a
        b)
  
  (** val modulo :
      n
      ->
      n
      ->
      n **)
  
  let modulo a b =
    snd
      (div_eucl
        a
        b)
  
  (** val gcd :
      n
      ->
      n
      ->
      n **)
  
  let gcd a b =
    match a with
    | N0 ->
      b
    | Npos p ->
      (match b with
       | N0 ->
         a
       | Npos q0 ->
         Npos
           (Coq_Pos.gcd
             p
             q0))
  
  (** val ggcd :
      n
      ->
      n
      ->
      (n,
      (n,
      n)
      prod)
      prod **)
  
  let ggcd a b =
    match a with
    | N0 ->
      Pair
        (b,
        (Pair
        (N0,
        (Npos
        XH))))
    | Npos p ->
      (match b with
       | N0 ->
         Pair
           (a,
           (Pair
           ((Npos
           XH),
           N0)))
       | Npos q0 ->
         let Pair (g,
                   p0) =
           Coq_Pos.ggcd
             p
             q0
         in
         let Pair (aa,
                   bb) =
           p0
         in
         Pair
         ((Npos
         g),
         (Pair
         ((Npos
         aa),
         (Npos
         bb)))))
  
  (** val sqrtrem :
      n
      ->
      (n,
      n)
      prod **)
  
  let sqrtrem = function
  | N0 ->
    Pair
      (N0,
      N0)
  | Npos p ->
    let Pair (s,
              m) =
      Coq_Pos.sqrtrem
        p
    in
    (match m with
     | Coq_Pos.IsPos r ->
       Pair
         ((Npos
         s),
         (Npos
         r))
     | _ ->
       Pair
         ((Npos
         s),
         N0))
  
  (** val sqrt :
      n
      ->
      n **)
  
  let sqrt = function
  | N0 ->
    N0
  | Npos p ->
    Npos
      (Coq_Pos.sqrt
        p)
  
  (** val coq_lor :
      n
      ->
      n
      ->
      n **)
  
  let coq_lor n0 m =
    match n0 with
    | N0 ->
      m
    | Npos p ->
      (match m with
       | N0 ->
         n0
       | Npos q0 ->
         Npos
           (Coq_Pos.coq_lor
             p
             q0))
  
  (** val coq_land :
      n
      ->
      n
      ->
      n **)
  
  let coq_land n0 m =
    match n0 with
    | N0 ->
      N0
    | Npos p ->
      (match m with
       | N0 ->
         N0
       | Npos q0 ->
         Coq_Pos.coq_land
           p
           q0)
  
  (** val ldiff :
      n
      ->
      n
      ->
      n **)
  
  let rec ldiff n0 m =
    match n0 with
    | N0 ->
      N0
    | Npos p ->
      (match m with
       | N0 ->
         n0
       | Npos q0 ->
         Coq_Pos.ldiff
           p
           q0)
  
  (** val coq_lxor :
      n
      ->
      n
      ->
      n **)
  
  let coq_lxor n0 m =
    match n0 with
    | N0 ->
      m
    | Npos p ->
      (match m with
       | N0 ->
         n0
       | Npos q0 ->
         Coq_Pos.coq_lxor
           p
           q0)
  
  (** val shiftl_nat :
      n
      ->
      nat
      ->
      n **)
  
  let shiftl_nat a n0 =
    nat_iter
      n0
      double
      a
  
  (** val shiftr_nat :
      n
      ->
      nat
      ->
      n **)
  
  let shiftr_nat a n0 =
    nat_iter
      n0
      div2
      a
  
  (** val shiftl :
      n
      ->
      n
      ->
      n **)
  
  let shiftl a n0 =
    match a with
    | N0 ->
      N0
    | Npos a0 ->
      Npos
        (Coq_Pos.shiftl
          a0
          n0)
  
  (** val shiftr :
      n
      ->
      n
      ->
      n **)
  
  let shiftr a = function
  | N0 ->
    a
  | Npos p ->
    Coq_Pos.iter
      p
      div2
      a
  
  (** val testbit_nat :
      n
      ->
      nat
      ->
      bool **)
  
  let testbit_nat = function
  | N0 ->
    (fun x ->
      False)
  | Npos p ->
    Coq_Pos.testbit_nat
      p
  
  (** val testbit :
      n
      ->
      n
      ->
      bool **)
  
  let testbit a n0 =
    match a with
    | N0 ->
      False
    | Npos p ->
      Coq_Pos.testbit
        p
        n0
  
  (** val to_nat :
      n
      ->
      nat **)
  
  let to_nat = function
  | N0 ->
    O
  | Npos p ->
    Coq_Pos.to_nat
      p
  
  (** val of_nat :
      nat
      ->
      n **)
  
  let of_nat = function
  | O ->
    N0
  | S n' ->
    Npos
      (Coq_Pos.of_succ_nat
        n')
  
  (** val iter :
      n
      ->
      ('a1
      ->
      'a1)
      ->
      'a1
      ->
      'a1 **)
  
  let iter n0 f x =
    match n0 with
    | N0 ->
      x
    | Npos p ->
      Coq_Pos.iter
        p
        f
        x
  
  (** val eq_dec :
      n
      ->
      n
      ->
      sumbool **)
  
  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 ->
         Left
       | Npos p ->
         Right)
    | Npos x ->
      (match m with
       | N0 ->
         Right
       | Npos p0 ->
         Coq_Pos.eq_dec
           x
           p0)
  
  (** val discr :
      n
      ->
      positive
      sumor **)
  
  let discr = function
  | N0 ->
    Inright
  | Npos p ->
    Inleft
      p
  
  (** val binary_rect :
      'a1
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      n
      ->
      'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' =
      fun p ->
      f2
        (Npos
        p)
    in
    let fS2' =
      fun p ->
      fS2
        (Npos
        p)
    in
    (match n0 with
     | N0 ->
       f0
     | Npos p ->
       let rec f = function
       | XI p1 ->
         fS2'
           p1
           (f
             p1)
       | XO p1 ->
         f2'
           p1
           (f
             p1)
       | XH ->
         fS2
           N0
           f0
       in f
            p)
  
  (** val binary_rec :
      'a1
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      n
      ->
      'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect :
      'a1
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      n
      ->
      'a1 **)
  
  let peano_rect f0 f n0 =
    let f' =
      fun p ->
      f
        (Npos
        p)
    in
    (match n0 with
     | N0 ->
       f0
     | Npos p ->
       Coq_Pos.peano_rect
         (f
           N0
           f0)
         f'
         p)
  
  (** val peano_rec :
      'a1
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      n
      ->
      'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 :
      n
      ->
      n
      ->
      reflect **)
  
  let leb_spec0 x y =
    iff_reflect
      (leb
        x
        y)
  
  (** val ltb_spec0 :
      n
      ->
      n
      ->
      reflect **)
  
  let ltb_spec0 x y =
    iff_reflect
      (ltb
        x
        y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion :
      'a1
      ->
      (n
      ->
      'a1
      ->
      'a1)
      ->
      n
      ->
      'a1 **)
  
  let recursion x =
    peano_rect
      x
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up :
      n
      ->
      n **)
  
  let sqrt_up a =
    match compare
            N0
            a with
    | Lt ->
      succ
        (sqrt
          (pred
            a))
    | _ ->
      N0
  
  (** val log2_up :
      n
      ->
      n **)
  
  let log2_up a =
    match compare
            (Npos
            XH)
            a with
    | Lt ->
      succ
        (log2
          (pred
            a))
    | _ ->
      N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm :
      n
      ->
      n
      ->
      n **)
  
  let lcm a b =
    mul
      a
      (div
        b
        (gcd
          a
          b))
  
  (** val eqb_spec :
      n
      ->
      n
      ->
      reflect **)
  
  let eqb_spec x y =
    iff_reflect
      (eqb
        x
        y)
  
  (** val b2n :
      bool
      ->
      n **)
  
  let b2n = function
  | True ->
    Npos
      XH
  | False ->
    N0
  
  (** val setbit :
      n
      ->
      n
      ->
      n **)
  
  let setbit a n0 =
    coq_lor
      a
      (shiftl
        (Npos
        XH)
        n0)
  
  (** val clearbit :
      n
      ->
      n
      ->
      n **)
  
  let clearbit a n0 =
    ldiff
      a
      (shiftl
        (Npos
        XH)
        n0)
  
  (** val ones :
      n
      ->
      n **)
  
  let ones n0 =
    pred
      (shiftl
        (Npos
        XH)
        n0)
  
  (** val lnot :
      n
      ->
      n
      ->
      n **)
  
  let lnot a n0 =
    coq_lxor
      a
      (ones
        n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        n
        ->
        n
        ->
        (n
        ->
        n
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c =
        compSpec2Type
          n0
          m
          (compare
            n0
            m)
      in
      (match c with
       | CompGtT ->
         compat
           n0
           (max
             n0
             m)
           __
           (hl
             __)
       | _ ->
         compat
           m
           (max
             n0
             m)
           __
           (hr
             __))
    
    (** val max_case :
        n
        ->
        n
        ->
        (n
        ->
        n
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong
        n0
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val max_dec :
        n
        ->
        n
        ->
        sumbool **)
    
    let max_dec n0 m =
      max_case
        n0
        m
        (fun x y _ h0 ->
        h0)
        Left
        Right
    
    (** val min_case_strong :
        n
        ->
        n
        ->
        (n
        ->
        n
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        (__
        ->
        'a1)
        ->
        'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c =
        compSpec2Type
          n0
          m
          (compare
            n0
            m)
      in
      (match c with
       | CompGtT ->
         compat
           m
           (min
             n0
             m)
           __
           (hr
             __)
       | _ ->
         compat
           n0
           (min
             n0
             m)
           __
           (hl
             __))
    
    (** val min_case :
        n
        ->
        n
        ->
        (n
        ->
        n
        ->
        __
        ->
        'a1
        ->
        'a1)
        ->
        'a1
        ->
        'a1
        ->
        'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong
        n0
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val min_dec :
        n
        ->
        n
        ->
        sumbool **)
    
    let min_dec n0 m =
      min_case
        n0
        m
        (fun x y _ h0 ->
        h0)
        Left
        Right
   end
  
  (** val max_case_strong :
      n
      ->
      n
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong
      n0
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val max_case :
      n
      ->
      n
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong
      n0
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val max_dec :
      n
      ->
      n
      ->
      sumbool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      n
      ->
      n
      ->
      (__
      ->
      'a1)
      ->
      (__
      ->
      'a1)
      ->
      'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong
      n0
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val min_case :
      n
      ->
      n
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong
      n0
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val min_dec :
      n
      ->
      n
      ->
      sumbool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t
    =
    z
  
  (** val zero :
      z **)
  
  let zero =
    Z0
  
  (** val one :
      z **)
  
  let one =
    Zpos
      XH
  
  (** val two :
      z **)
  
  let two =
    Zpos
      (XO
      XH)
  
  (** val double :
      z
      ->
      z **)
  
  let double = function
  | Z0 ->
    Z0
  | Zpos p ->
    Zpos
      (XO
      p)
  | Zneg p ->
    Zneg
      (XO
      p)
  
  (** val succ_double :
      z
      ->
      z **)
  
  let succ_double = function
  | Z0 ->
    Zpos
      XH
  | Zpos p ->
    Zpos
      (XI
      p)
  | Zneg p ->
    Zneg
      (Coq_Pos.pred_double
        p)
  
  (** val pred_double :
      z
      ->
      z **)
  
  let pred_double = function
  | Z0 ->
    Zneg
      XH
  | Zpos p ->
    Zpos
      (Coq_Pos.pred_double
        p)
  | Zneg p ->
    Zneg
      (XI
      p)
  
  (** val pos_sub :
      positive
      ->
      positive
      ->
      z **)
  
  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 ->
         double
           (pos_sub
             p
             q0)
       | XO q0 ->
         succ_double
           (pos_sub
             p
             q0)
       | XH ->
         Zpos
           (XO
           p))
    | XO p ->
      (match y with
       | XI q0 ->
         pred_double
           (pos_sub
             p
             q0)
       | XO q0 ->
         double
           (pos_sub
             p
             q0)
       | XH ->
         Zpos
           (Coq_Pos.pred_double
             p))
    | XH ->
      (match y with
       | XI q0 ->
         Zneg
           (XO
           q0)
       | XO q0 ->
         Zneg
           (Coq_Pos.pred_double
             q0)
       | XH ->
         Z0)
  
  (** val add :
      z
      ->
      z
      ->
      z **)
  
  let add x y =
    match x with
    | Z0 ->
      y
    | Zpos x' ->
      (match y with
       | Z0 ->
         x
       | Zpos y' ->
         Zpos
           (Coq_Pos.add
             x'
             y')
       | Zneg y' ->
         pos_sub
           x'
           y')
    | Zneg x' ->
      (match y with
       | Z0 ->
         x
       | Zpos y' ->
         pos_sub
           y'
           x'
       | Zneg y' ->
         Zneg
           (Coq_Pos.add
             x'
             y'))
  
  (** val opp :
      z
      ->
      z **)
  
  let opp = function
  | Z0 ->
    Z0
  | Zpos x0 ->
    Zneg
      x0
  | Zneg x0 ->
    Zpos
      x0
  
  (** val succ :
      z
      ->
      z **)
  
  let succ x =
    add
      x
      (Zpos
      XH)
  
  (** val pred :
      z
      ->
      z **)
  
  let pred x =
    add
      x
      (Zneg
      XH)
  
  (** val sub :
      z
      ->
      z
      ->
      z **)
  
  let sub m n0 =
    add
      m
      (opp
        n0)
  
  (** val mul :
      z
      ->
      z
      ->
      z **)
  
  let mul x y =
    match x with
    | Z0 ->
      Z0
    | Zpos x' ->
      (match y with
       | Z0 ->
         Z0
       | Zpos y' ->
         Zpos
           (Coq_Pos.mul
             x'
             y')
       | Zneg y' ->
         Zneg
           (Coq_Pos.mul
             x'
             y'))
    | Zneg x' ->
      (match y with
       | Z0 ->
         Z0
       | Zpos y' ->
         Zneg
           (Coq_Pos.mul
             x'
             y')
       | Zneg y' ->
         Zpos
           (Coq_Pos.mul
             x'
             y'))
  
  (** val pow_pos :
      z
      ->
      positive
      ->
      z **)
  
  let pow_pos z0 n0 =
    Coq_Pos.iter
      n0
      (mul
        z0)
      (Zpos
      XH)
  
  (** val pow :
      z
      ->
      z
      ->
      z **)
  
  let pow x = function
  | Z0 ->
    Zpos
      XH
  | Zpos p ->
    pow_pos
      x
      p
  | Zneg p ->
    Z0
  
  (** val square :
      z
      ->
      z **)
  
  let square = function
  | Z0 ->
    Z0
  | Zpos p ->
    Zpos
      (Coq_Pos.square
        p)
  | Zneg p ->
    Zpos
      (Coq_Pos.square
        p)
  
  (** val compare :
      z
      ->
      z
      ->
      comparison **)
  
  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 ->
         Eq
       | Zpos y' ->
         Lt
       | Zneg y' ->
         Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' ->
         Coq_Pos.compare
           x'
           y'
       | _ ->
         Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' ->
         compOpp
           (Coq_Pos.compare
             x'
             y')
       | _ ->
         Lt)
  
  (** val sgn :
      z
      ->
      z **)
  
  let sgn = function
  | Z0 ->
    Z0
  | Zpos p ->
    Zpos
      XH
  | Zneg p ->
    Zneg
      XH
  
  (** val leb :
      z
      ->
      z
      ->
      bool **)
  
  let leb x y =
    match compare
            x
            y with
    | Gt ->
      False
    | _ ->
      True
  
  (** val ltb :
      z
      ->
      z
      ->
      bool **)
  
  let ltb x y =
    match compare
            x
            y with
    | Lt ->
      True
    | _ ->
      False
  
  (** val geb :
      z
      ->
      z
      ->
      bool **)
  
  let geb x y =
    match compare
            x
            y with
    | Lt ->
      False
    | _ ->
      True
  
  (** val gtb :
      z
      ->
      z
      ->
      bool **)
  
  let gtb x y =
    match compare
            x
            y with
    | Gt ->
      True
    | _ ->
      False
  
  (** val eqb :
      z
      ->
      z
      ->
      bool **)
  
  let rec eqb x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 ->
         True
       | _ ->
         False)
    | Zpos p ->
      (match y with
       | Zpos q0 ->
         Coq_Pos.eqb
           p
           q0
       | _ ->
         False)
    | Zneg p ->
      (match y with
       | Zneg q0 ->
         Coq_Pos.eqb
           p
           q0
       | _ ->
         False)
  
  (** val max :
      z
      ->
      z
      ->
      z **)
  
  let max n0 m =
    match compare
            n0
            m with
    | Lt ->
      m
    | _ ->
      n0
  
  (** val min :
      z
      ->
      z
      ->
      z **)
  
  let min n0 m =
    match compare
            n0
            m with
    | Gt ->
      m
    | _ ->
      n0
  
  (** val abs :
      z
      ->
      z **)
  
  let abs = function
  | Zneg p ->
    Zpos
      p
  | x ->
    x
  
  (** val abs_nat :
      z
      ->
      nat **)
  
  let abs_nat = function
  | Z0 ->
    O
  | Zpos p ->
    Coq_Pos.to_nat
      p
  | Zneg p ->
    Coq_Pos.to_nat
      p
  
  (** val abs_N :
      z
      ->
      n **)
  
  let abs_N = function
  | Z0 ->
    N0
  | Zpos p ->
    Npos
      p
  | Zneg p ->
    Npos
      p
  
  (** val to_nat :
      z
      ->
      nat **)
  
  let to_nat = function
  | Zpos p ->
    Coq_Pos.to_nat
      p
  | _ ->
    O
  
  (** val to_N :
      z
      ->
      n **)
  
  let to_N = function
  | Zpos p ->
    Npos
      p
  | _ ->
    N0
  
  (** val of_nat :
      nat
      ->
      z **)
  
  let of_nat = function
  | O ->
    Z0
  | S n1 ->
    Zpos
      (Coq_Pos.of_succ_nat
        n1)
  
  (** val of_N :
      n
      ->
      z **)
  
  let of_N = function
  | N0 ->
    Z0
  | Npos p ->
    Zpos
      p
  
  (** val to_pos :
      z
      ->
      positive **)
  
  let to_pos = function
  | Zpos p ->
    p
  | _ ->
    XH
  
  (** val iter :
      z
      ->
      ('a1
      ->
      'a1)
      ->
      'a1
      ->
      'a1 **)
  
  let iter n0 f x =
    match n0 with
    | Zpos p ->
      Coq_Pos.iter
        p
        f
        x
    | _ ->
      x
  
  (** val pos_div_eucl :
      positive
      ->
      z
      ->
      (z,
      z)
      prod **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q0,
                r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        add
          (mul
            (Zpos
            (XO
            XH))
            r)
          (Zpos
          XH)
      in
      (match ltb
               r'
               b with
       | True ->
         Pair
           ((mul
              (Zpos
              (XO
              XH))
              q0),
           r')
       | False ->
         Pair
           ((add
              (mul
                (Zpos
                (XO
                XH))
                q0)
              (Zpos
              XH)),
           (sub
             r'
             b)))
    | XO a' ->
      let Pair (q0,
                r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        mul
          (Zpos
          (XO
          XH))
          r
      in
      (match ltb
               r'
               b with
       | True ->
         Pair
           ((mul
              (Zpos
              (XO
              XH))
              q0),
           r')
       | False ->
         Pair
           ((add
              (mul
                (Zpos
                (XO
                XH))
                q0)
              (Zpos
              XH)),
           (sub
             r'
             b)))
    | XH ->
      (match leb
               (Zpos
               (XO
               XH))
               b with
       | True ->
         Pair
           (Z0,
           (Zpos
           XH))
       | False ->
         Pair
           ((Zpos
           XH),
           Z0))
  
  (** val div_eucl :
      z
      ->
      z
      ->
      (z,
      z)
      prod **)
  
  let div_eucl a b =
    match a with
    | Z0 ->
      Pair
        (Z0,
        Z0)
    | Zpos a' ->
      (match b with
       | Z0 ->
         Pair
           (Z0,
           Z0)
       | Zpos p ->
         pos_div_eucl
           a'
           b
       | Zneg b' ->
         let Pair (q0,
                   r) =
           pos_div_eucl
             a'
             (Zpos
             b')
         in
         (match r with
          | Z0 ->
            Pair
              ((opp
                 q0),
              Z0)
          | _ ->
            Pair
              ((opp
                 (add
                   q0
                   (Zpos
                   XH))),
              (add
                b
                r))))
    | Zneg a' ->
      (match b with
       | Z0 ->
         Pair
           (Z0,
           Z0)
       | Zpos p ->
         let Pair (q0,
                   r) =
           pos_div_eucl
             a'
             b
         in
         (match r with
          | Z0 ->
            Pair
              ((opp
                 q0),
              Z0)
          | _ ->
            Pair
              ((opp
                 (add
                   q0
                   (Zpos
                   XH))),
              (sub
                b
                r)))
       | Zneg b' ->
         let Pair (q0,
                   r) =
           pos_div_eucl
             a'
             (Zpos
             b')
         in
         Pair
         (q0,
         (opp
           r)))
  
  (** val div :
      z
      ->
      z
      ->
      z **)
  
  let div a b =
    let Pair (q0,
              x) =
      div_eucl
        a
        b
    in
    q0
  
  (** val modulo :
      z
      ->
      z
      ->
      z **)
  
  let modulo a b =
    let Pair (x,
              r) =
      div_eucl
        a
        b
    in
    r
  
  (** val quotrem :
      z
      ->
      z
      ->
      (z,
      z)
      prod **)
  
  let quotrem a b =
    match a with
    | Z0 ->
      Pair
        (Z0,
        Z0)
    | Zpos a0 ->
      (match b with
       | Z0 ->
         Pair
           (Z0,
           a)
       | Zpos b0 ->
         let Pair (q0,
                   r) =
           N.pos_div_eucl
             a0
             (Npos
             b0)
         in
         Pair
         ((of_N
            q0),
         (of_N
           r))
       | Zneg b0 ->
         let Pair (q0,
                   r) =
           N.pos_div_eucl
             a0
             (Npos
             b0)
         in
         Pair
         ((opp
            (of_N
              q0)),
         (of_N
           r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q0, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q0)), (opp (of_N r)))
       | Zneg b0 ->
         let Pair (q0, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q0), (opp (of_N r))))
  
  (** val quot : z -> z -> z **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : z -> z -> z **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : z -> bool **)
  
  let even = function
  | Z0 -> True
  | Zpos p ->
    (match p with
     | XO p0 -> True
     | _ -> False)
  | Zneg p ->
    (match p with
     | XO p0 -> True
     | _ -> False)
  
  (** val odd : z -> bool **)
  
  let odd = function
  | Z0 -> False
  | Zpos p ->
    (match p with
     | XO p0 -> False
     | _ -> True)
  | Zneg p ->
    (match p with
     | XO p0 -> False
     | _ -> True)
  
  (** val div2 : z -> z **)
  
  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)
  
  (** val quot2 : z -> z **)
  
  let quot2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p ->
    (match p with
     | XH -> Z0
     | _ -> Zneg (Coq_Pos.div2 p))
  
  (** val log2 : z -> z **)
  
  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0
  
  (** val sqrtrem : z -> (z, z) prod **)
  
  let sqrtrem = function
  | Zpos p ->
    let Pair (s, m) = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> Pair ((Zpos s), (Zpos r))
     | _ -> Pair ((Zpos s), Z0))
  | _ -> Pair (Z0, Z0)
  
  (** val sqrt : z -> z **)
  
  let sqrt = function
  | Zpos p -> Zpos (Coq_Pos.sqrt p)
  | _ -> Z0
  
  (** val gcd : z -> z -> z **)
  
  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
  
  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)
  
  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
  
  (** val testbit : z -> z -> bool **)
  
  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> False
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg p -> False
  
  (** val shiftl : z -> z -> z **)
  
  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter p (mul (Zpos (XO XH))) a
  | Zneg p -> Coq_Pos.iter p div2 a
  
  (** val shiftr : z -> z -> z **)
  
  let shiftr a n0 =
    shiftl a (opp n0)
  
  (** val coq_lor : z -> z -> z **)
  
  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val coq_land : z -> z -> z **)
  
  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val ldiff : z -> z -> z **)
  
  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
  
  (** val coq_lxor : z -> z -> z **)
  
  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
  
  (** val eq_dec : z -> z -> sumbool **)
  
  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Left
       | _ -> Right)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> Right)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> Right)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : z -> z -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : z -> z -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  (** val sqrt_up : z -> z **)
  
  let sqrt_up a =
    match compare Z0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Z0
  
  (** val log2_up : z -> z **)
  
  let log2_up a =
    match compare (Zpos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : z -> z -> z **)
      
      let div =
        quot
      
      (** val modulo : z -> z -> z **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : z -> z -> z **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : z -> z -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> z **)
  
  let b2z = function
  | True -> Zpos XH
  | False -> Z0
  
  (** val setbit : z -> z -> z **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Zpos XH) n0)
  
  (** val clearbit : z -> z -> z **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Zpos XH) n0)
  
  (** val lnot : z -> z **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : z -> z **)
  
  let ones n0 =
    pred (shiftl (Zpos XH) n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : z -> z -> sumbool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) Left Right
    
    (** val min_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : z -> z -> sumbool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) Left Right
   end
  
  (** val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : z -> z -> sumbool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : z -> z -> sumbool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos0 rmul x = function
| XI i0 -> let p = pow_pos0 rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos0 rmul x i0 in rmul p p
| XH -> x

type q = { qnum : z; qden : positive }

(** val qnum : q -> z **)

let qnum x = x.qnum

(** val qden : q -> positive **)

let qden x = x.qden

(** val inject_Z : z -> q **)

let inject_Z x =
  { qnum = x; qden = XH }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum (Zpos q0.qden)) (Z.mul q0.qnum (Zpos p.qden))

(** val qeq_dec : q -> q -> sumbool **)

let qeq_dec x y =
  Z.eq_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val qpower_positive : q -> positive -> q **)

let qpower_positive q0 p =
  pow_pos0 qmult q0 p

(** val qpower : q -> z -> q **)

let qpower q0 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q0 p
| Zneg p -> qinv (qpower_positive q0 p)

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Cons of 'a * 'a stream

(** val hd : 'a1 stream -> 'a1 **)

let hd x =
  let Cons (a, s) = Lazy.force x in a

(** val tl : 'a1 stream -> 'a1 stream **)

let tl x =
  let Cons (a, s) = Lazy.force x in s

(** val map : ('a1 -> 'a2) -> 'a1 stream -> 'a2 stream **)

let rec map f s =
  lazy (Cons ((f (hd s)), (map f (tl s))))

(** val zipWith :
    ('a1 -> 'a2 -> 'a3) -> 'a1 stream -> 'a2 stream -> 'a3 stream **)

let rec zipWith f a b =
  lazy (Cons ((f (hd a) (hd b)), (zipWith f (tl a) (tl b))))

type ('a, 'b) cast = 'a -> 'b

type 'a plus0 = 'a -> 'a -> 'a

(** val plus1 : 'a1 plus0 -> 'a1 -> 'a1 -> 'a1 **)

let plus1 plus2 =
  plus2

type 'a mult = 'a -> 'a -> 'a

(** val mult0 : 'a1 mult -> 'a1 -> 'a1 -> 'a1 **)

let mult0 mult1 =
  mult1

type 'a one0 = 'a

(** val one1 : 'a1 one0 -> 'a1 **)

let one1 one2 =
  one2

type 'a zero0 = 'a

(** val zero1 : 'a1 zero0 -> 'a1 **)

let zero1 zero2 =
  zero2

type rSetoid =
| Build_RSetoid

type st_car = __

module Default = 
 struct 
  (** val min : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1 **)
  
  let min le_total x y =
    match le_total x y with
    | Left -> x
    | Right -> y
  
  (** val min_case :
      ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) ->
      'a2 **)
  
  let min_case le_total x y hx hy =
    match le_total x y with
    | Left -> hx __
    | Right -> hy __
  
  (** val max : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> 'a1 **)
  
  let max le_total x y =
    match le_total y x with
    | Left -> x
    | Right -> y
  
  (** val max_case :
      ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) ->
      'a2 **)
  
  let max_case le_total x y x0 x1 =
    let flip_le_total = fun x2 y0 -> le_total y0 x2 in
    min_case flip_le_total x y x0 x1
 end

(** val qlt_le_dec_fast : q -> q -> sumbool **)

let qlt_le_dec_fast x y =
  let c = qcompare x y in
  (match c with
   | Lt -> Left
   | _ -> Right)

(** val qle_total : q -> q -> sumbool **)

let qle_total x y =
  qlt_le_dec_fast x y

(** val qmin : q -> q -> q **)

let qmin =
  Default.min qle_total

(** val qmax : q -> q -> q **)

let qmax =
  Default.max qle_total

type ('a, 'r) csymmetric = 'a -> 'a -> 'r -> 'r

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let Pair (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

(** val qminus' : q -> q -> q **)

let qminus' x y =
  qred (qminus x y)

(** val qfloor : q -> z **)

let qfloor x =
  let { qnum = n0; qden = d } = x in Z.div n0 (Zpos d)

(** val qceiling : q -> z **)

let qceiling x =
  Z.opp (qfloor (qopp x))

(** val ap_Q_cotransitive0 : q -> q -> q -> (__, __) sum **)

let ap_Q_cotransitive0 x y z0 =
  match qeq_dec x z0 with
  | Left -> Inr __
  | Right -> Inl __

type ('a, 'r) cotransitive = 'a -> 'a -> 'r -> 'a -> ('r, 'r) sum

type ('a, 'ap) is_CSetoid = { ax_ap_symmetric : ('a, 'ap) csymmetric;
                              ax_ap_cotransitive : ('a, 'ap) cotransitive }

type cSetoid = { cs_crr : rSetoid; cs_proof : (st_car, __) is_CSetoid }

(** val cs_crr : cSetoid -> rSetoid **)

let cs_crr x = x.cs_crr

(** val build_CSetoid : ('a1, 'a2) is_CSetoid -> cSetoid **)

let build_CSetoid p =
  { cs_crr = Build_RSetoid; cs_proof = (Obj.magic p) }

(** val ap_Q_cotransitive1 : q -> q -> q -> (__, __) sum **)

let ap_Q_cotransitive1 x y z0 =
  ap_Q_cotransitive0 x y z0

(** val ap_Q_is_apartness : (q, __) is_CSetoid **)

let ap_Q_is_apartness =
  { ax_ap_symmetric = (Obj.magic __); ax_ap_cotransitive = (fun x x0 _ ->
    ap_Q_cotransitive1 x x0) }

(** val q_as_CSetoid : cSetoid **)

let q_as_CSetoid =
  build_CSetoid ap_Q_is_apartness

(** val q_is_Setoid : rSetoid **)

let q_is_Setoid =
  q_as_CSetoid.cs_crr

type qpos = q

(** val qposMake : positive -> positive -> qpos **)

let qposMake num den =
  { qnum = (Zpos num); qden = den }

(** val qposAsQ : qpos -> q **)

let qposAsQ e =
  e

(** val mkQpos : q -> qpos **)

let mkQpos a =
  a

(** val qpos_mult : qpos -> qpos -> qpos **)

let qpos_mult x y =
  qmult (qposAsQ x) (qposAsQ y)

(** val qpos_inv : qpos -> qpos **)

let qpos_inv x =
  qinv (qposAsQ x)

(** val qpos_power : qpos -> z -> qpos **)

let qpos_power x z0 =
  mkQpos (qpower (qposAsQ x) z0)

type qposInf =
| Qpos2QposInf of qpos
| QposInfinity

(** val qposInf_bind : (qpos -> qposInf) -> qposInf -> qposInf **)

let qposInf_bind f = function
| Qpos2QposInf x' -> f x'
| QposInfinity -> QposInfinity

(** val qposInf_mult : qposInf -> qposInf -> qposInf **)

let qposInf_mult x y =
  qposInf_bind (fun x' ->
    qposInf_bind (fun y' -> Qpos2QposInf (qpos_mult x' y')) y) x

type metricSpace =
  rSetoid
  (* singleton inductive, whose constructor was Build_MetricSpace *)

(** val ball_ex_dec :
    metricSpace -> (qpos -> st_car -> st_car -> sumbool) -> qposInf -> st_car
    -> st_car -> sumbool **)

let ball_ex_dec x ball_dec e a b =
  match e with
  | Qpos2QposInf e0 -> ball_dec e0 a b
  | QposInfinity -> Left

type uniformlyContinuousFunction = { ucFun : (st_car -> st_car);
                                     mu : (qpos -> qposInf) }

(** val ucFun :
    metricSpace -> metricSpace -> uniformlyContinuousFunction -> st_car ->
    st_car **)

let ucFun _ _ x = x.ucFun

(** val mu :
    metricSpace -> metricSpace -> uniformlyContinuousFunction -> qpos ->
    qposInf **)

let mu _ _ x = x.mu

(** val uc_compose :
    metricSpace -> metricSpace -> metricSpace -> st_car -> st_car -> st_car **)

let uc_compose x y z0 g f =
  Obj.magic { ucFun = (fun x0 ->
    (Obj.magic g).ucFun ((Obj.magic f).ucFun x0)); mu = (fun e ->
    qposInf_bind (Obj.magic f).mu ((Obj.magic g).mu e)) }

type decidableMetric = qpos -> st_car -> st_car -> sumbool

type regularFunction =
  qposInf -> st_car
  (* singleton inductive, whose constructor was Build_RegularFunction *)

(** val approximate : metricSpace -> regularFunction -> qposInf -> st_car **)

let approximate x r =
  r

(** val regFun_Setoid : metricSpace -> rSetoid **)

let regFun_Setoid x =
  Build_RSetoid

(** val complete : metricSpace -> metricSpace **)

let complete x =
  regFun_Setoid x

(** val cunit_fun : metricSpace -> st_car -> st_car **)

let cunit_fun x x0 =
  Obj.magic (fun x1 -> x0)

(** val cunit : metricSpace -> st_car **)

let cunit x =
  Obj.magic { ucFun = (cunit_fun x); mu = (fun x0 -> Qpos2QposInf x0) }

(** val cjoin_raw : metricSpace -> st_car -> qposInf -> st_car **)

let cjoin_raw x x0 e =
  approximate x
    (Obj.magic
      (approximate (complete x) (Obj.magic x0)
        (qposInf_mult (Qpos2QposInf (qposMake XH (XO XH))) e)))
    (qposInf_mult (Qpos2QposInf (qposMake XH (XO XH))) e)

(** val cjoin_fun : metricSpace -> st_car -> st_car **)

let cjoin_fun x x0 =
  Obj.magic (cjoin_raw x x0)

(** val cjoin : metricSpace -> st_car **)

let cjoin x =
  Obj.magic { ucFun = (cjoin_fun x); mu = (fun x0 -> Qpos2QposInf x0) }

(** val cmap_fun :
    metricSpace -> metricSpace -> st_car -> st_car -> st_car **)

let cmap_fun x y f x0 =
  Obj.magic (fun e ->
    (Obj.magic f).ucFun
      (approximate x (Obj.magic x0) (qposInf_bind (Obj.magic f).mu e)))

(** val cmap : metricSpace -> metricSpace -> st_car -> st_car **)

let cmap x y f =
  Obj.magic { ucFun = (cmap_fun x y f); mu = (Obj.magic f).mu }

(** val cbind : metricSpace -> metricSpace -> st_car -> st_car **)

let cbind x y f =
  uc_compose (complete x) (complete (complete y)) (complete y) (cjoin y)
    (cmap x (complete y) f)

(** val q_as_MetricSpace : metricSpace **)

let q_as_MetricSpace =
  q_is_Setoid

(** val qmetric_dec : decidableMetric **)

let qmetric_dec e a b =
  let c = qopp (qposAsQ e) in
  let d = qminus (Obj.magic a) (Obj.magic b) in
  let s = qlt_le_dec_fast d c in
  (match s with
   | Left -> Right
   | Right ->
     let s0 = qlt_le_dec_fast (qposAsQ e) d in
     (match s0 with
      | Left -> Right
      | Right -> Left))

(** val qball_ex_bool : qposInf -> st_car -> st_car -> bool **)

let qball_ex_bool e a b =
  match ball_ex_dec q_as_MetricSpace qmetric_dec e a b with
  | Left -> True
  | Right -> False

(** val q_0 : q zero0 **)

let q_0 =
  { qnum = Z0; qden = XH }

(** val q_1 : q one0 **)

let q_1 =
  { qnum = (Zpos XH); qden = XH }

(** val q_plus : q plus0 **)

let q_plus =
  qplus

(** val q_mult : q mult **)

let q_mult =
  qmult

(** val inject_Q_CR : (q, st_car) cast **)

let inject_Q_CR =
  Obj.magic (Obj.magic (cunit q_as_MetricSpace)).ucFun

(** val qboundBelow_uc : st_car -> st_car **)

let qboundBelow_uc a =
  Obj.magic { ucFun = (fun b ->
    Obj.magic (qmax (Obj.magic a) (Obj.magic b))); mu = (fun x ->
    Qpos2QposInf x) }

(** val qboundAbove_uc : st_car -> st_car **)

let qboundAbove_uc a =
  Obj.magic { ucFun = (fun b ->
    Obj.magic (qmin (Obj.magic a) (Obj.magic b))); mu = (fun x ->
    Qpos2QposInf x) }

(** val qscale_modulus : q -> qpos -> qposInf **)

let qscale_modulus a e =
  let { qnum = qnum0; qden = ad } = a in
  (match qnum0 with
   | Z0 -> QposInfinity
   | Zpos an -> Qpos2QposInf (qpos_mult (qposMake ad an) e)
   | Zneg an -> Qpos2QposInf (qpos_mult (qposMake ad an) e))

(** val qboundAbs : qpos -> st_car **)

let qboundAbs c =
  uc_compose q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace
    (qboundBelow_uc (Obj.magic (qopp (qposAsQ c))))
    (qboundAbove_uc (Obj.magic (qposAsQ c)))

(** val qinv_modulus : qpos -> qpos -> qpos **)

let qinv_modulus c e =
  qpos_mult (qpos_mult c c) e

(** val qinv_pos_uc : qpos -> st_car **)

let qinv_pos_uc c =
  Obj.magic { ucFun = (fun a ->
    Obj.magic (qinv (qmax (qposAsQ c) (Obj.magic a)))); mu = (fun e ->
    Qpos2QposInf (qinv_modulus c e)) }

(** val cRinv_pos : qpos -> st_car **)

let cRinv_pos c =
  cmap q_as_MetricSpace q_as_MetricSpace (qinv_pos_uc c)

(** val iterate : ('a1 -> 'a1) -> 'a1 -> 'a1 stream **)

let rec iterate f x =
  lazy (Cons (x, (iterate f (f x))))

(** val takeUntil :
    ('a1 stream -> bool) -> 'a1 stream -> ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a2 **)

let rec takeUntil p s cons nil =
  match p s with
  | True -> nil
  | False -> cons (hd s) (takeUntil p (tl s) cons nil)

(** val mult_Streams : 'a1 mult -> 'a1 stream -> 'a1 stream -> 'a1 stream **)

let mult_Streams h1 =
  zipWith (mult0 h1)

(** val powers_help : 'a1 mult -> 'a1 -> 'a1 -> 'a1 stream **)

let powers_help h1 a =
  iterate (fun y -> mult0 h1 y a)

(** val powers : 'a1 mult -> 'a1 one0 -> 'a1 -> 'a1 stream **)

let powers h1 h3 a =
  powers_help h1 a (one1 h3)

(** val partialAlternatingSumUntil : (q stream -> bool) -> q stream -> q **)

let partialAlternatingSumUntil p s =
  takeUntil p s qminus' (zero1 q_0)

(** val infiniteAlternatingSum_raw : q stream -> qposInf -> q **)

let infiniteAlternatingSum_raw s __U03b5_ =
  partialAlternatingSumUntil (fun s0 ->
    qball_ex_bool __U03b5_ (hd (Obj.magic s0))
      (Obj.magic { qnum = Z0; qden = XH })) s

(** val infiniteAlternatingSum : q stream -> st_car **)

let infiniteAlternatingSum seq =
  Obj.magic (Obj.magic (infiniteAlternatingSum_raw seq))

(** val pfactorials_help : positive -> positive -> positive stream **)

let rec pfactorials_help n0 c =
  lazy (Cons (c, (pfactorials_help (Coq_Pos.succ n0) (Coq_Pos.mul n0 c))))

(** val pfactorials : positive stream **)

let pfactorials =
  pfactorials_help XH XH

(** val qrecip_factorials : q stream **)

let qrecip_factorials =
  map (fun x -> { qnum = (Zpos XH); qden = x }) pfactorials

(** val qpower_N_modulus : n -> qpos -> qpos -> qposInf **)

let qpower_N_modulus n0 c e =
  match n0 with
  | N0 -> QposInfinity
  | Npos p ->
    Qpos2QposInf
      (qpos_mult e
        (qpos_inv
          (qpos_mult (qposMake p XH) (qpos_power c (Z.pred (Zpos p))))))

(** val qpower_N_uc : n -> qpos -> st_car **)

let qpower_N_uc n0 c =
  Obj.magic { ucFun = (fun x ->
    Obj.magic
      (qpower (Obj.magic ((Obj.magic (qboundAbs c)).ucFun x)) (Z.of_N n0)));
    mu = (qpower_N_modulus n0 c) }

(** val cRpower_N_bounded : n -> qpos -> st_car **)

let cRpower_N_bounded n0 c =
  cmap q_as_MetricSpace q_as_MetricSpace (qpower_N_uc n0 c)

(** val approximateQ : q -> positive -> q **)

let approximateQ x p =
  let { qnum = n0; qden = d } = x in
  { qnum = (Z.div (Z.mul n0 (Zpos p)) (Zpos d)); qden = p }

(** val compress_raw : st_car -> qposInf -> q **)

let compress_raw x e = match e with
| Qpos2QposInf e0 ->
  let { qnum = n0; qden = d } = qposAsQ e0 in
  (match Z.succ (Z.div (Z.mul (Zpos (XO XH)) (Zpos d)) n0) with
   | Zpos p ->
     approximateQ
       (Obj.magic
         (approximate q_as_MetricSpace (Obj.magic x) (Qpos2QposInf
           (qposMake XH p)))) p
   | _ ->
     Obj.magic (approximate q_as_MetricSpace (Obj.magic x) (Qpos2QposInf e0)))
| QposInfinity -> Obj.magic (approximate q_as_MetricSpace (Obj.magic x) e)

(** val compress_fun : st_car -> st_car **)

let compress_fun x =
  Obj.magic (Obj.magic (compress_raw x))

(** val compress : st_car **)

let compress =
  Obj.magic { ucFun = compress_fun; mu = (fun x -> Qpos2QposInf x) }

(** val expSequence : q -> q stream **)

let expSequence a =
  mult_Streams q_mult qrecip_factorials (powers q_mult q_1 a)

(** val rational_exp_small_neg : q -> st_car **)

let rational_exp_small_neg a =
  infiniteAlternatingSum (expSequence (qopp a))

(** val rational_exp_neg_bounded : nat -> q -> st_car **)

let rec rational_exp_neg_bounded n0 a =
  match n0 with
  | O -> rational_exp_small_neg a
  | S n' ->
    (match qlt_le_dec_fast a (qopp { qnum = (Zpos XH); qden = XH }) with
     | Left ->
       (Obj.magic (cRpower_N_bounded (Npos (XO XH)) (qposMake XH XH))).ucFun
         ((Obj.magic compress).ucFun
           (rational_exp_neg_bounded n'
             (qdiv a (plus1 q_plus (one1 q_1) (one1 q_1)))))
     | Right -> rational_exp_small_neg a)

(** val rational_exp_neg : q -> st_car **)

let rational_exp_neg a =
  rational_exp_neg_bounded
    (match a.qnum with
     | Z0 -> O
     | Zpos x -> Coq_Pos.size_nat x
     | Zneg x -> Coq_Pos.size_nat x) a

(** val rational_exp : q -> st_car **)

let rational_exp a =
  let s = qle_total { qnum = Z0; qden = XH } a in
  (match s with
   | Left ->
     (Obj.magic (cRinv_pos (qpos_power (qposMake XH (XI XH)) (qceiling a)))).ucFun
       (rational_exp_neg (qopp a))
   | Right -> rational_exp_neg a)

(** val exp_bound : z -> qpos **)

let exp_bound = function
| Z0 -> qposMake XH XH
| Zpos p -> qpos_power (qposMake (XI XH) XH) (Zpos p)
| Zneg p -> qpos_power (qposMake XH (XO XH)) (Zpos p)

(** val exp_bound_uc : z -> st_car **)

let exp_bound_uc z0 =
  Obj.magic { ucFun = (fun a ->
    rational_exp (qmin (inject_Z z0) (Obj.magic a))); mu =
    (qscale_modulus (qposAsQ (exp_bound z0))) }

(** val exp_bounded : z -> st_car **)

let exp_bounded z0 =
  cbind q_as_MetricSpace q_as_MetricSpace (exp_bound_uc z0)

(** val exp : st_car -> st_car **)

let exp x =
  (Obj.magic
    (exp_bounded
      (qceiling
        (qplus
          (Obj.magic
            (approximate q_as_MetricSpace (Obj.magic x) (Qpos2QposInf
              (qposMake XH XH)))) { qnum = (Zpos XH); qden = XH })))).ucFun x

(** val answer : positive -> st_car -> z **)

let answer n0 r =
  let m = Coq_Pos.iter n0 (Coq_Pos.mul (XO (XI (XO XH)))) XH in
  let { qnum = a; qden = b } =
    qmult
      (Obj.magic
        (approximate q_as_MetricSpace (Obj.magic r) (Qpos2QposInf
          (qposMake XH m)))) (inject_Z (Zpos m))
  in
  Z.div a (Zpos b)

(** val test : z **)

let test =
  answer (XI XH) (exp (inject_Q_CR { qnum = (Zpos XH); qden = XH }))


(* scons: done building targets. *)
