type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

type comparison =
| Eq
| Lt
| Gt

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

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n f x =
  match n with
  | O -> x
  | S n' -> f (nat_iter n' f x)

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module Pos = 
 struct 
  type t = Big.big_int
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let rec succ x =
    Big.positive_case
      (fun p -> Big.double
      (succ p))
      (fun p -> Big.doubleplusone
      p)
      (fun _ -> Big.double
      Big.one)
      x
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec add x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.double
        (add_carry p q0))
        (fun q0 -> Big.doubleplusone
        (add p q0))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (add p q0))
        (fun q0 -> Big.double
        (add p q0))
        (fun _ -> Big.doubleplusone
        p)
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.double
        (succ q0))
        (fun q0 -> Big.doubleplusone
        q0)
        (fun _ -> Big.double
        Big.one)
        y)
      x
  
  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)
  
  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (add_carry p q0))
        (fun q0 -> Big.double
        (add_carry p q0))
        (fun _ -> Big.doubleplusone
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.double
        (add_carry p q0))
        (fun q0 -> Big.doubleplusone
        (add p q0))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (succ q0))
        (fun q0 -> Big.double
        (succ q0))
        (fun _ -> Big.doubleplusone
        Big.one)
        y)
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double
      p))
      (fun p -> Big.doubleplusone
      (pred_double p))
      (fun _ ->
      Big.one)
      x
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred x =
    Big.positive_case
      (fun p -> Big.double
      p)
      (fun p ->
      pred_double p)
      (fun _ ->
      Big.one)
      x
  
  (** val pred_N : Big.big_int -> Big.big_int **)
  
  let pred_N x =
    Big.positive_case
      (fun p -> (Big.double
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      Big.zero)
      x
  
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0
  
  (** val double_pred_mask : Big.big_int -> mask **)
  
  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double
      p)))
      (fun p -> IsPos (Big.double
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q0 ->
    (Big.positive_case
       (fun p0 -> IsPos
       (pred q0))
       (fun p0 -> IsPos
       (pred q0))
       (fun _ ->
       IsNul)
       q0)
  | _ -> IsNeg
  
  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)
  
  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 ->
        double_mask (sub_mask p q0))
        (fun q0 ->
        succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 ->
        succ_double_mask (sub_mask_carry p q0))
        (fun q0 ->
        double_mask (sub_mask p q0))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)
  
  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 ->
        succ_double_mask (sub_mask_carry p q0))
        (fun q0 ->
        double_mask (sub_mask p q0))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 ->
        double_mask (sub_mask_carry p q0))
        (fun q0 ->
        succ_double_mask (sub_mask_carry p q0))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> Big.one
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec mul x y =
    Big.positive_case
      (fun p ->
      add y (Big.double (mul p y)))
      (fun p -> Big.double
      (mul p y))
      (fun _ ->
      y)
      x
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    Big.positive_case
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    iter y (mul x) Big.one
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let rec square p =
    Big.positive_case
      (fun p0 -> Big.doubleplusone (Big.double
      (add (square p0) p0)))
      (fun p0 -> Big.double (Big.double
      (square p0)))
      (fun _ ->
      Big.one)
      p
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 p =
    Big.positive_case
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val div2_up : Big.big_int -> Big.big_int **)
  
  let div2_up p =
    Big.positive_case
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val size_nat : Big.big_int -> nat **)
  
  let rec size_nat p =
    Big.positive_case
      (fun p0 -> S
      (size_nat p0))
      (fun p0 -> S
      (size_nat p0))
      (fun _ -> S
      O)
      p
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let rec size p =
    Big.positive_case
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      Big.one)
      p
  
  (** val compare_cont :
      Big.big_int -> Big.big_int -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 ->
        compare_cont p q0 r)
        (fun q0 ->
        compare_cont p q0 Gt)
        (fun _ ->
        Gt)
        y)
      (fun p ->
      Big.positive_case
        (fun q0 ->
        compare_cont p q0 Lt)
        (fun q0 ->
        compare_cont p q0 r)
        (fun _ ->
        Gt)
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 ->
        Lt)
        (fun q0 ->
        Lt)
        (fun _ ->
        r)
        y)
      x
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        eqb p0 q1)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun q1 ->
        eqb p0 q1)
        (fun _ ->
        false)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q0)
      p
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
      (Big.big_int * mask) -> Big.big_int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Big.doubleplusone (Big.double s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Big.doubleplusone s), (sub_mask r' s'))
       else ((Big.double s), (IsPos r'))
     | _ ->
       ((Big.double s),
         (sub_mask (g (f Big.one)) (Big.double (Big.double Big.one)))))
  
  (** val sqrtrem : Big.big_int -> Big.big_int * mask **)
  
  let rec sqrtrem p =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x ->
          Big.doubleplusone x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.doubleplusone x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos (Big.double
        Big.one))))
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos
        Big.one)))
        p0)
      (fun _ -> (Big.one,
      IsNul))
      p
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec gcdn n a b =
    match n with
    | O -> Big.one
    | S n0 ->
      (Big.positive_case
         (fun a' ->
         Big.positive_case
           (fun b' ->
           match compare a' b' with
           | Eq -> a
           | Lt -> gcdn n0 (sub b' a') a
           | Gt -> gcdn n0 (sub a' b') b)
           (fun b0 ->
           gcdn n0 a b0)
           (fun _ ->
           Big.one)
           b)
         (fun a0 ->
         Big.positive_case
           (fun p ->
           gcdn n0 a0 b)
           (fun b0 -> Big.double
           (gcdn n0 a0 b0))
           (fun _ ->
           Big.one)
           b)
         (fun _ ->
         Big.one)
         a)
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> Big.big_int -> Big.big_int ->
      Big.big_int * (Big.big_int * Big.big_int) **)
  
  let rec ggcdn n a b =
    match n with
    | O -> (Big.one, (a, b))
    | S n0 ->
      (Big.positive_case
         (fun a' ->
         Big.positive_case
           (fun b' ->
           match compare a' b' with
           | Eq -> (a, (Big.one, Big.one))
           | Lt ->
             let (g, p) = ggcdn n0 (sub b' a') a in
             let (ba, aa) = p in (g, (aa, (add aa (Big.double ba))))
           | Gt ->
             let (g, p) = ggcdn n0 (sub a' b') b in
             let (ab, bb) = p in (g, ((add bb (Big.double ab)), bb)))
           (fun b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, (Big.double bb))))
           (fun _ -> (Big.one, (a,
           Big.one)))
           b)
         (fun a0 ->
         Big.positive_case
           (fun p ->
           let (g, p0) = ggcdn n0 a0 b in
           let (aa, bb) = p0 in (g, ((Big.double aa), bb)))
           (fun b0 ->
           let (g, p) = ggcdn n0 a0 b0 in ((Big.double g), p))
           (fun _ -> (Big.one, (a,
           Big.one)))
           b)
         (fun _ -> (Big.one, (Big.one,
         b)))
         a)
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : Big.big_int -> Big.big_int **)
  
  let coq_Nsucc_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val coq_Ndouble : Big.big_int -> Big.big_int **)
  
  let coq_Ndouble n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lor p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 -> Big.doubleplusone
        (coq_lor p0 q1))
        (fun q1 -> Big.doubleplusone
        (coq_lor p0 q1))
        (fun _ ->
        p)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 -> Big.doubleplusone
        (coq_lor p0 q1))
        (fun q1 -> Big.double
        (coq_lor p0 q1))
        (fun _ -> Big.doubleplusone
        p0)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        q0)
        (fun q1 -> Big.doubleplusone
        q1)
        (fun _ ->
        q0)
        q0)
      p
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_land p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Nsucc_double (coq_land p0 q1))
        (fun q1 ->
        coq_Ndouble (coq_land p0 q1))
        (fun _ ->
        Big.one)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble (coq_land p0 q1))
        (fun q1 ->
        coq_Ndouble (coq_land p0 q1))
        (fun _ ->
        Big.zero)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.one)
        (fun q1 ->
        Big.zero)
        (fun _ ->
        Big.one)
        q0)
      p
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble (ldiff p0 q1))
        (fun q1 ->
        coq_Nsucc_double (ldiff p0 q1))
        (fun _ -> (Big.double
        p0))
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble (ldiff p0 q1))
        (fun q1 ->
        coq_Ndouble (ldiff p0 q1))
        (fun _ ->
        p)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.zero)
        (fun q1 ->
        Big.one)
        (fun _ ->
        Big.zero)
        q0)
      p
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lxor p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble (coq_lxor p0 q1))
        (fun q1 ->
        coq_Nsucc_double (coq_lxor p0 q1))
        (fun _ -> (Big.double
        p0))
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Nsucc_double (coq_lxor p0 q1))
        (fun q1 ->
        coq_Ndouble (coq_lxor p0 q1))
        (fun _ -> (Big.doubleplusone
        p0))
        q0)
      (fun _ ->
      Big.positive_case
        (fun q1 -> (Big.double
        q1))
        (fun q1 -> (Big.doubleplusone
        q1))
        (fun _ ->
        Big.zero)
        q0)
      p
  
  (** val shiftl_nat : Big.big_int -> nat -> Big.big_int **)
  
  let shiftl_nat p n =
    nat_iter n (fun x -> Big.double x) p
  
  (** val shiftr_nat : Big.big_int -> nat -> Big.big_int **)
  
  let shiftr_nat p n =
    nat_iter n div2 p
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 (fun x -> Big.double x) p)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 div2 p)
      n
  
  (** val testbit_nat : Big.big_int -> nat -> bool **)
  
  let rec testbit_nat p n =
    Big.positive_case
      (fun p0 ->
      match n with
      | O -> true
      | S n' -> testbit_nat p0 n')
      (fun p0 ->
      match n with
      | O -> false
      | S n' -> testbit_nat p0 n')
      (fun _ ->
      match n with
      | O -> true
      | S n0 -> false)
      p
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit p n =
    Big.positive_case
      (fun p0 ->
      Big.n_case
        (fun _ ->
        true)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        false)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    Big.positive_case
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p
  
  (** val to_nat : Big.big_int -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> Big.big_int **)
  
  let rec of_nat = function
  | O -> Big.one
  | S x ->
    (match x with
     | O -> Big.one
     | S n0 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> Big.big_int **)
  
  let rec of_succ_nat = function
  | O -> Big.one
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos = 
 struct 
  type t = Big.big_int
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let rec succ = Big.succ
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec add = Big.add
  
  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)
  
  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (add_carry p q0))
        (fun q0 -> Big.double
        (add_carry p q0))
        (fun _ -> Big.doubleplusone
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 -> Big.double
        (add_carry p q0))
        (fun q0 -> Big.doubleplusone
        (add p q0))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (succ q0))
        (fun q0 -> Big.double
        (succ q0))
        (fun _ -> Big.doubleplusone
        Big.one)
        y)
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double
      p))
      (fun p -> Big.doubleplusone
      (pred_double p))
      (fun _ ->
      Big.one)
      x
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred = fun n -> Big.max Big.one (Big.pred n)
  
  (** val pred_N : Big.big_int -> Big.big_int **)
  
  let pred_N x =
    Big.positive_case
      (fun p -> (Big.double
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      Big.zero)
      x
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0
  
  (** val double_pred_mask : Big.big_int -> mask **)
  
  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double
      p)))
      (fun p -> IsPos (Big.double
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q0 ->
    (Big.positive_case
       (fun p0 -> IsPos
       (pred q0))
       (fun p0 -> IsPos
       (pred q0))
       (fun _ ->
       IsNul)
       q0)
  | _ -> IsNeg
  
  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)
  
  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 ->
        double_mask (sub_mask p q0))
        (fun q0 ->
        succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 ->
        succ_double_mask (sub_mask_carry p q0))
        (fun q0 ->
        double_mask (sub_mask p q0))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)
  
  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 ->
        succ_double_mask (sub_mask_carry p q0))
        (fun q0 ->
        double_mask (sub_mask p q0))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 ->
        double_mask (sub_mask_carry p q0))
        (fun q0 ->
        succ_double_mask (sub_mask_carry p q0))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub = fun n m -> Big.max Big.one (Big.sub n m)
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec mul = Big.mult
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    Big.positive_case
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    iter y (mul x) Big.one
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let rec square p =
    Big.positive_case
      (fun p0 -> Big.doubleplusone (Big.double
      (add (square p0) p0)))
      (fun p0 -> Big.double (Big.double
      (square p0)))
      (fun _ ->
      Big.one)
      p
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 p =
    Big.positive_case
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val div2_up : Big.big_int -> Big.big_int **)
  
  let div2_up p =
    Big.positive_case
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val size_nat : Big.big_int -> nat **)
  
  let rec size_nat p =
    Big.positive_case
      (fun p0 -> S
      (size_nat p0))
      (fun p0 -> S
      (size_nat p0))
      (fun _ -> S
      O)
      p
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let rec size p =
    Big.positive_case
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      Big.one)
      p
  
  (** val compare_cont :
      Big.big_int -> Big.big_int -> comparison -> comparison **)
  
  let rec compare_cont = fun x y c -> Big.compare_case c Lt Gt x y
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare = fun x y -> Big.compare_case Eq Lt Gt x y
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min = Big.min
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max = Big.max
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        eqb p0 q1)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun q1 ->
        eqb p0 q1)
        (fun _ ->
        false)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q0)
      p
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
      (Big.big_int * mask) -> Big.big_int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Big.doubleplusone (Big.double s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Big.doubleplusone s), (sub_mask r' s'))
       else ((Big.double s), (IsPos r'))
     | _ ->
       ((Big.double s),
         (sub_mask (g (f Big.one)) (Big.double (Big.double Big.one)))))
  
  (** val sqrtrem : Big.big_int -> Big.big_int * mask **)
  
  let rec sqrtrem p =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x ->
          Big.doubleplusone x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.doubleplusone x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos (Big.double
        Big.one))))
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos
        Big.one)))
        p0)
      (fun _ -> (Big.one,
      IsNul))
      p
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec gcdn n a b =
    match n with
    | O -> Big.one
    | S n0 ->
      (Big.positive_case
         (fun a' ->
         Big.positive_case
           (fun b' ->
           match compare a' b' with
           | Eq -> a
           | Lt -> gcdn n0 (sub b' a') a
           | Gt -> gcdn n0 (sub a' b') b)
           (fun b0 ->
           gcdn n0 a b0)
           (fun _ ->
           Big.one)
           b)
         (fun a0 ->
         Big.positive_case
           (fun p ->
           gcdn n0 a0 b)
           (fun b0 -> Big.double
           (gcdn n0 a0 b0))
           (fun _ ->
           Big.one)
           b)
         (fun _ ->
         Big.one)
         a)
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> Big.big_int -> Big.big_int ->
      Big.big_int * (Big.big_int * Big.big_int) **)
  
  let rec ggcdn n a b =
    match n with
    | O -> (Big.one, (a, b))
    | S n0 ->
      (Big.positive_case
         (fun a' ->
         Big.positive_case
           (fun b' ->
           match compare a' b' with
           | Eq -> (a, (Big.one, Big.one))
           | Lt ->
             let (g, p) = ggcdn n0 (sub b' a') a in
             let (ba, aa) = p in (g, (aa, (add aa (Big.double ba))))
           | Gt ->
             let (g, p) = ggcdn n0 (sub a' b') b in
             let (ab, bb) = p in (g, ((add bb (Big.double ab)), bb)))
           (fun b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, (Big.double bb))))
           (fun _ -> (Big.one, (a,
           Big.one)))
           b)
         (fun a0 ->
         Big.positive_case
           (fun p ->
           let (g, p0) = ggcdn n0 a0 b in
           let (aa, bb) = p0 in (g, ((Big.double aa), bb)))
           (fun b0 ->
           let (g, p) = ggcdn n0 a0 b0 in ((Big.double g), p))
           (fun _ -> (Big.one, (a,
           Big.one)))
           b)
         (fun _ -> (Big.one, (Big.one,
         b)))
         a)
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : Big.big_int -> Big.big_int **)
  
  let coq_Nsucc_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val coq_Ndouble : Big.big_int -> Big.big_int **)
  
  let coq_Ndouble n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lor p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 -> Big.doubleplusone
        (coq_lor p0 q1))
        (fun q1 -> Big.doubleplusone
        (coq_lor p0 q1))
        (fun _ ->
        p)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 -> Big.doubleplusone
        (coq_lor p0 q1))
        (fun q1 -> Big.double
        (coq_lor p0 q1))
        (fun _ -> Big.doubleplusone
        p0)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        q0)
        (fun q1 -> Big.doubleplusone
        q1)
        (fun _ ->
        q0)
        q0)
      p
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_land p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Nsucc_double (coq_land p0 q1))
        (fun q1 ->
        coq_Ndouble (coq_land p0 q1))
        (fun _ ->
        Big.one)
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble (coq_land p0 q1))
        (fun q1 ->
        coq_Ndouble (coq_land p0 q1))
        (fun _ ->
        Big.zero)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.one)
        (fun q1 ->
        Big.zero)
        (fun _ ->
        Big.one)
        q0)
      p
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble
          (ldiff
            p0
            q1))
        (fun q1 ->
        coq_Nsucc_double
          (ldiff
            p0
            q1))
        (fun _ ->
        (Big.double
        p0))
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble
          (ldiff
            p0
            q1))
        (fun q1 ->
        coq_Ndouble
          (ldiff
            p0
            q1))
        (fun _ ->
        p)
        q0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.zero)
        (fun q1 ->
        Big.one)
        (fun _ ->
        Big.zero)
        q0)
      p
  
  (** val coq_lxor :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let rec coq_lxor p q0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Ndouble
          (coq_lxor
            p0
            q1))
        (fun q1 ->
        coq_Nsucc_double
          (coq_lxor
            p0
            q1))
        (fun _ ->
        (Big.double
        p0))
        q0)
      (fun p0 ->
      Big.positive_case
        (fun q1 ->
        coq_Nsucc_double
          (coq_lxor
            p0
            q1))
        (fun q1 ->
        coq_Ndouble
          (coq_lxor
            p0
            q1))
        (fun _ ->
        (Big.doubleplusone
        p0))
        q0)
      (fun _ ->
      Big.positive_case
        (fun q1 ->
        (Big.double
        q1))
        (fun q1 ->
        (Big.doubleplusone
        q1))
        (fun _ ->
        Big.zero)
        q0)
      p
  
  (** val shiftl_nat :
      Big.big_int
      ->
      nat
      ->
      Big.big_int **)
  
  let shiftl_nat p n =
    nat_iter
      n
      (fun x ->
      Big.double
      x)
      p
  
  (** val shiftr_nat :
      Big.big_int
      ->
      nat
      ->
      Big.big_int **)
  
  let shiftr_nat p n =
    nat_iter
      n
      div2
      p
  
  (** val shiftl :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let shiftl p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter
        n0
        (fun x ->
        Big.double
        x)
        p)
      n
  
  (** val shiftr :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let shiftr p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter
        n0
        div2
        p)
      n
  
  (** val testbit_nat :
      Big.big_int
      ->
      nat
      ->
      bool **)
  
  let rec testbit_nat p n =
    Big.positive_case
      (fun p0 ->
      match n with
      | O ->
        true
      | S n' ->
        testbit_nat
          p0
          n')
      (fun p0 ->
      match n with
      | O ->
        false
      | S n' ->
        testbit_nat
          p0
          n')
      (fun _ ->
      match n with
      | O ->
        true
      | S n0 ->
        false)
      p
  
  (** val testbit :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let rec testbit p n =
    Big.positive_case
      (fun p0 ->
      Big.n_case
        (fun _ ->
        true)
        (fun n0 ->
        testbit
          p0
          (pred_N
            n0))
        n)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        false)
        (fun n0 ->
        testbit
          p0
          (pred_N
            n0))
        n)
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op :
      ('a1
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1
      ->
      'a1 **)
  
  let rec iter_op op p a =
    Big.positive_case
      (fun p0 ->
      op
        a
        (iter_op
          op
          p0
          (op
            a
            a)))
      (fun p0 ->
      iter_op
        op
        p0
        (op
          a
          a))
      (fun _ ->
      a)
      p
  
  (** val to_nat :
      Big.big_int
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
      Big.big_int **)
  
  let rec of_nat = function
  | O ->
    Big.one
  | S x ->
    (match x with
     | O ->
       Big.one
     | S n0 ->
       succ
         (of_nat
           x))
  
  (** val of_succ_nat :
      nat
      ->
      Big.big_int **)
  
  let rec of_succ_nat = function
  | O ->
    Big.one
  | S x ->
    succ
      (of_succ_nat
        x)
  
  (** val eq_dec :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let rec eq_dec p y0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        eq_dec
          p0
          p1)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        y0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun p1 ->
        eq_dec
          p0
          p1)
        (fun _ ->
        false)
        y0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        y0)
      p
  
  (** val peano_rect :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1 **)
  
  let rec peano_rect a f p =
    let f2 =
      peano_rect
        (f
          Big.one
          a)
        (fun p0 x ->
        f
          (succ
            (Big.double
            p0))
          (f
            (Big.double
            p0)
            x))
    in
    (Big.positive_case
       (fun q0 ->
       f
         (Big.double
         q0)
         (f2
           q0))
       (fun q0 ->
       f2
         q0)
       (fun _ ->
       a)
       p)
  
  (** val peano_rec :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of Big.big_int
     * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1
      ->
      (Big.big_int
      ->
      coq_PeanoView
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
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
      (Big.big_int
      ->
      coq_PeanoView
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
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
      Big.big_int
      ->
      coq_PeanoView
      ->
      coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne ->
    PeanoSucc
      (Big.one,
      PeanoOne)
  | PeanoSucc (p0,
               q1) ->
    PeanoSucc
      ((succ
         (Big.double
         p0)),
      (PeanoSucc
      ((Big.double
      p0),
      (peanoView_xO
        p0
        q1))))
  
  (** val peanoView_xI :
      Big.big_int
      ->
      coq_PeanoView
      ->
      coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne ->
    PeanoSucc
      ((succ
         Big.one),
      (PeanoSucc
      (Big.one,
      PeanoOne)))
  | PeanoSucc (p0,
               q1) ->
    PeanoSucc
      ((succ
         (Big.doubleplusone
         p0)),
      (PeanoSucc
      ((Big.doubleplusone
      p0),
      (peanoView_xI
        p0
        q1))))
  
  (** val peanoView :
      Big.big_int
      ->
      coq_PeanoView **)
  
  let rec peanoView p =
    Big.positive_case
      (fun p0 ->
      peanoView_xI
        p0
        (peanoView
          p0))
      (fun p0 ->
      peanoView_xO
        p0
        (peanoView
          p0))
      (fun _ ->
      PeanoOne)
      p
  
  (** val coq_PeanoView_iter :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
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
      Big.big_int
      ->
      Big.big_int
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
      Big.big_int
      ->
      Big.big_int
      ->
      reflect **)
  
  let leb_spec0 x y =
    iff_reflect
      (leb
        x
        y)
  
  (** val ltb_spec0 :
      Big.big_int
      ->
      Big.big_int
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
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let max_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           n
           (max
             n
             m)
           __
           (hl
             __)
       | _ ->
         compat
           m
           (max
             n
             m)
           __
           (hr
             __))
    
    (** val max_case :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let max_case n m x x0 x1 =
      max_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val max_dec :
        Big.big_int
        ->
        Big.big_int
        ->
        bool **)
    
    let max_dec n m =
      max_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
    
    (** val min_case_strong :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let min_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           m
           (min
             n
             m)
           __
           (hr
             __)
       | _ ->
         compat
           n
           (min
             n
             m)
           __
           (hl
             __))
    
    (** val min_case :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let min_case n m x x0 x1 =
      min_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val min_dec :
        Big.big_int
        ->
        Big.big_int
        ->
        bool **)
    
    let min_dec n m =
      min_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
   end
  
  (** val max_case_strong :
      Big.big_int
      ->
      Big.big_int
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
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val max_case :
      Big.big_int
      ->
      Big.big_int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let max_case n m x x0 =
    max_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val max_dec :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int
      ->
      Big.big_int
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
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val min_case :
      Big.big_int
      ->
      Big.big_int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let min_case n m x x0 =
    min_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val min_dec :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t
    =
    Big.big_int
  
  (** val zero :
      Big.big_int **)
  
  let zero =
    Big.zero
  
  (** val one :
      Big.big_int **)
  
  let one =
    Big.one
  
  (** val two :
      Big.big_int **)
  
  let two =
    (Big.double
      Big.one)
  
  (** val succ_double :
      Big.big_int
      ->
      Big.big_int **)
  
  let succ_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p ->
      (Big.doubleplusone
      p))
      x
  
  (** val double :
      Big.big_int
      ->
      Big.big_int **)
  
  let double n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Big.double
      p))
      n
  
  (** val succ :
      Big.big_int
      ->
      Big.big_int **)
  
  let succ = Big.succ
  
  (** val pred :
      Big.big_int
      ->
      Big.big_int **)
  
  let pred = fun n -> Big.max Big.zero (Big.pred n)
  
  (** val succ_pos :
      Big.big_int
      ->
      Big.big_int **)
  
  let succ_pos n =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p ->
      Coq_Pos.succ
        p)
      n
  
  (** val add :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let add = Big.add
  
  (** val sub :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let sub = fun n m -> Big.max Big.zero (Big.sub n m)
  
  (** val mul :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let mul = Big.mult
  
  (** val compare :
      Big.big_int
      ->
      Big.big_int
      ->
      comparison **)
  
  let compare = Big.compare_case Eq Lt Gt
  
  (** val eqb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let rec eqb n m =
    Big.n_case
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun p ->
      Big.n_case
        (fun _ ->
        false)
        (fun q0 ->
        Coq_Pos.eqb
          p
          q0)
        m)
      n
  
  (** val leb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let leb x y =
    match compare
            x
            y with
    | Gt ->
      false
    | _ ->
      true
  
  (** val ltb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let ltb x y =
    match compare
            x
            y with
    | Lt ->
      true
    | _ ->
      false
  
  (** val min :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let min = Big.min
  
  (** val max :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let max = Big.max
  
  (** val div2 :
      Big.big_int
      ->
      Big.big_int **)
  
  let div2 n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        p)
        (fun p ->
        p)
        (fun _ ->
        Big.zero)
        p0)
      n
  
  (** val even :
      Big.big_int
      ->
      bool **)
  
  let even n =
    Big.n_case
      (fun _ ->
      true)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      n
  
  (** val odd :
      Big.big_int
      ->
      bool **)
  
  let odd n =
    negb
      (even
        n)
  
  (** val pow :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let pow n p =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        Big.zero)
        (fun q0 ->
        (Coq_Pos.pow
          q0
          p0))
        n)
      p
  
  (** val square :
      Big.big_int
      ->
      Big.big_int **)
  
  let square n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.square
        p))
      n
  
  (** val log2 :
      Big.big_int
      ->
      Big.big_int **)
  
  let log2 n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        (Coq_Pos.size
          p))
        (fun p ->
        (Coq_Pos.size
          p))
        (fun _ ->
        Big.zero)
        p0)
      n
  
  (** val size :
      Big.big_int
      ->
      Big.big_int **)
  
  let size n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.size
        p))
      n
  
  (** val size_nat :
      Big.big_int
      ->
      nat **)
  
  let size_nat n =
    Big.n_case
      (fun _ ->
      O)
      (fun p ->
      Coq_Pos.size_nat
        p)
      n
  
  (** val pos_div_eucl :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int * Big.big_int **)
  
  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q0,
           r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        succ_double
          r
      in
      if leb
           b
           r'
      then ((succ_double
              q0),
             (sub
               r'
               b))
      else ((double
              q0),
             r'))
      (fun a' ->
      let (q0,
           r) =
        pos_div_eucl
          a'
          b
      in
      let r' =
        double
          r
      in
      if leb
           b
           r'
      then ((succ_double
              q0),
             (sub
               r'
               b))
      else ((double
              q0),
             r'))
      (fun _ ->
      Big.n_case
        (fun _ ->
        (Big.zero,
        Big.one))
        (fun p ->
        Big.positive_case
          (fun p0 ->
          (Big.zero,
          Big.one))
          (fun p0 ->
          (Big.zero,
          Big.one))
          (fun _ ->
          (Big.one,
          Big.zero))
          p)
        b)
      a
  
  (** val div_eucl :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int * Big.big_int **)
  
  let div_eucl a b =
    Big.n_case
      (fun _ ->
      (Big.zero,
      Big.zero))
      (fun na ->
      Big.n_case
        (fun _ ->
        (Big.zero,
        a))
        (fun p ->
        pos_div_eucl
          na
          b)
        b)
      a
  
  (** val div :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let div = fun a b -> if Big.eq b Big.zero then Big.zero else Big.div a b
  
  (** val modulo :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let modulo = fun a b -> if Big.eq b Big.zero then Big.zero else Big.modulo a b
  
  (** val gcd :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let gcd a b =
    Big.n_case
      (fun _ ->
      b)
      (fun p ->
      Big.n_case
        (fun _ ->
        a)
        (fun q0 ->
        (Coq_Pos.gcd
          p
          q0))
        b)
      a
  
  (** val ggcd :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    Big.n_case
      (fun _ ->
      (b,
      (Big.zero,
      Big.one)))
      (fun p ->
      Big.n_case
        (fun _ ->
        (a,
        (Big.one,
        Big.zero)))
        (fun q0 ->
        let (g,
             p0) =
          Coq_Pos.ggcd
            p
            q0
        in
        let (aa,
             bb) =
          p0
        in
        (g,
        (aa,
        bb)))
        b)
      a
  
  (** val sqrtrem :
      Big.big_int
      ->
      Big.big_int * Big.big_int **)
  
  let sqrtrem n =
    Big.n_case
      (fun _ ->
      (Big.zero,
      Big.zero))
      (fun p ->
      let (s,
           m) =
        Coq_Pos.sqrtrem
          p
      in
      (match m with
       | Coq_Pos.IsPos r ->
         (s,
           r)
       | _ ->
         (s,
           Big.zero)))
      n
  
  (** val sqrt :
      Big.big_int
      ->
      Big.big_int **)
  
  let sqrt n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.sqrt
        p))
      n
  
  (** val coq_lor :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let coq_lor n m =
    Big.n_case
      (fun _ ->
      m)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q0 ->
        (Coq_Pos.coq_lor
          p
          q0))
        m)
      n
  
  (** val coq_land :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let coq_land n m =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.n_case
        (fun _ ->
        Big.zero)
        (fun q0 ->
        Coq_Pos.coq_land
          p
          q0)
        m)
      n
  
  (** val ldiff :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let rec ldiff n m =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q0 ->
        Coq_Pos.ldiff
          p
          q0)
        m)
      n
  
  (** val coq_lxor :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let coq_lxor n m =
    Big.n_case
      (fun _ ->
      m)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q0 ->
        Coq_Pos.coq_lxor
          p
          q0)
        m)
      n
  
  (** val shiftl_nat :
      Big.big_int
      ->
      nat
      ->
      Big.big_int **)
  
  let shiftl_nat a n =
    nat_iter
      n
      double
      a
  
  (** val shiftr_nat :
      Big.big_int
      ->
      nat
      ->
      Big.big_int **)
  
  let shiftr_nat a n =
    nat_iter
      n
      div2
      a
  
  (** val shiftl :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let shiftl a n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      (Coq_Pos.shiftl
        a0
        n))
      a
  
  (** val shiftr :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let shiftr a n =
    Big.n_case
      (fun _ ->
      a)
      (fun p ->
      Coq_Pos.iter
        p
        div2
        a)
      n
  
  (** val testbit_nat :
      Big.big_int
      ->
      nat
      ->
      bool **)
  
  let testbit_nat a =
    Big.n_case
      (fun _ x ->
      false)
      (fun p ->
      Coq_Pos.testbit_nat
        p)
      a
  
  (** val testbit :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let testbit a n =
    Big.n_case
      (fun _ ->
      false)
      (fun p ->
      Coq_Pos.testbit
        p
        n)
      a
  
  (** val to_nat :
      Big.big_int
      ->
      nat **)
  
  let to_nat a =
    Big.n_case
      (fun _ ->
      O)
      (fun p ->
      Coq_Pos.to_nat
        p)
      a
  
  (** val of_nat :
      nat
      ->
      Big.big_int **)
  
  let of_nat = function
  | O ->
    Big.zero
  | S n' ->
    (Coq_Pos.of_succ_nat
      n')
  
  (** val iter :
      Big.big_int
      ->
      ('a1
      ->
      'a1)
      ->
      'a1
      ->
      'a1 **)
  
  let iter n f x =
    Big.n_case
      (fun _ ->
      x)
      (fun p ->
      Coq_Pos.iter
        p
        f
        x)
      n
  
  (** val eq_dec :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let eq_dec n m =
    Big.n_case
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun x ->
      Big.n_case
        (fun _ ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec
          x
          p0)
        m)
      n
  
  (** val discr :
      Big.big_int
      ->
      Big.big_int
      option **)
  
  let discr n =
    Big.n_case
      (fun _ ->
      None)
      (fun p ->
      Some
      p)
      n
  
  (** val binary_rect :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1 **)
  
  let binary_rect f0 f2 fS2 n =
    let f2' =
      fun p ->
      f2
        p
    in
    let fS2' =
      fun p ->
      fS2
        p
    in
    (Big.n_case
       (fun _ ->
       f0)
       (fun p ->
       let rec f p0 =
         Big.positive_case
           (fun p1 ->
           fS2'
             p1
             (f
               p1))
           (fun p1 ->
           f2'
             p1
             (f
               p1))
           (fun _ ->
           fS2
             Big.zero
             f0)
           p0
       in f
            p)
       n)
  
  (** val binary_rec :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1 **)
  
  let peano_rect f0 f n =
    let f' =
      fun p ->
      f
        p
    in
    (Big.n_case
       (fun _ ->
       f0)
       (fun p ->
       Coq_Pos.peano_rect
         (f
           Big.zero
           f0)
         f'
         p)
       n)
  
  (** val peano_rec :
      'a1
      ->
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
      ->
      'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 :
      Big.big_int
      ->
      Big.big_int
      ->
      reflect **)
  
  let leb_spec0 x y =
    iff_reflect
      (leb
        x
        y)
  
  (** val ltb_spec0 :
      Big.big_int
      ->
      Big.big_int
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
      (Big.big_int
      ->
      'a1
      ->
      'a1)
      ->
      Big.big_int
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
      Big.big_int
      ->
      Big.big_int **)
  
  let sqrt_up a =
    match compare
            Big.zero
            a with
    | Lt ->
      succ
        (sqrt
          (pred
            a))
    | _ ->
      Big.zero
  
  (** val log2_up :
      Big.big_int
      ->
      Big.big_int **)
  
  let log2_up a =
    match compare
            Big.one
            a with
    | Lt ->
      succ
        (log2
          (pred
            a))
    | _ ->
      Big.zero
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let lcm a b =
    mul
      a
      (div
        b
        (gcd
          a
          b))
  
  (** val eqb_spec :
      Big.big_int
      ->
      Big.big_int
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
      Big.big_int **)
  
  let b2n = function
  | true ->
    Big.one
  | false ->
    Big.zero
  
  (** val setbit :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let setbit a n =
    coq_lor
      a
      (shiftl
        Big.one
        n)
  
  (** val clearbit :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let clearbit a n =
    ldiff
      a
      (shiftl
        Big.one
        n)
  
  (** val ones :
      Big.big_int
      ->
      Big.big_int **)
  
  let ones n =
    pred
      (shiftl
        Big.one
        n)
  
  (** val lnot :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let lnot a n =
    coq_lxor
      a
      (ones
        n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let max_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           n
           (max
             n
             m)
           __
           (hl
             __)
       | _ ->
         compat
           m
           (max
             n
             m)
           __
           (hr
             __))
    
    (** val max_case :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let max_case n m x x0 x1 =
      max_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val max_dec :
        Big.big_int
        ->
        Big.big_int
        ->
        bool **)
    
    let max_dec n m =
      max_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
    
    (** val min_case_strong :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let min_case_strong n m compat hl hr =
      let c =
        compSpec2Type
          n
          m
          (compare
            n
            m)
      in
      (match c with
       | CompGtT ->
         compat
           m
           (min
             n
             m)
           __
           (hr
             __)
       | _ ->
         compat
           n
           (min
             n
             m)
           __
           (hl
             __))
    
    (** val min_case :
        Big.big_int
        ->
        Big.big_int
        ->
        (Big.big_int
        ->
        Big.big_int
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
    
    let min_case n m x x0 x1 =
      min_case_strong
        n
        m
        x
        (fun _ ->
        x0)
        (fun _ ->
        x1)
    
    (** val min_dec :
        Big.big_int
        ->
        Big.big_int
        ->
        bool **)
    
    let min_dec n m =
      min_case
        n
        m
        (fun x y _ h0 ->
        h0)
        true
        false
   end
  
  (** val max_case_strong :
      Big.big_int
      ->
      Big.big_int
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
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val max_case :
      Big.big_int
      ->
      Big.big_int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let max_case n m x x0 =
    max_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val max_dec :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int
      ->
      Big.big_int
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
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong
      n
      m
      (fun x1 y _ x2 ->
      x2)
      x
      x0
  
  (** val min_case :
      Big.big_int
      ->
      Big.big_int
      ->
      'a1
      ->
      'a1
      ->
      'a1 **)
  
  let min_case n m x x0 =
    min_case_strong
      n
      m
      (fun _ ->
      x)
      (fun _ ->
      x0)
  
  (** val min_dec :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t
    =
    Big.big_int
  
  (** val zero :
      Big.big_int **)
  
  let zero =
    Big.zero
  
  (** val one :
      Big.big_int **)
  
  let one =
    Big.one
  
  (** val two :
      Big.big_int **)
  
  let two =
    (Big.double
      Big.one)
  
  (** val double :
      Big.big_int
      ->
      Big.big_int **)
  
  let double x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Big.double
      p))
      (fun p ->
      Big.opp
      (Big.double
      p))
      x
  
  (** val succ_double :
      Big.big_int
      ->
      Big.big_int **)
  
  let succ_double x =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      (Big.doubleplusone
      p))
      (fun p ->
      Big.opp
      (Coq_Pos.pred_double
        p))
      x
  
  (** val pred_double :
      Big.big_int
      ->
      Big.big_int **)
  
  let pred_double x =
    Big.z_case
      (fun _ ->
      Big.opp
      Big.one)
      (fun p ->
      (Coq_Pos.pred_double
        p))
      (fun p ->
      Big.opp
      (Big.doubleplusone
      p))
      x
  
  (** val pos_sub :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let rec pos_sub x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q0 ->
        double
          (pos_sub
            p
            q0))
        (fun q0 ->
        succ_double
          (pos_sub
            p
            q0))
        (fun _ ->
        (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q0 ->
        pred_double
          (pos_sub
            p
            q0))
        (fun q0 ->
        double
          (pos_sub
            p
            q0))
        (fun _ ->
        (Coq_Pos.pred_double
          p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q0 ->
        Big.opp
        (Big.double
        q0))
        (fun q0 ->
        Big.opp
        (Coq_Pos.pred_double
          q0))
        (fun _ ->
        Big.zero)
        y)
      x
  
  (** val add :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let add = Big.add
  
  (** val opp :
      Big.big_int
      ->
      Big.big_int **)
  
  let opp = Big.opp
  
  (** val succ :
      Big.big_int
      ->
      Big.big_int **)
  
  let succ = Big.succ
  
  (** val pred :
      Big.big_int
      ->
      Big.big_int **)
  
  let pred = Big.pred
  
  (** val sub :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let sub = Big.sub
  
  (** val mul :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let mul = Big.mult
  
  (** val pow_pos :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let pow_pos z n =
    Coq_Pos.iter
      n
      (mul
        z)
      Big.one
  
  (** val pow :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let pow x y =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      pow_pos
        x
        p)
      (fun p ->
      Big.zero)
      y
  
  (** val square :
      Big.big_int
      ->
      Big.big_int **)
  
  let square x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.square
        p))
      (fun p ->
      (Coq_Pos.square
        p))
      x
  
  (** val compare :
      Big.big_int
      ->
      Big.big_int
      ->
      comparison **)
  
  let compare = Big.compare_case Eq Lt Gt
  
  (** val sgn :
      Big.big_int
      ->
      Big.big_int **)
  
  let sgn z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.one)
      (fun p ->
      Big.opp
      Big.one)
      z
  
  (** val leb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let leb x y =
    match compare
            x
            y with
    | Gt ->
      false
    | _ ->
      true
  
  (** val ltb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let ltb x y =
    match compare
            x
            y with
    | Lt ->
      true
    | _ ->
      false
  
  (** val geb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let geb x y =
    match compare
            x
            y with
    | Lt ->
      false
    | _ ->
      true
  
  (** val gtb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let gtb x y =
    match compare
            x
            y with
    | Gt ->
      true
    | _ ->
      false
  
  (** val eqb :
      Big.big_int
      ->
      Big.big_int
      ->
      bool **)
  
  let rec eqb x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun q0 ->
        Coq_Pos.eqb
          p
          q0)
        (fun p0 ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun q0 ->
        Coq_Pos.eqb
          p
          q0)
        y)
      x
  
  (** val max :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let max = Big.max
  
  (** val min :
      Big.big_int
      ->
      Big.big_int
      ->
      Big.big_int **)
  
  let min = Big.min
  
  (** val abs : Big.big_int -> Big.big_int **)
  
  let abs = Big.abs
  
  (** val abs_nat : Big.big_int -> nat **)
  
  let abs_nat z =
    Big.z_case
      (fun _ ->
      O)
      (fun p ->
      Coq_Pos.to_nat p)
      (fun p ->
      Coq_Pos.to_nat p)
      z
  
  (** val abs_N : Big.big_int -> Big.big_int **)
  
  let abs_N = Big.abs
  
  (** val to_nat : Big.big_int -> nat **)
  
  let to_nat z =
    Big.z_case
      (fun _ ->
      O)
      (fun p ->
      Coq_Pos.to_nat p)
      (fun p ->
      O)
      z
  
  (** val to_N : Big.big_int -> Big.big_int **)
  
  let to_N z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      p)
      (fun p ->
      Big.zero)
      z
  
  (** val of_nat : nat -> Big.big_int **)
  
  let of_nat = function
  | O -> Big.zero
  | S n0 -> (Coq_Pos.of_succ_nat n0)
  
  (** val of_N : Big.big_int -> Big.big_int **)
  
  let of_N = fun p -> p
  
  (** val to_pos : Big.big_int -> Big.big_int **)
  
  let to_pos z =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      p)
      (fun p ->
      Big.one)
      z
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n f x =
    Big.z_case
      (fun _ ->
      x)
      (fun p ->
      Coq_Pos.iter p f x)
      (fun p ->
      x)
      n
  
  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Big.double Big.one) r) Big.one in
      if ltb r' b
      then ((mul (Big.double Big.one) q0), r')
      else ((add (mul (Big.double Big.one) q0) Big.one), (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Big.double Big.one) r in
      if ltb r' b
      then ((mul (Big.double Big.one) q0), r')
      else ((add (mul (Big.double Big.one) q0) Big.one), (sub r' b)))
      (fun _ ->
      if leb (Big.double Big.one) b
      then (Big.zero, Big.one)
      else (Big.one, Big.zero))
      a
  
  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let div_eucl a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun p ->
        pos_div_eucl a' b)
        (fun b' ->
        let (q0, r) = pos_div_eucl a' b' in
        (Big.z_case
           (fun _ -> ((opp q0),
           Big.zero))
           (fun p -> ((opp (add q0 Big.one)),
           (add b r)))
           (fun p -> ((opp (add q0 Big.one)),
           (add b r)))
           r))
        b)
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun p ->
        let (q0, r) = pos_div_eucl a' b in
        (Big.z_case
           (fun _ -> ((opp q0),
           Big.zero))
           (fun p0 -> ((opp (add q0 Big.one)),
           (sub b r)))
           (fun p0 -> ((opp (add q0 Big.one)),
           (sub b r)))
           r))
        (fun b' ->
        let (q0, r) = pos_div_eucl a' b' in (q0, (opp r)))
        b)
      a
  
  (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let div a b =
    let (q0, x) = div_eucl a b in q0
  
  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let modulo a b =
    let (x, r) = div_eucl a b in r
  
  (** val quotrem :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let quotrem a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a0 ->
      Big.z_case
        (fun _ -> (Big.zero,
        a))
        (fun b0 ->
        let (q0, r) = N.pos_div_eucl a0 b0 in ((of_N q0), (of_N r)))
        (fun b0 ->
        let (q0, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q0)), (of_N r)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ -> (Big.zero,
        a))
        (fun b0 ->
        let (q0, r) = N.pos_div_eucl a0 b0 in
        ((opp (of_N q0)), (opp (of_N r))))
        (fun b0 ->
        let (q0, r) = N.pos_div_eucl a0 b0 in ((of_N q0), (opp (of_N r))))
        b)
      a
  
  (** val quot : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : Big.big_int -> bool **)
  
  let even z =
    Big.z_case
      (fun _ ->
      true)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      z
  
  (** val odd : Big.big_int -> bool **)
  
  let odd z =
    Big.z_case
      (fun _ ->
      false)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      z
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p -> Big.opp
      (Coq_Pos.div2_up p))
      z
  
  (** val quot2 : Big.big_int -> Big.big_int **)
  
  let quot2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun p0 ->
        (Coq_Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 -> Big.opp
        (Coq_Pos.div2 p))
        (fun p0 -> Big.opp
        (Coq_Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      z
  
  (** val log2 : Big.big_int -> Big.big_int **)
  
  let log2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        (Coq_Pos.size p))
        (fun p ->
        (Coq_Pos.size p))
        (fun _ ->
        Big.zero)
        p0)
      (fun p ->
      Big.zero)
      z
  
  (** val sqrtrem : Big.big_int -> Big.big_int * Big.big_int **)
  
  let sqrtrem n =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun p ->
      let (s, m) = Coq_Pos.sqrtrem p in
      (match m with
       | Coq_Pos.IsPos r -> (s, r)
       | _ -> (s, Big.zero)))
      (fun p -> (Big.zero,
      Big.zero))
      n
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt n =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Coq_Pos.sqrt p))
      (fun p ->
      Big.zero)
      n
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    Big.z_case
      (fun _ ->
      abs b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        abs a)
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        abs a)
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        (fun b0 ->
        (Coq_Pos.gcd a0 b0))
        b)
      a
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    Big.z_case
      (fun _ -> ((abs b), (Big.zero,
      (sgn b))))
      (fun a0 ->
      Big.z_case
        (fun _ -> ((abs a), ((sgn a),
        Big.zero)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, (Big.opp bb))))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ -> ((abs a), ((sgn a),
        Big.zero)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big.opp aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big.opp aa), (Big.opp bb))))
        b)
      a
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let testbit a n =
    Big.z_case
      (fun _ ->
      odd a)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun a0 ->
        Coq_Pos.testbit a0 p)
        (fun a0 ->
        negb (N.testbit (Coq_Pos.pred_N a0) p))
        a)
      (fun p ->
      false)
      n
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl a n =
    Big.z_case
      (fun _ ->
      a)
      (fun p ->
      Coq_Pos.iter p (mul (Big.double Big.one)) a)
      (fun p ->
      Coq_Pos.iter p div2 a)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr a n =
    shiftl a (opp n)
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lor a b =
    Big.z_case
      (fun _ ->
      b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        (Coq_Pos.coq_lor a0 b0))
        (fun b0 -> Big.opp
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_land a b =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        Big.zero)
        (fun b0 ->
        of_N (Coq_Pos.coq_land a0 b0))
        (fun b0 ->
        of_N (N.ldiff a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        Big.zero)
        (fun b0 ->
        of_N (N.ldiff b0 (Coq_Pos.pred_N a0)))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let ldiff a b =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Coq_Pos.ldiff a0 b0))
        (fun b0 ->
        of_N (N.coq_land a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
        b)
      a
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lxor a b =
    Big.z_case
      (fun _ ->
      b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Coq_Pos.coq_lxor a0 b0))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lxor a0 (Coq_Pos.pred_N b0))))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
        b)
      a
  
  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)
  
  let eq_dec x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x0 p0)
        (fun p0 ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun p0 ->
        Coq_Pos.eq_dec x0 p0)
        y)
      x
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
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
  
  (** val sqrt_up : Big.big_int -> Big.big_int **)
  
  let sqrt_up a =
    match compare Big.zero a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Big.zero
  
  (** val log2_up : Big.big_int -> Big.big_int **)
  
  let log2_up a =
    match compare Big.one a with
    | Lt -> succ (log2 (pred a))
    | _ -> Big.zero
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let div =
        quot
      
      (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : Big.big_int -> Big.big_int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> Big.big_int **)
  
  let b2z = function
  | true -> Big.one
  | false -> Big.zero
  
  (** val setbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let setbit a n =
    coq_lor a (shiftl Big.one n)
  
  (** val clearbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let clearbit a n =
    ldiff a (shiftl Big.one n)
  
  (** val lnot : Big.big_int -> Big.big_int **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : Big.big_int -> Big.big_int **)
  
  let ones n =
    pred (shiftl Big.one n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))
    
    (** val max_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : Big.big_int -> Big.big_int -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))
    
    (** val min_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : Big.big_int -> Big.big_int -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : Big.big_int -> Big.big_int -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : Big.big_int -> Big.big_int -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1 **)

let rec pow_pos0 rmul x i =
  Big.positive_case
    (fun i0 ->
    let p = pow_pos0 rmul x i0 in rmul x (rmul p p))
    (fun i0 ->
    let p = pow_pos0 rmul x i0 in rmul p p)
    (fun _ ->
    x)
    i

type q = { qnum : Big.big_int; qden : Big.big_int }

(** val qnum : q -> Big.big_int **)

let qnum x = x.qnum

(** val qden : q -> Big.big_int **)

let qden x = x.qden

(** val inject_Z : Big.big_int -> q **)

let inject_Z x =
  { qnum = x; qden = Big.one }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum q0.qden) (Z.mul q0.qnum p.qden)

(** val qeq_dec : q -> q -> bool **)

let qeq_dec x y =
  Z.eq_dec (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)); qden =
    (Coq_Pos.mul x.qden y.qden) }

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
  Big.z_case
    (fun _ -> { qnum = Big.zero; qden =
    Big.one })
    (fun p -> { qnum = x.qden; qden =
    p })
    (fun p -> { qnum = (Big.opp x.qden); qden =
    p })
    x.qnum

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val qpower_positive : q -> Big.big_int -> q **)

let qpower_positive q0 p =
  pow_pos0 qmult q0 p

(** val qpower : q -> Big.big_int -> q **)

let qpower q0 z =
  Big.z_case
    (fun _ -> { qnum = Big.one; qden =
    Big.one })
    (fun p ->
    qpower_positive q0 p)
    (fun p ->
    qinv (qpower_positive q0 p))
    z

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
  (** val min : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 **)
  
  let min le_total x y =
    if le_total x y then x else y
  
  (** val min_case :
      ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> 'a2 **)
  
  let min_case le_total x y hx hy =
    if le_total x y then hx __ else hy __
  
  (** val max : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> 'a1 **)
  
  let max le_total x y =
    if le_total y x then x else y
  
  (** val max_case :
      ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> 'a2 **)
  
  let max_case le_total x y x0 x1 =
    let flip_le_total = fun x2 y0 -> le_total y0 x2 in
    min_case flip_le_total x y x0 x1
 end

(** val qlt_le_dec_fast : q -> q -> bool **)

let qlt_le_dec_fast x y =
  let c = qcompare x y in
  (match c with
   | Lt -> true
   | _ -> false)

(** val qle_total : q -> q -> bool **)

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
  let (r1, r2) = snd (Z.ggcd q1 q2) in { qnum = r1; qden = (Z.to_pos r2) }

(** val qminus' : q -> q -> q **)

let qminus' x y =
  qred (qminus x y)

(** val qfloor : q -> Big.big_int **)

let qfloor x =
  let { qnum = n; qden = d } = x in Z.div n d

(** val qceiling : q -> Big.big_int **)

let qceiling x =
  Z.opp (qfloor (qopp x))

(** val ap_Q_cotransitive0 : q -> q -> q -> (__, __) sum **)

let ap_Q_cotransitive0 x y z =
  if qeq_dec x z then Inr __ else Inl __

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

let ap_Q_cotransitive1 x y z =
  ap_Q_cotransitive0 x y z

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

(** val qposMake : Big.big_int -> Big.big_int -> qpos **)

let qposMake num den =
  { qnum = num; qden = den }

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

(** val qpos_power : qpos -> Big.big_int -> qpos **)

let qpos_power x z =
  mkQpos (qpower (qposAsQ x) z)

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
    metricSpace -> (qpos -> st_car -> st_car -> bool) -> qposInf -> st_car ->
    st_car -> bool **)

let ball_ex_dec x ball_dec e a b =
  match e with
  | Qpos2QposInf e0 -> ball_dec e0 a b
  | QposInfinity -> true

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

let uc_compose x y z g f =
  Obj.magic { ucFun = (fun x0 ->
    (Obj.magic g).ucFun ((Obj.magic f).ucFun x0)); mu = (fun e ->
    qposInf_bind (Obj.magic f).mu ((Obj.magic g).mu e)) }

type decidableMetric = qpos -> st_car -> st_car -> bool

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
        (qposInf_mult (Qpos2QposInf (qposMake Big.one (Big.double Big.one)))
          e)))
    (qposInf_mult (Qpos2QposInf (qposMake Big.one (Big.double Big.one))) e)

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
  if s
  then false
  else let s0 = qlt_le_dec_fast (qposAsQ e) d in if s0 then false else true

(** val qball_ex_bool : qposInf -> st_car -> st_car -> bool **)

let qball_ex_bool e a b =
  if ball_ex_dec q_as_MetricSpace qmetric_dec e a b then true else false

(** val q_0 : q zero0 **)

let q_0 =
  { qnum = Big.zero; qden = Big.one }

(** val q_1 : q one0 **)

let q_1 =
  { qnum = Big.one; qden = Big.one }

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
  (Big.z_case
     (fun _ ->
     QposInfinity)
     (fun an -> Qpos2QposInf
     (qpos_mult (qposMake ad an) e))
     (fun an -> Qpos2QposInf
     (qpos_mult (qposMake ad an) e))
     qnum0)

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
  if p s then nil else cons (hd s) (takeUntil p (tl s) cons nil)

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
      (Obj.magic { qnum = Big.zero; qden = Big.one })) s

(** val infiniteAlternatingSum : q stream -> st_car **)

let infiniteAlternatingSum seq =
  Obj.magic (Obj.magic (infiniteAlternatingSum_raw seq))

(** val pfactorials_help :
    Big.big_int -> Big.big_int -> Big.big_int stream **)

let rec pfactorials_help n c =
  lazy (Cons (c, (pfactorials_help (Coq_Pos.succ n) (Coq_Pos.mul n c))))

(** val pfactorials : Big.big_int stream **)

let pfactorials =
  pfactorials_help Big.one Big.one

(** val qrecip_factorials : q stream **)

let qrecip_factorials =
  map (fun x -> { qnum = Big.one; qden = x }) pfactorials

(** val qpower_N_modulus : Big.big_int -> qpos -> qpos -> qposInf **)

let qpower_N_modulus n c e =
  Big.n_case
    (fun _ ->
    QposInfinity)
    (fun p ->
    Qpos2QposInf
    (qpos_mult
      e
      (qpos_inv
        (qpos_mult
          (qposMake
            p
            Big.one)
          (qpos_power
            c
            (Z.pred
              p))))))
    n

(** val qpower_N_uc :
    Big.big_int
    ->
    qpos
    ->
    st_car **)

let qpower_N_uc n c =
  Obj.magic
    { ucFun =
    (fun x ->
    Obj.magic
      (qpower
        (Obj.magic
          ((Obj.magic
             (qboundAbs
               c)).ucFun
            x))
        (Z.of_N
          n)));
    mu =
    (qpower_N_modulus
      n
      c) }

(** val cRpower_N_bounded :
    Big.big_int
    ->
    qpos
    ->
    st_car **)

let cRpower_N_bounded n c =
  cmap
    q_as_MetricSpace
    q_as_MetricSpace
    (qpower_N_uc
      n
      c)

(** val approximateQ :
    q
    ->
    Big.big_int
    ->
    q **)

let approximateQ x p =
  let { qnum =
    n;
    qden =
    d } =
    x
  in
  { qnum =
  (Z.div
    (Z.mul
      n
      p)
    d);
  qden =
  p }

(** val compress_raw :
    st_car
    ->
    qposInf
    ->
    q **)

let compress_raw x e = match e with
| Qpos2QposInf e0 ->
  let { qnum =
    n;
    qden =
    d } =
    qposAsQ
      e0
  in
  (Big.z_case
     (fun _ ->
     Obj.magic
       (approximate
         q_as_MetricSpace
         (Obj.magic
           x)
         (Qpos2QposInf
         e0)))
     (fun p ->
     approximateQ
       (Obj.magic
         (approximate
           q_as_MetricSpace
           (Obj.magic
             x)
           (Qpos2QposInf
           (qposMake
             Big.one
             p))))
       p)
     (fun p ->
     Obj.magic
       (approximate
         q_as_MetricSpace
         (Obj.magic
           x)
         (Qpos2QposInf
         e0)))
     (Z.succ
       (Z.div
         (Z.mul
           (Big.double
           Big.one)
           d)
         n)))
| QposInfinity ->
  Obj.magic
    (approximate
      q_as_MetricSpace
      (Obj.magic
        x)
      e)

(** val compress_fun :
    st_car
    ->
    st_car **)

let compress_fun x =
  Obj.magic
    (Obj.magic
      (compress_raw
        x))

(** val compress :
    st_car **)

let compress =
  Obj.magic
    { ucFun =
    compress_fun;
    mu =
    (fun x ->
    Qpos2QposInf
    x) }

(** val expSequence :
    q
    ->
    q
    stream **)

let expSequence a =
  mult_Streams
    q_mult
    qrecip_factorials
    (powers
      q_mult
      q_1
      a)

(** val rational_exp_small_neg :
    q
    ->
    st_car **)

let rational_exp_small_neg a =
  infiniteAlternatingSum
    (expSequence
      (qopp
        a))

(** val rational_exp_neg_bounded :
    nat
    ->
    q
    ->
    st_car **)

let rec rational_exp_neg_bounded n a =
  match n with
  | O ->
    rational_exp_small_neg
      a
  | S n' ->
    if qlt_le_dec_fast
         a
         (qopp
           { qnum =
           Big.one;
           qden =
           Big.one })
    then (Obj.magic
           (cRpower_N_bounded
             (Big.double
             Big.one)
             (qposMake
               Big.one
               Big.one))).ucFun
           ((Obj.magic
              compress).ucFun
             (rational_exp_neg_bounded
               n'
               (qdiv
                 a
                 (plus1
                   q_plus
                   (one1
                     q_1)
                   (one1
                     q_1)))))
    else rational_exp_small_neg
           a

(** val rational_exp_neg :
    q
    ->
    st_car **)

let rational_exp_neg a =
  rational_exp_neg_bounded
    (Big.z_case
       (fun _ ->
       O)
       (fun x ->
       Coq_Pos.size_nat
         x)
       (fun x ->
       Coq_Pos.size_nat
         x)
       a.qnum)
    a

(** val rational_exp :
    q
    ->
    st_car **)

let rational_exp a =
  let s =
    qle_total
      { qnum =
      Big.zero;
      qden =
      Big.one }
      a
  in
  if s
  then (Obj.magic
         (cRinv_pos
           (qpos_power
             (qposMake
               Big.one
               (Big.doubleplusone
               Big.one))
             (qceiling
               a)))).ucFun
         (rational_exp_neg
           (qopp
             a))
  else rational_exp_neg
         a

(** val exp_bound :
    Big.big_int
    ->
    qpos **)

let exp_bound z =
  Big.z_case
    (fun _ ->
    qposMake
      Big.one
      Big.one)
    (fun p ->
    qpos_power
      (qposMake
        (Big.doubleplusone
        Big.one)
        Big.one)
      p)
    (fun p ->
    qpos_power
      (qposMake
        Big.one
        (Big.double
        Big.one))
      p)
    z

(** val exp_bound_uc :
    Big.big_int
    ->
    st_car **)

let exp_bound_uc z =
  Obj.magic
    { ucFun =
    (fun a ->
    rational_exp
      (qmin
        (inject_Z
          z)
        (Obj.magic
          a)));
    mu =
    (qscale_modulus
      (qposAsQ
        (exp_bound
          z))) }

(** val exp_bounded :
    Big.big_int
    ->
    st_car **)

let exp_bounded z =
  cbind
    q_as_MetricSpace
    q_as_MetricSpace
    (exp_bound_uc
      z)

(** val exp :
    st_car
    ->
    st_car **)

let exp x =
  (Obj.magic
    (exp_bounded
      (qceiling
        (qplus
          (Obj.magic
            (approximate
              q_as_MetricSpace
              (Obj.magic
                x)
              (Qpos2QposInf
              (qposMake
                Big.one
                Big.one))))
          { qnum =
          Big.one;
          qden =
          Big.one })))).ucFun
    x

(** val answer :
    Big.big_int
    ->
    st_car
    ->
    Big.big_int **)

let answer n r =
  let m =
    Coq_Pos.iter
      n
      (Coq_Pos.mul
        (Big.double
        (Big.doubleplusone
        (Big.double
        Big.one))))
      Big.one
  in
  let { qnum =
    a;
    qden =
    b } =
    qmult
      (Obj.magic
        (approximate
          q_as_MetricSpace
          (Obj.magic
            r)
          (Qpos2QposInf
          (qposMake
            Big.one
            m))))
      (inject_Z
        m)
  in
  Z.div
    a
    b

(** val test :
    Big.big_int **)

let test =
  answer
    (Big.doubleplusone
    Big.one)
    (exp
      (inject_Q_CR
        { qnum =
        Big.one;
        qden =
        Big.one }))

