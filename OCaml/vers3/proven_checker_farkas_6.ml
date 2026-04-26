
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Nat =
 struct
  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    leb (Stdlib.Int.succ n) m

  (** val min : int -> int -> int **)

  let rec min n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> Stdlib.Int.succ (min n' m'))
        m)
      n
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> y)
      (fun x' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> x)
        (fun y' -> (Pos.add x' y'))
        (fun y' -> pos_sub x' y')
        y)
      (fun x' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> x)
        (fun y' -> pos_sub y' x')
        (fun y' -> (~-) (Pos.add x' y'))
        y)
      x

  (** val mul : int -> int -> int **)

  let mul x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun x' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun y' -> (Pos.mul x' y'))
        (fun y' -> (~-) (Pos.mul x' y'))
        y)
      (fun x' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun y' -> (~-) (Pos.mul x' y'))
        (fun y' -> (Pos.mul x' y'))
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> Eq)
        (fun _ -> Lt)
        (fun _ -> Gt)
        y)
      (fun x' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> Gt)
        (fun y' -> Pos.compare x' y')
        (fun _ -> Gt)
        y)
      (fun x' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun y' -> compOpp (Pos.compare x' y'))
        y)
      x

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val geb : int -> int -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
 end

(** val list_length : 'a1 list -> int **)

let rec list_length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (list_length l')

type z3_Variable_Bool = int

type z3_Variable_Int = int

type listIntExpr = (z3_Variable_Int * int list) list

type linIntExpr = (z3_Variable_Int * int) list

type linIntExprWithRHS = { vars : linIntExpr; int : int }

type farkasFormulas = { lhs : listIntExpr; rhs : int list }

type farkasStep = { mults : int list; constrs : farkasFormulas }

type z3_Equality = { eq_vars : linIntExpr; eq_int : int }

type z3_Formula =
| Z3var of z3_Variable_Bool
| Z3eq of z3_Equality
| Z3ineq of linIntExprWithRHS
| And of listZ3_Formula
| Or of listZ3_Formula
| Imply of z3_Formula * z3_Formula
| Not of z3_Formula
and listZ3_Formula =
| Lnil
| Lcons of z3_Formula * listZ3_Formula

type pos_Z3_Formula =
| Pos_z3var of z3_Variable_Bool
| Pos_z3eq of z3_Equality
| Pos_z3ineq of linIntExprWithRHS
| Pos_and of listZ3_Formula
| Pos_or of listZ3_Formula
| Pos_imply of z3_Formula * z3_Formula

type literal =
| Pos of pos_Z3_Formula
| Neg of pos_Z3_Formula

type clause = literal list

type formula = clause list

type tseitinStep =
| TseitinNot of z3_Formula
| TseitinImpElim of z3_Formula * z3_Formula
| TseitinImpIntro1 of z3_Formula * z3_Formula
| TseitinImpIntro2 of z3_Formula * z3_Formula
| TseitinImpIntro3 of z3_Formula * z3_Formula
| TseitinAndIntro of listZ3_Formula
| TseitinAndElim of listZ3_Formula * int
| TseitinOrIntro of listZ3_Formula * int
| TseitinOrElim of listZ3_Formula

type zProofItem =
| TseitinStep of tseitinStep
| AssumptionZ3 of listZ3_Formula
| RupZ3proof of listZ3_Formula
| TseitinStepRed of tseitinStep * listZ3_Formula
| Deletion of listZ3_Formula
| Farkas of farkasStep

type zClause = listZ3_Formula

(** val false_string : int **)

let false_string =
  Stdlib.Int.succ 0

(** val falseFor : z3_Formula **)

let falseFor =
  Z3var false_string

(** val negFor : z3_Formula -> z3_Formula **)

let negFor f = match f with
| Not x -> x
| _ -> Not f

(** val andFor : zClause -> z3_Formula **)

let andFor l =
  And l

(** val orFor : zClause -> z3_Formula **)

let orFor l =
  Or l

(** val nthWithDefault : int -> zClause -> z3_Formula -> z3_Formula **)

let rec nthWithDefault n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | Lnil -> default
              | Lcons (x, _) -> x)
    (fun n' ->
    match l with
    | Lnil -> default
    | Lcons (_, xs) -> nthWithDefault n' xs default)
    n

(** val negForList : zClause -> zClause **)

let rec negForList = function
| Lnil -> Lnil
| Lcons (a, rest) -> Lcons ((negFor a), (negForList rest))

(** val tseitinNot2For : z3_Formula -> zClause **)

let tseitinNot2For a =
  Lcons (a, (Lcons ((negFor a), Lnil)))

(** val tseitinImpElim2For : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpElim2For a b =
  Lcons ((negFor a), (Lcons (b, (Lcons ((Not (Imply (a, b))), Lnil)))))

(** val tseitinImpIntro1toFor : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpIntro1toFor a b =
  Lcons (a, (Lcons ((Imply (a, b)), Lnil)))

(** val tseitinImpIntro2toFor : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpIntro2toFor a b =
  Lcons ((negFor b), (Lcons ((Imply (a, b)), Lnil)))

(** val tseitinImpIntro3toFor : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpIntro3toFor a b =
  Lcons ((Not b), (Lcons ((Imply (a, b)), Lnil)))

(** val tseitinAndIntro2ForOpt : zClause -> zClause **)

let tseitinAndIntro2ForOpt l =
  Lcons ((andFor l), (negForList l))

(** val tseitinAndElim2For : zClause -> int -> zClause **)

let tseitinAndElim2For l i =
  Lcons ((nthWithDefault i l falseFor), (Lcons ((Not (andFor l)), Lnil)))

(** val tseitinOrIntro2For : zClause -> int -> zClause **)

let tseitinOrIntro2For l i =
  Lcons ((negFor (nthWithDefault i l falseFor)), (Lcons ((orFor l), Lnil)))

(** val tseitinOrElim2ForOpt : zClause -> zClause **)

let tseitinOrElim2ForOpt l =
  Lcons ((Not (orFor l)), l)

(** val tseitinProofItem2ConclusionOpt : tseitinStep -> zClause **)

let tseitinProofItem2ConclusionOpt = function
| TseitinNot a -> tseitinNot2For a
| TseitinImpElim (a, b) -> tseitinImpElim2For a b
| TseitinImpIntro1 (a, b) -> tseitinImpIntro1toFor a b
| TseitinImpIntro2 (a, b) -> tseitinImpIntro2toFor a b
| TseitinImpIntro3 (a, b) -> tseitinImpIntro3toFor a b
| TseitinAndIntro l -> tseitinAndIntro2ForOpt l
| TseitinAndElim (l, i) -> tseitinAndElim2For l i
| TseitinOrIntro (l, i) -> tseitinOrIntro2For l i
| TseitinOrElim l -> tseitinOrElim2ForOpt l

(** val pair_head_int_list_prime :
    z3_Variable_Int -> int list -> z3_Variable_Int * int **)

let pair_head_int_list_prime v = function
| [] -> (v, 0)
| x :: _ -> (v, x)

(** val pair_to_first_row : listIntExpr -> linIntExpr **)

let rec pair_to_first_row = function
| [] -> []
| p :: xs ->
  let (v, c) = p in (pair_head_int_list_prime v c) :: (pair_to_first_row xs)

(** val pair_tail_int_list_prime :
    z3_Variable_Int -> int list -> z3_Variable_Int * int list **)

let pair_tail_int_list_prime v = function
| [] -> (v, [])
| _ :: xs -> (v, xs)

(** val pair_to_tail : listIntExpr -> listIntExpr **)

let rec pair_to_tail = function
| [] -> []
| p :: xs ->
  let (v, c) = p in (pair_tail_int_list_prime v c) :: (pair_to_tail xs)

(** val pair_matrix_to_first_k_rows :
    listIntExpr -> int -> linIntExpr list **)

let rec pair_matrix_to_first_k_rows l k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k0 ->
    (pair_to_first_row l) :: (pair_matrix_to_first_k_rows (pair_to_tail l) k0))
    k

(** val pair_list_min_aux : listIntExpr -> int **)

let rec pair_list_min_aux = function
| [] -> 0
| p :: xs ->
  let (_, c) = p in
  (match xs with
   | [] -> list_length c
   | _ :: _ -> Nat.min (list_length c) (pair_list_min_aux xs))

(** val pair_matrix_to_rows : listIntExpr -> linIntExpr list **)

let pair_matrix_to_rows l =
  pair_matrix_to_first_k_rows l (pair_list_min_aux l)

(** val nonzero_coeff : (z3_Variable_Int * int) -> bool **)

let nonzero_coeff t =
  negb (Z.eqb (snd t) 0)

(** val prune_linexpr : linIntExpr -> linIntExpr **)

let prune_linexpr e =
  filter nonzero_coeff e

(** val lin_rows_with_rhs_aux :
    linIntExpr list -> int list -> linIntExprWithRHS list **)

let rec lin_rows_with_rhs_aux rows bs =
  match rows with
  | [] -> []
  | row :: rows' ->
    (match bs with
     | [] -> []
     | b :: bs' ->
       { vars = (prune_linexpr row); int =
         b } :: (lin_rows_with_rhs_aux rows' bs'))

(** val lin_rows_with_rhs : farkasFormulas -> linIntExprWithRHS list **)

let lin_rows_with_rhs ff =
  lin_rows_with_rhs_aux (pair_matrix_to_rows ff.lhs) ff.rhs

(** val negate_lin_rows : linIntExprWithRHS list -> listZ3_Formula **)

let rec negate_lin_rows = function
| [] -> Lnil
| r :: tl -> Lcons ((Not (Z3ineq r)), (negate_lin_rows tl))

(** val farkas_step_to_clause : farkasStep -> listZ3_Formula **)

let farkas_step_to_clause fs =
  let lhs0 = fs.constrs in negate_lin_rows (lin_rows_with_rhs lhs0)

(** val zProofItem2ConclusionOpt : zProofItem -> zClause **)

let zProofItem2ConclusionOpt = function
| TseitinStep a -> tseitinProofItem2ConclusionOpt a
| AssumptionZ3 a -> a
| RupZ3proof a -> a
| TseitinStepRed (_, c) -> c
| Deletion d -> d
| Farkas f -> farkas_step_to_clause f

(** val length_listZ3 : zClause -> int **)

let rec length_listZ3 = function
| Lnil -> 0
| Lcons (_, rest) -> Stdlib.Int.succ (length_listZ3 rest)

(** val z3_Variable_Int_eqb : z3_Variable_Int -> z3_Variable_Int -> bool **)

let z3_Variable_Int_eqb =
  (=)

(** val pair_int_expr_eqb :
    (z3_Variable_Int * int) -> (z3_Variable_Int * int) -> bool **)

let pair_int_expr_eqb p1 p2 =
  let (v1, c1) = p1 in
  let (v2, c2) = p2 in (&&) (z3_Variable_Int_eqb v1 v2) (Z.eqb c1 c2)

(** val linIntExpr_eqb : linIntExpr -> linIntExpr -> bool **)

let rec linIntExpr_eqb xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | p1 :: xs' ->
    (match ys with
     | [] -> false
     | p2 :: ys' -> (&&) (pair_int_expr_eqb p1 p2) (linIntExpr_eqb xs' ys'))

(** val linIntExprWithRHS_eqb :
    linIntExprWithRHS -> linIntExprWithRHS -> bool **)

let linIntExprWithRHS_eqb x y =
  (&&) (linIntExpr_eqb x.vars y.vars) (Z.eqb x.int y.int)

(** val z3_Equality_eqb : z3_Equality -> z3_Equality -> bool **)

let z3_Equality_eqb x y =
  (&&) (linIntExpr_eqb x.eq_vars y.eq_vars) (Z.eqb x.eq_int y.eq_int)

(** val z3_formula_eq : z3_Formula -> z3_Formula -> bool **)

let rec z3_formula_eq f1 f2 =
  match f1 with
  | Z3var x -> (match f2 with
                | Z3var y -> (=) x y
                | _ -> false)
  | Z3eq x -> (match f2 with
               | Z3eq y -> z3_Equality_eqb x y
               | _ -> false)
  | Z3ineq x ->
    (match f2 with
     | Z3ineq y -> linIntExprWithRHS_eqb x y
     | _ -> false)
  | And l1 -> (match f2 with
               | And l2 -> list_z3_formula_eq l1 l2
               | _ -> false)
  | Or l1 -> (match f2 with
              | Or l2 -> list_z3_formula_eq l1 l2
              | _ -> false)
  | Imply (a1, b1) ->
    (match f2 with
     | Imply (a2, b2) -> (&&) (z3_formula_eq a1 a2) (z3_formula_eq b1 b2)
     | _ -> false)
  | Not f1' -> (match f2 with
                | Not f2' -> z3_formula_eq f1' f2'
                | _ -> false)

(** val list_z3_formula_eq : listZ3_Formula -> listZ3_Formula -> bool **)

and list_z3_formula_eq l1 l2 =
  match l1 with
  | Lnil -> (match l2 with
             | Lnil -> true
             | Lcons (_, _) -> false)
  | Lcons (h1, t1) ->
    (match l2 with
     | Lnil -> false
     | Lcons (h2, t2) -> (&&) (z3_formula_eq h1 h2) (list_z3_formula_eq t1 t2))

(** val pos_z3_formula_eq : pos_Z3_Formula -> pos_Z3_Formula -> bool **)

let pos_z3_formula_eq p1 p2 =
  match p1 with
  | Pos_z3var x -> (match p2 with
                    | Pos_z3var y -> (=) x y
                    | _ -> false)
  | Pos_z3eq x ->
    (match p2 with
     | Pos_z3eq y -> z3_Equality_eqb x y
     | _ -> false)
  | Pos_z3ineq x ->
    (match p2 with
     | Pos_z3ineq y -> linIntExprWithRHS_eqb x y
     | _ -> false)
  | Pos_and l1 ->
    (match p2 with
     | Pos_and l2 -> list_z3_formula_eq l1 l2
     | _ -> false)
  | Pos_or l1 ->
    (match p2 with
     | Pos_or l2 -> list_z3_formula_eq l1 l2
     | _ -> false)
  | Pos_imply (l1, l2) ->
    (match p2 with
     | Pos_imply (l3, l4) -> (&&) (z3_formula_eq l1 l3) (z3_formula_eq l2 l4)
     | _ -> false)

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb l1 l2 =
  match l1 with
  | Pos p1 ->
    (match l2 with
     | Pos p2 -> pos_z3_formula_eq p1 p2
     | Neg _ -> false)
  | Neg p1 ->
    (match l2 with
     | Pos _ -> false
     | Neg p2 -> pos_z3_formula_eq p1 p2)

(** val negate : literal -> literal **)

let negate = function
| Pos x -> Neg x
| Neg x -> Pos x

type assumption = clause list

type splitClauses = (clause list * literal list) * bool

type preparePropStep = (clause list * literal list) * literal

type splitLiterals = literal list * bool

(** val removeLitFromClause : literal -> clause -> clause **)

let rec removeLitFromClause l = function
| [] -> []
| hd :: tl ->
  let new_clause = removeLitFromClause l tl in
  if literal_eqb l hd then new_clause else hd :: new_clause

(** val lit_in_clause : literal -> clause -> bool **)

let lit_in_clause l c =
  existsb (literal_eqb l) c

(** val processOneClause_aux2 : clause -> literal -> bool -> clause **)

let processOneClause_aux2 c l = function
| true -> removeLitFromClause (negate l) c
| false -> c

(** val processOneClause_aux1 : clause -> literal -> bool -> clause option **)

let processOneClause_aux1 c l = function
| true -> None
| false -> Some (processOneClause_aux2 c l (lit_in_clause (negate l) c))

(** val processOneClause : clause -> literal -> clause option **)

let processOneClause c l =
  processOneClause_aux1 c l (lit_in_clause l c)

(** val processClausesaux : clause option -> clause list -> clause list **)

let processClausesaux c ih =
  match c with
  | Some c0 -> c0 :: ih
  | None -> ih

(** val processClauses : clause list -> literal -> clause list **)

let rec processClauses c l =
  match c with
  | [] -> []
  | hd :: tl ->
    processClausesaux (processOneClause hd l) (processClauses tl l)

(** val addClauseToSplitClauses : clause -> splitClauses -> splitClauses **)

let addClauseToSplitClauses clause0 = function
| (p, boolIH) ->
  let (clausesIH, literalsIH) = p in
  (match clause0 with
   | [] -> (([], []), true)
   | l :: l0 ->
     (match l0 with
      | [] -> ((clausesIH, (l :: literalsIH)), boolIH)
      | _ :: _ -> (((clause0 :: clausesIH), literalsIH), boolIH)))

(** val splitClauses0 : clause list -> splitClauses **)

let rec splitClauses0 = function
| [] -> (([], []), false)
| c :: cs -> addClauseToSplitClauses c (splitClauses0 cs)

(** val processAndSplitClausesWithLit :
    clause list -> literal -> splitClauses **)

let processAndSplitClausesWithLit clauses l =
  let processed_clauses = processClauses clauses l in
  splitClauses0 processed_clauses

(** val processListLitsWithLit : literal list -> literal -> splitLiterals **)

let rec processListLitsWithLit literals l =
  match literals with
  | [] -> ([], false)
  | hd :: tl ->
    if literal_eqb hd l
    then processListLitsWithLit tl l
    else if literal_eqb hd (negate l)
         then ([], true)
         else let (remaining_literals, found_negation) =
                processListLitsWithLit tl l
              in
              ((hd :: remaining_literals), found_negation)

(** val combineSplitClausesSplitLits :
    splitClauses -> splitLiterals -> splitClauses **)

let combineSplitClausesSplitLits sc rl =
  let (p, contains_empty) = sc in
  let (processed_clauses, unit_literals) = p in
  let (filtered_literals, found_negation) = rl in
  ((processed_clauses, (app unit_literals filtered_literals)),
  ((||) contains_empty found_negation))

(** val propagationStep' :
    clause list -> literal list -> literal -> splitClauses **)

let propagationStep' clauses literals l =
  combineSplitClausesSplitLits (processAndSplitClausesWithLit clauses l)
    (processListLitsWithLit literals l)

(** val propagationStep : preparePropStep -> splitClauses **)

let propagationStep = function
| (p0, l) -> let (c, ls) = p0 in propagationStep' c ls l

(** val selectAndRunPropagator :
    splitClauses -> (splitClauses -> splitClauses) -> splitClauses **)

let selectAndRunPropagator sc cont =
  let (p, b) = sc in
  let (c, ls) = p in
  if b
  then sc
  else (match ls with
        | [] -> sc
        | l :: ls0 -> cont (propagationStep ((c, ls0), l)))

(** val iteratePropagator : int -> splitClauses -> splitClauses **)

let rec iteratePropagator n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> p)
    (fun n0 -> selectAndRunPropagator p (iteratePropagator n0))
    n

(** val splitClauses_to_bool : splitClauses -> bool **)

let splitClauses_to_bool = function
| (_, b) -> b

(** val literal_in_seen : literal -> pos_Z3_Formula list -> bool **)

let literal_in_seen l seen =
  match l with
  | Pos x -> existsb (pos_z3_formula_eq x) seen
  | Neg x -> existsb (pos_z3_formula_eq x) seen

(** val addVarsInClauseToSeen :
    clause -> pos_Z3_Formula list -> pos_Z3_Formula list **)

let rec addVarsInClauseToSeen c seen =
  match c with
  | [] -> seen
  | l :: ls ->
    let lit_str = match l with
                  | Pos x -> x
                  | Neg x -> x in
    if literal_in_seen l seen
    then addVarsInClauseToSeen ls seen
    else addVarsInClauseToSeen ls (lit_str :: seen)

(** val addVarsInForToSeen :
    formula -> pos_Z3_Formula list -> pos_Z3_Formula list **)

let rec addVarsInForToSeen f seen =
  match f with
  | [] -> seen
  | c :: cs ->
    let updated_seen = addVarsInClauseToSeen c seen in
    addVarsInForToSeen cs updated_seen

(** val countVarsInFor : formula -> int **)

let countVarsInFor f =
  list_length (addVarsInForToSeen f [])

(** val unitPropagationAndCheck : assumption -> bool **)

let unitPropagationAndCheck a =
  splitClauses_to_bool
    (iteratePropagator (countVarsInFor a) (splitClauses0 a))

(** val negate_clause : clause -> formula **)

let negate_clause c =
  map (fun l -> (negate l) :: []) c

(** val rUP_Checker : assumption -> clause -> bool **)

let rUP_Checker a c =
  unitPropagationAndCheck (app (negate_clause c) a)

(** val scale_Integers : int list -> int list -> int list **)

let rec scale_Integers ms l =
  match ms with
  | [] -> []
  | m :: ms0 ->
    (match l with
     | [] -> []
     | x :: tl -> (Z.mul m x) :: (scale_Integers ms0 tl))

(** val scale1Column :
    int list -> (z3_Variable_Int * int list) -> z3_Variable_Int * int list **)

let scale1Column ms = function
| (v, c) -> (v, (scale_Integers ms c))

(** val scaleColumns : int list -> listIntExpr -> listIntExpr **)

let rec scaleColumns ms = function
| [] -> []
| x :: xs -> (scale1Column ms x) :: (scaleColumns ms xs)

(** val add_Column : int list -> int **)

let rec add_Column = function
| [] -> 0
| l :: ls -> Z.add l (add_Column ls)

(** val add_Column_Pair :
    (z3_Variable_Int * int list) -> z3_Variable_Int * int **)

let add_Column_Pair = function
| (x, c) -> (match c with
             | [] -> (x, 0)
             | _ :: _ -> (x, (add_Column c)))

(** val add_ListIntExpr : listIntExpr -> linIntExpr **)

let rec add_ListIntExpr = function
| [] -> []
| x :: xs -> (add_Column_Pair x) :: (add_ListIntExpr xs)

(** val add_RHS : int list -> int **)

let rec add_RHS = function
| [] -> 0
| x :: tl -> Z.add x (add_RHS tl)

(** val scale_and_add_LHS : int list -> listIntExpr -> linIntExpr **)

let scale_and_add_LHS ms l =
  add_ListIntExpr (scaleColumns ms l)

(** val scale_and_add_RHS : int list -> int list -> int **)

let scale_and_add_RHS ms l =
  add_RHS (scale_Integers ms l)

(** val lhs_equals_zero : linIntExpr -> bool **)

let rec lhs_equals_zero = function
| [] -> true
| p :: xs ->
  let (_, z0) = p in
  ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
     (fun _ -> lhs_equals_zero xs)
     (fun _ -> false)
     (fun _ -> false)
     z0)

(** val lHS_zero_after_scaling : int list -> listIntExpr -> bool **)

let lHS_zero_after_scaling ms l =
  lhs_equals_zero (scale_and_add_LHS ms l)

(** val rHS_value_after_scaling : int list -> int list -> int **)

let rHS_value_after_scaling =
  scale_and_add_RHS

(** val ge_Z : int -> int -> bool **)

let ge_Z =
  Z.geb

(** val ge0b : int -> bool **)

let ge0b z0 =
  ge_Z z0 0

(** val ms_nonnegb : int list -> bool **)

let ms_nonnegb ms =
  forallb ge0b ms

(** val rows_rhs_len_eqb : farkasFormulas -> bool **)

let rows_rhs_len_eqb c =
  (=) (list_length (pair_matrix_to_rows c.lhs)) (list_length c.rhs)

(** val multiplier_check : int list -> farkasFormulas -> bool **)

let multiplier_check ms ff =
  let c = ff.lhs in (=) (list_length ms) (list_length (pair_matrix_to_rows c))

(** val farkas_contradiction : farkasStep -> bool **)

let farkas_contradiction f =
  let ms = f.mults in
  let c = f.constrs in
  let ms_ok = ms_nonnegb ms in
  let len_ok = rows_rhs_len_eqb c in
  let mults_ok = multiplier_check ms c in
  let lhs_zero = lHS_zero_after_scaling ms c.lhs in
  let rhs_val = rHS_value_after_scaling ms c.rhs in
  (&&) ((&&) ((&&) ((&&) ms_ok len_ok) mults_ok) lhs_zero)
    (negb (ge_Z 0 rhs_val))

(** val zfor2Lit : z3_Formula -> literal **)

let rec zfor2Lit = function
| Z3var v -> Pos (Pos_z3var v)
| Z3eq v -> Pos (Pos_z3eq v)
| Z3ineq v -> Pos (Pos_z3ineq v)
| And l -> Pos (Pos_and l)
| Or l -> Pos (Pos_or l)
| Imply (a, b) -> Pos (Pos_imply (a, b))
| Not x ->
  (match x with
   | Z3var v -> Neg (Pos_z3var v)
   | Z3eq v -> Neg (Pos_z3eq v)
   | Z3ineq v -> Neg (Pos_z3ineq v)
   | And l -> Neg (Pos_and l)
   | Or l -> Neg (Pos_or l)
   | Imply (a, b) -> Neg (Pos_imply (a, b))
   | Not y -> zfor2Lit y)

(** val zCl2RClause : zClause -> clause **)

let rec zCl2RClause = function
| Lnil -> []
| Lcons (x, xs) -> (zfor2Lit x) :: (zCl2RClause xs)

(** val zListCl2RListCl : zClause list -> clause list **)

let rec zListCl2RListCl = function
| [] -> []
| x :: xs -> (zCl2RClause x) :: (zListCl2RListCl xs)

(** val remove_listZ3_Formula :
    listZ3_Formula -> listZ3_Formula list -> listZ3_Formula list **)

let rec remove_listZ3_Formula target = function
| [] -> []
| x :: xs ->
  if list_z3_formula_eq x target
  then remove_listZ3_Formula target xs
  else x :: (remove_listZ3_Formula target xs)

(** val in_listZ3b : z3_Formula -> listZ3_Formula -> bool **)

let rec in_listZ3b x = function
| Lnil -> false
| Lcons (y, ys) -> (||) (z3_formula_eq x y) (in_listZ3b x ys)

(** val listZ3_subset : listZ3_Formula -> listZ3_Formula -> bool **)

let rec listZ3_subset l1 l2 =
  match l1 with
  | Lnil -> true
  | Lcons (x, xs) -> (&&) (in_listZ3b x l2) (listZ3_subset xs l2)

(** val negSingletons : listZ3_Formula -> listZ3_Formula list **)

let rec negSingletons = function
| Lnil -> []
| Lcons (f, rest) -> (Lcons ((negFor f), Lnil)) :: (negSingletons rest)

(** val in_listZ3List : listZ3_Formula -> listZ3_Formula list -> bool **)

let rec in_listZ3List x = function
| [] -> false
| y :: ys -> (||) (list_z3_formula_eq x y) (in_listZ3List x ys)

(** val listZ3List_subset :
    listZ3_Formula list -> listZ3_Formula list -> bool **)

let rec listZ3List_subset l1 l2 =
  match l1 with
  | [] -> true
  | x :: xs -> (&&) (in_listZ3List x l2) (listZ3List_subset xs l2)

(** val setminus : listZ3_Formula -> listZ3_Formula -> listZ3_Formula **)

let rec setminus a b =
  match a with
  | Lnil -> Lnil
  | Lcons (x, xs) ->
    if in_listZ3b x b then setminus xs b else Lcons (x, (setminus xs b))

(** val subset_in_list : listZ3_Formula -> listZ3_Formula list -> bool **)

let rec subset_in_list c = function
| [] -> false
| x :: xs -> if listZ3_subset c x then true else subset_in_list c xs

(** val zProofCheckTseitin : tseitinStep -> bool **)

let zProofCheckTseitin = function
| TseitinAndElim (l, i) -> Nat.ltb i (length_listZ3 l)
| TseitinOrIntro (l, i) -> Nat.ltb i (length_listZ3 l)
| _ -> true

(** val zProofCheckLastStep : zClause list -> zProofItem -> bool **)

let zProofCheckLastStep cl = function
| TseitinStep a -> zProofCheckTseitin a
| AssumptionZ3 _ -> true
| RupZ3proof l -> rUP_Checker (zListCl2RListCl cl) (zCl2RClause l)
| TseitinStepRed (a, c) ->
  (&&)
    ((&&) (listZ3_subset c (tseitinProofItem2ConclusionOpt a))
      (listZ3List_subset
        (negSingletons (setminus (tseitinProofItem2ConclusionOpt a) c)) cl))
    (zProofCheckTseitin a)
| Deletion d -> subset_in_list d cl
| Farkas f -> farkas_contradiction f

(** val zProof2ConclusionOptPrime :
    zClause list -> zProofItem -> zClause list **)

let zProof2ConclusionOptPrime ls x = match x with
| Deletion _ -> remove_listZ3_Formula (zProofItem2ConclusionOpt x) ls
| _ -> (zProofItem2ConclusionOpt x) :: ls

(** val checkList :
    zClause list -> zClause list -> zProofItem list -> bool -> (zClause
    list * zClause list) * bool **)

let rec checkList a c p b =
  match p with
  | [] -> (([], []), true)
  | s :: rs ->
    if b
    then let (p0, b0) = checkList a c rs b in
         let (al, cl) = p0 in
         let b' = zProofCheckLastStep cl s in
         let a' = zProof2ConclusionOptPrime al s in
         let c' = zProof2ConclusionOptPrime cl s in ((a', c'), ((&&) b0 b'))
    else ((a, c), b)

(** val checkList_trim :
    zClause list -> zProofItem list -> bool -> zClause list * bool **)

let rec checkList_trim c p b =
  match p with
  | [] -> ([], true)
  | s :: rs ->
    if b
    then let (cl, b0) = checkList_trim c rs b in
         let b' = zProofCheckLastStep cl s in
         let c' = zProof2ConclusionOptPrime cl s in (c', ((&&) b0 b'))
    else (c, b)
