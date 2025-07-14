open Rupchecker_z3_datatype

(*
type z3_variable = char list

type z3_formula =
  | Z3Var of z3_variable
  | And of z3_formula list
  | Or of z3_formula list
  | Imply of z3_formula list
  | Not of z3_formula

type pos_z3_formula =
  | PosZ3Var of z3_variable
  | PosAnd of z3_formula list
  | PosOr of z3_formula list
  | PosImply of z3_formula list

type literal =
  | Pos of pos_z3_formula
  | Neg of pos_z3_formula

type clause = literal list

type item =
  | Tseitin of clause * clause
  | Assumption of clause
  | Rup of clause
*)