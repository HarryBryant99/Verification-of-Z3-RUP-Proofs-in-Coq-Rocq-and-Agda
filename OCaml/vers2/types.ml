(*
type z3_variable = char list

type z3_formula =
  | Z3Var of z3_variable
  | And of list_z3_formula
  | Or of list_z3_formula
  | Imply of z3_formula * z3_formula
  | Not of z3_formula

and list_z3_formula =
  | LNil
  | LCons of z3_formula * list_z3_formula

type pos_z3_formula =
  | PosZ3Var of z3_variable
  | PosAnd of list_z3_formula
  | PosOr of list_z3_formula
  | PosImply of z3_formula * z3_formula

type literal =
  | Pos of pos_z3_formula
  | Neg of pos_z3_formula

type clause = literal list
*)

open Proven_sat_checker

type item =
  | Tseitin of listZ3_Formula * listZ3_Formula
  | Assumption of listZ3_Formula
  | Rup of listZ3_Formula


