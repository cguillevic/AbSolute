(* Copyright 2019 AbSolute Team

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

open Bounds
open Core
open Core.Types

exception Wrong_modelling of string
type vname = string
type i = Bound_rat.t
type binop = ADD | SUB | MUL | DIV | POW
type cmpop = EQ | LEQ | GEQ | NEQ | GT | LT
type expr =
  | Funcall of string * expr list
  | Poly  of binop * expr list
  | Var     of vname
  | Cst     of i * var_concrete_ty

type bconstraint = (expr * cmpop * expr)
type formula =
  | FVar of vname
  | Cmp of bconstraint
  | Equiv of formula * formula
  | Imply of formula * formula
  | And of formula * formula
  | Or  of formula * formula
  | Not of formula

type qformula =
  | QFFormula of formula
  | Exists of vname * var_ty * qformula

type optimization_kind =
  | Minimize of vname
  | Maximize of vname
  | Satisfy

type bab_qformula = {
  qf: qformula;
  optimise: optimization_kind
}

let one = Cst (Bound_rat.one, Int)
let zero = Cst (Bound_rat.zero, Int)
let two  = Cst (Bound_rat.two, Int)

let truef = Cmp (zero, LEQ, zero)
let falsef = Cmp (one, LEQ, zero)

let rec has_variable = function
  | Funcall(_, args) -> List.exists has_variable args
  | Poly (_, l) -> List.exists has_variable l
  | Var _ -> true
  | Cst _ -> false

let rec count_variable = function
  | Funcall(_, args) -> List.fold_left (fun a b -> a+(count_variable b)) 0 args
  | Poly (_, l) -> List.fold_left (fun a b -> a+(count_variable b)) 0 l
  | Var _ -> 1
  | Cst _ -> 0


let rec is_linear = function
  | Poly(MUL, l) | Poly(DIV, l)
    -> count_variable (Poly(MUL,l)) <= 1 && List.for_all is_linear l
  | Poly(POW, l) -> not (has_variable (Poly(POW, l)))
  | Poly(_, l) -> List.for_all is_linear l
  | Var _ | Cst _ -> true
  | _ -> false

let rec is_cons_linear = function
  | Cmp (e1,_,e2) -> is_linear e1 && is_linear e2
  | FVar _ -> true
  | Equiv (b1,b2)
  | Imply (b1,b2)
  | And (b1,b2)
  | Or (b1,b2) -> is_cons_linear b1 && is_cons_linear b2
  | Not b -> is_cons_linear b

let is_cst = function
  | Cst _ -> true
  | _ -> false

let type_dispatch (module B: Bound_sig.S) from ty f =
  match ty with
  | (Concrete ty) when ty=B.concrete_ty -> f ()
  | (Abstract ty) when
      (less_precise_than ty B.abstract_ty) = Kleene.True -> f ()
  | ty -> raise (Wrong_modelling (
      from ^ "(" ^ (string_of_aty B.abstract_ty) ^ ") does not support " ^
      (string_of_ty ty)))
