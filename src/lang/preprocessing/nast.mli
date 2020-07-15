(* Copyright 2020 Corentin Guillevic

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

open Core.Types
open Lang.Ast

type nexpr =  
  | NFuncall of string * nexpr list
  | NVar     of vname
  | NCst     of i * var_concrete_ty
  | NUnary   of unop * nexpr
  | Nary     of binop * nexpr list

(** Convert a nexpr in a expr *)
val expr_of_nexpr : nexpr -> expr

(** Convert a expr in a nexpr *)
val nexpr_of_expr : expr -> nexpr

(** Simplify a nexpr *)
val simplify_nexpr : nexpr -> nexpr

(** Test if the 2 nexpr are equals *)
val is_equal_nexpr : nexpr -> nexpr -> bool