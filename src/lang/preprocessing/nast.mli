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

type fun_symbol = FADD | FSUB | FMUL | FDIV | FPOW | FNEG | COS | SIN

type nexpr =  
  | NFuncall of fun_symbol * nexpr list
  | NVar     of vname
  | NCst     of i * var_concrete_ty

(** Convert an integer in a nexpr*)
val nexpr_of_int : int -> nexpr  

(** Convert an integer in a expr*)
val expr_of_int : int -> expr  

(** Convert a nexpr in a expr *)
val expr_of_nexpr : nexpr -> expr

(** Convert a expr in a nexpr *)
val nexpr_of_expr : expr -> nexpr

(** Simplify a nexpr
Simplifications applied :
--x = x
0-x-y = -(x+y)
x+y+0+z = x+y+z
x-y-0-z = x-y-z
x*y*1*z = x*y*z
x*y*0*z = 0
0/x/y (with x <> 0 && y <> 0) = 0
x/y/1/z = x/y/z
1^x^y = 1
1^x^0^y = 1
0^x^y (with x <> 0 and y <> 0) = 0
 *)
val simplify_nexpr : nexpr -> nexpr

(** Compare 2 nexpr *)
val compare_nexpr : nexpr -> nexpr -> int

(** Test if the 2 nexpr are equals *)
val is_equal_nexpr : nexpr -> nexpr -> bool