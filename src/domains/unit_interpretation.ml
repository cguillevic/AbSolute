(* Copyright 2019 Pierre Talbot

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

open Typing
open Lang.Ast

type t = unit
type var_id = unit
type rconstraint = unit

let exact_interpretation = true
let empty _ = ()
let to_logic_var _ _ = raise Not_found
let to_abstract_var _ _ = raise Not_found
let local_vars _ _ = raise Not_found
let interpret _ _ _ = raise (Wrong_modelling "`Unit_representation` does not support interpreting constraints.")
let to_qformula _ _ = Tast.ttrue
