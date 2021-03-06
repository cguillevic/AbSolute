(* Copyright 2019 Pierre Talbot

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

open Core
open Lang
open Lang.Ast
open Typing.Tast
open Bounds
open Dbm
open Domains.Interpretation

let rec normalize_expr e =
  let neg e = Unary (NEG, e) in
  match e with
  | Unary (NEG, Cst(c,a)) -> Cst (Bound_rat.neg c, a)
  | Unary (NEG, Unary (NEG, e)) -> normalize_expr e
  | Unary (NEG, Binary (x, SUB, y)) -> normalize_expr (Binary (neg x, ADD, y))
  | Unary (NEG, Binary (x, ADD, y)) -> normalize_expr (Binary (neg x, SUB, y))
  | Unary (op, x) -> Unary(op, normalize_expr x)
  | Binary (x, SUB, Unary (NEG, y)) -> normalize_expr (Binary (x, ADD, y))
  | Binary (x, ADD, Unary (NEG, y)) -> normalize_expr (Binary (x, SUB, y))
  | Binary (x, op, y) -> Binary (normalize_expr x, op, normalize_expr y)
  | e -> e

let normalize (e1, op, e2) = ((normalize_expr e1), op, (normalize_expr e2))

module type Octagon_interpretation_sig =
sig
  module B: Bound_sig.S
  type rconstraint = B.t dbm_constraint
  include module type of (Interpretation_ground(struct type var_id=dbm_var end))

  val exact_interpretation: bool
  val interpret: t -> approx_kind -> tformula -> t * rconstraint list
  val to_qformula: t -> rconstraint list -> tqformula
  val negate: rconstraint -> rconstraint
end

module Octagon_interpretation(B: Bound_sig.S) =
struct
  module B = B
  module IG = Interpretation_ground(struct type var_id=dbm_var end)
  include IG
  type rconstraint = B.t dbm_constraint

  let exact_interpretation = not (Types.is_continuous B.abstract_ty)

  let dim_of_var repr v =
    let (v,_) = to_abstract_var repr v in
    let k1, k2 = (v.l / 2), (v.c / 2) in
    if k1 <> k2 then failwith "Octagon_interpretation.dim_of_var: only variable with a canonical plane are defined on a single dimension."
    else k1

  (** If the bound is discrete, it reformulates strict inequalities `<` into the inequality `<=` (dual `>` is handled by `generic_rewrite`).
      It is not an over-approximation because the rewritten constraint is logically equivalent to the initial constraint.
      For example, it rewrites `x - y < d` into `x - y <= d - 1`. *)
  let reformulate c =
    if Types.is_continuous B.abstract_ty then c
    else
      match c with
      | e1, LT, Cst (d, a) -> normalize (e1, LEQ, Cst (Bound_rat.sub_up d Bound_rat.one, a))
      | c -> c

  (** `x <= d` ~> `x + x <= 2d` *)
  let x_leq_d x c = {v=make_var (x+1) x; d=(B.mul_up c B.two)}

  (** `-x <= d` ~> `-x - x <= 2d` *)
  let minus_x_leq_d x c = {v=make_var x (x+1); d=(B.mul_up c B.two)}

  (* NOTE: we invert `x` and `y` because dbm_var is defined as {x; y} where `x` is the line and `y` the column.
     In an expression such as `X - Y <= 10`, `X` is the column and `Y` the line. *)

  (** `x + y <= d` *)
  let x_plus_y_leq_d x y d = {v=make_var (y+1) x; d=d}

  (** `x - y <= d` *)
  let x_minus_y_leq_d x y d = {v=make_var y x; d=d}

  (** `-x + y <= d` *)
  let minus_x_plus_y_leq_d x y d = {v=make_var (y+1) (x+1); d=d}

  (** `-x - y <= d` *)
  let minus_x_minus_y_leq_d x y d = {v=make_var y (x+1); d=d}

  let map_to_dim r f x d = f ((dim_of_var r x)*2) (B.of_rat_up d)
  let map2_to_dim r f x y d =
    f ((dim_of_var r x)*2) ((dim_of_var r y)*2) (B.of_rat_up d)

  (* Try interpreting exactly an octagonal constraint from a normalized form.
     The constraint should be processed by `generic_rewrite` first. *)
  let try_create r = function
    | Var x, LEQ, Cst (d, _) -> Some (map_to_dim r x_leq_d x d)
    | Unary (NEG, Var x), LEQ, Cst (d, _) -> Some (map_to_dim r minus_x_leq_d x d)
    | Binary (Var x, ADD, Var y), LEQ, Cst (d, _) -> Some (map2_to_dim r x_plus_y_leq_d x y d)
    | Binary (Var x, SUB, Var y), LEQ, Cst (d, _) -> Some (map2_to_dim r x_minus_y_leq_d x y d)
    | Binary (Unary (NEG, Var x), ADD, Var y), LEQ, Cst (d, _) -> Some (map2_to_dim r minus_x_plus_y_leq_d x y d)
    | Binary (Unary (NEG, Var x), SUB, Var y), LEQ, Cst (d, _) -> Some (map2_to_dim r minus_x_minus_y_leq_d x y d)
    | _ -> None

  let rec generic_rewrite c =
    match normalize c with
    | e1, EQ, e2 -> (generic_rewrite (e1, LEQ, e2))@(generic_rewrite (e1, GEQ, e2))
    | e1, GEQ, e2 -> generic_rewrite (Unary (NEG, e1), LEQ, Unary (NEG, e2))
    | e1, GT, e2 -> generic_rewrite (Unary (NEG, e1), LT, Unary (NEG, e2))
    | Var x, op, Var y -> generic_rewrite (Binary (Var x, SUB, Var y), op, Cst (Bound_rat.zero, B.concrete_ty))
    | Unary (NEG, Var x), op, Var y ->
        generic_rewrite (Binary (Unary (NEG, Var x), SUB, Var y), op, Cst (Bound_rat.zero, B.concrete_ty))
    | Var x, op, Unary (NEG, Var y) ->
        generic_rewrite (Binary (Var x, ADD, Var y), op, Cst (Bound_rat.zero, B.concrete_ty))
    | Unary (NEG, Var x), op, Unary (NEG, Var y) ->
        generic_rewrite (Binary (Unary (NEG, Var x), ADD, Var y), op, Cst (Bound_rat.zero, B.concrete_ty))
    | c -> [c]

  let unwrap_all constraints =
    if List.for_all Tools.is_some constraints then
      List.map Tools.unwrap constraints
    else []

  let cannot_interpret approx c =
    raise (Wrong_modelling
      ("Cannot interpret the formula " ^ (Pretty_print.string_of_constraint c)
     ^ " with an " ^ approx ^ "approximation in the octagon domain."))

  let interpret_one_exact from repr c =
    let oc =
      generic_rewrite c |>
      List.map (fun c -> try_create repr (reformulate c)) |>
      unwrap_all in
    match oc with
    | [] -> cannot_interpret from c
    | oc -> oc

  let interpret_one_over_approx repr c =
    List.flatten (List.map (fun c ->
      match c with
      | e1, LT, e2 -> interpret_one_exact "over-" repr (e1, LEQ, e2)
      | _ -> cannot_interpret "over-" c
    ) (generic_rewrite c))

  let interpret_one_under_approx repr c =
    List.flatten (List.map (fun c ->
      match c with
      (* transform `d` into `w` where `w` is the first floating point number coming before `d`.
         It means that solutions between `w` and `d` are possibly lost. *)
      | e1, LT, Cst (d, Real) ->
          let w = Bound_float.of_rat_up d in
          let w = Float.pred w in
          let w = Cst (Bound_rat.of_float w, Real) in
          interpret_one_exact "under-" repr (e1, LEQ, w)
      | _ -> cannot_interpret "under-" c
    ) (generic_rewrite c))

  let interpret_one approx repr c =
    try
      interpret_one_exact "exact " repr c
    with Wrong_modelling msg ->
      match approx with
      | Exact -> raise (Wrong_modelling msg)
      | UnderApprox -> interpret_one_under_approx repr c
      | OverApprox -> interpret_one_over_approx repr c

  (* let c = ref 0 *)

  let interpret repr approx tf =
    (* let _ = Printf.printf "Interpreted %d constraints in Octagon (%s) %s.\n" (c := !c + 1; !c) (string_of_approx approx) (Lang.Pretty_print.string_of_formula (tformula_to_formula tf)); flush_all () in *)
    IG.interpret_gen repr "Octagon" tf (interpret_one approx)

  let negate c =
    if is_rotated c.v then
      { v=(Dbm.inv c.v); d=B.neg (B.succ c.d) }
    else
      { v=(Dbm.inv c.v); d=B.mul_up (B.neg (B.succ (B.div_down c.d B.two))) B.two }

  let ty = B.concrete_ty

  module IV = Interval_view_dbm.Interval_view(B)

  let to_formula_one repr oc =
    let d = B.to_rat oc.d in
    let k1, k2 = oc.v.c / 2, oc.v.l / 2 in
    let x,y = Dbm.make_canonical_var k1, Dbm.make_canonical_var k2 in
    let x, y = to_logic_var repr x, to_logic_var repr y in
    let x, y = x.name, y.name in
    let c =
      if k1 = k2 then
        if oc.v.l > oc.v.c then
          let d = B.to_rat (IV.dbm_to_ub oc.v oc.d) in
          TCmp (Var x, LEQ, Cst (d, ty))
        else
          let d = B.to_rat (IV.dbm_to_lb oc.v (B.neg oc.d)) in
          TCmp (Var x, GEQ, Cst (d, ty))
      else
        let x = if oc.v.c = k1 * 2 then Var x else Unary (NEG, Var x) in
        let y = if oc.v.l = k2 * 2 then Var y else Unary (NEG, Var y) in
        TCmp (Binary (x, SUB, y), LEQ, Cst (d, ty))
    in
      (IG.uid repr, c)

  let to_qformula repr cs = IG.to_qformula_gen repr cs to_formula_one

end
