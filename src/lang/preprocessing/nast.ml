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
open Bounds

type nexpr =  
  | NFuncall of string * nexpr list
  | NVar     of vname
  | NCst     of i * var_concrete_ty
  | NUnary   of unop * nexpr
  | Nary     of binop * nexpr list  

let is_commutative = function
  | ADD | MUL -> true
  | SUB | DIV | POW -> false

let rec expr_of_nexpr = function
    | NFuncall (name, l) -> Funcall (name, (List.map expr_of_nexpr l))
    | NVar x -> Var x
    | NCst (a, b) -> Cst (a, b)
    | NUnary (NEG, e) -> Unary(NEG, (expr_of_nexpr e))
    | Nary (_, [e]) -> expr_of_nexpr e    
    | Nary (_, []) -> failwith "empty list"
    | Nary (op, l) -> expr_of_nary (false, op, l)
and expr_of_nary = function
    | (false, op, l) -> expr_of_nary (true, op, List.rev l)
    | (_, _, [e]) -> expr_of_nexpr e
    | (_, _, []) -> failwith "empty list"
    | (true, op, l) -> Binary (expr_of_nexpr (Nary (op, (List.tl l))), op, (expr_of_nexpr (List.hd l)))


(** Create a list of terms from binary expression *)
let rec create_list op expr = 
  match expr with
  | Binary (a, binop, b) when op = binop && is_commutative op -> (create_list op a) @ (create_list op b)
  | Binary (a, binop, b) when op = binop -> (create_list op a) @ [b]
  | _ -> [expr]
  
let rec nexpr_of_expr expr = 
  match expr with
  | Funcall (name, l) -> NFuncall (name, (List.map nexpr_of_expr l)) 
  | Var x -> NVar x
  | Cst (a, b) -> NCst (a, b)
  | Unary (NEG, e) -> NUnary (NEG, nexpr_of_expr e)
  | Binary (_, op, _) -> let l = create_list op expr in Nary (op, List.map nexpr_of_expr l)

let equals_constants a b = 
  match (a,b) with 
  | (NCst(ia,_), NCst(ib, _)) -> Bound_rat.equal ia ib
  | _ -> false 

let nexpr_of_int i = NCst (Bound_rat.of_int i, Int)

let nexpr_of_zero = NCst (Bound_rat.zero, Int)

let is_zero c = equals_constants nexpr_of_zero c

let is_one c = equals_constants (nexpr_of_int 1) c

(* Delete all occurences of the constant in nexpr_list *)
let delete_constant_in_nexpr_list constant nexpr_list =
  let f a = not (equals_constants a constant) in
  List.filter f nexpr_list  

(* Return neutral element of operation *)
let neutral_element op = 
 match op with
  |ADD -> nexpr_of_zero
  |SUB -> nexpr_of_zero
  |DIV -> nexpr_of_int 1
  |MUL -> nexpr_of_int 1
  |POW -> nexpr_of_int 1

let rec simplify_nexpr nexpr =
  match nexpr with
  | NFuncall (n, l) -> NFuncall (n, (List.map simplify_nexpr l))
  | NCst _ as cst -> cst
  | NVar x -> NVar x 
  | NUnary (NEG, NUnary(NEG, e)) -> simplify_nexpr e
  | NUnary (NEG, e) -> NUnary (NEG, simplify_nexpr e)
  | Nary (_, [e]) -> simplify_nexpr e
  | Nary (SUB, h::t) when is_zero h -> NUnary (NEG, simplify_nexpr (Nary (ADD, t)))
  | Nary (op, l) -> simplify_nary op l
and simplify_nary op l =
    let simplified_list =
      match op with
      | ADD|SUB -> delete_constant_in_nexpr_list (neutral_element op) (List.map simplify_nexpr l)
      | MUL ->
          let nl = List.map simplify_nexpr l in 
            if List.exists is_zero nl then [nexpr_of_zero] 
            else delete_constant_in_nexpr_list (neutral_element op) nl
      | DIV ->
          let nl = List.map simplify_nexpr l in 
            if is_zero (List.hd nl) then [nexpr_of_zero] 
          (*else if List.exists is_zero (List.tl nl) then not_a_number*)
            else ((List.hd nl)::(delete_constant_in_nexpr_list (neutral_element op) (List.tl nl)))
      | POW ->
          let nl = List.map simplify_nexpr l in 
            let ntl = delete_constant_in_nexpr_list (neutral_element op) (List.tl nl) in
              if is_one (List.hd nl) || List.exists is_zero ntl then [nexpr_of_int 1]
              else if is_zero (List.hd nl) then [nexpr_of_zero]
              else (List.hd nl)::ntl
    in 
      if List.length simplified_list = 0 then neutral_element op
      else if List.length simplified_list = 1 then List.hd simplified_list
      else Nary (op, simplified_list)  

let compare_ncst a b = 
  match (a,b) with    
  | (NCst (ia, ta), NCst (ib, tb)) -> (
      match (ta, tb) with
      | (a,b) when a = b -> Bound_rat.compare ia ib
      | (Real, _) -> 1
      | _ -> -1
      )
  | _ -> failwith "a or b is not a constant"

let compare_var a b =
  match (a, b) with 
  | (NVar va, NVar vb) -> String.compare va vb
  | _ -> failwith "a or b is not a variable" 

let compare_binop a b =
  match (a, b) with
  | (a, b) when a = b -> 0
  | (POW, _) -> 1
  | (MUL, (DIV|ADD|SUB)) -> 1
  | (DIV, (ADD|SUB)) -> 1
  | (ADD, SUB) -> 1
  | _ -> -1 

let compare_unop a b =
  match (a, b) with
  | (a, b) when a = b -> 0
  | _ -> -1   	

let rec compare_nexpr a b =
  match a with
  | NCst _ -> (
      match b with
      | NCst _ -> compare_ncst a b
      | _ -> -1
      )
  | NVar _ -> (
      match b with
      | NCst _ -> -1
      | NVar _ -> compare_var a b
      | _ -> -1
      )
  | NFuncall (na, la) -> (
      match b with
      | NCst _ | NVar _ -> 1
      | NFuncall (nb, lb) ->
          let compare_n = String.compare na nb in
            let compare_length = compare (List.length la) (List.length lb) in
              if compare_n <> 0 then compare_n 
              else if compare_length <> 0 then compare_length
              else equals_list la lb
      | _ -> -1
      )
  | NUnary (opa, ea) -> (
      match b with
      | NCst _ | NVar _ | NFuncall _ -> 1
      | NUnary (opb, eb) ->
          let comp_op = compare_unop opa opb in
          if  comp_op = 0 then comp_op
          else compare_nexpr ea eb
      | _ -> -1 
      )
  | Nary (opa, la) -> (
      match b with
      | NCst _ | NVar _ | NFuncall _ | NUnary _ -> 1
      | Nary (opb, lb) ->
          let comp_op = compare_binop opa opb in
            if comp_op = 0 then
              let compare_length = compare (List.length la) (List.length lb) in
                if compare_length <> 0 then compare_length
                else equals_list la lb
            else comp_op
      )
and equals_list la lb =
    match (la, lb) with
    |([],[]) -> 0
    |(ha::ta , hb::tb) ->
        let compare_h = compare_nexpr ha hb in
          if compare_h <> 0 then compare_h
          else equals_list ta tb 
    |_ -> raise (Invalid_argument "lists's length is not compatible")

(** Sort the commutatives terms of nexpr *)
let rec sort_nexpr nexpr =
  match nexpr with
  | NCst _ | NVar _ -> nexpr
  | NFuncall (n, l) -> NFuncall (n, (List.map sort_nexpr l))
  | NUnary (op, e) -> NUnary (op, sort_nexpr e)
  | Nary (op, l) when is_commutative op -> Nary (op , List.sort compare_nexpr (List.map sort_nexpr l))
  | Nary (op, l) -> let nl = (List.hd l)::(List.sort compare_nexpr (List.tl l)) in Nary (op, List.map sort_nexpr nl) 

let is_equal_nexpr a b =
  let na = sort_nexpr (simplify_nexpr a) in
  let nb = sort_nexpr (simplify_nexpr b) in
  if compare_nexpr na nb = 0 then true
  else false