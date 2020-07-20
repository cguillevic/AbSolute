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

type fun_symbol = FADD | FSUB | FMUL | FDIV | FPOW | FNEG | COS | SIN

type fun_arity = FUnary | FBinary | FNary

type nexpr =  
  | NFuncall of fun_symbol * nexpr list
  | NVar     of vname
  | NCst     of i * var_concrete_ty

let is_commutative = (function
  | FADD | FMUL -> true
  | _ -> false)

let is_commutative_binop = (function
  | ADD | MUL -> true
  | _ -> false)

let funcall_arity = (function
  | FADD | FSUB | FMUL | FDIV | FPOW -> FNary
  | _ -> FUnary)

let fun_symbol_to_str = (function
  | COS -> "COS"
  | SIN -> "SIN"
  | _ -> failwith "not compatible")

let str_to_fun_symbol = (function
  | "COS" -> COS
  | "SIN" -> SIN
  | _ -> failwith "not compatible")

let fun_symbol_to_binop = (function
  | FADD -> ADD
  | FSUB -> SUB
  | FMUL -> MUL
  | FDIV -> DIV
  | FPOW -> POW
  | _ -> failwith "not compatible")

let binop_to_fun_symbol = (function
  | ADD -> FADD 
  | SUB -> FSUB
  | MUL -> FMUL
  | DIV -> FDIV
  | POW -> FPOW)

let rec expr_of_nexpr = function
    | NVar x -> Var x
    | NCst (a, b) -> Cst (a, b)
    | NFuncall (_, []) -> failwith "empty list"
    | NFuncall (f, l) when funcall_arity f = FUnary -> (
        match (f, l) with
        | (FNEG, [e]) -> Unary(NEG, (expr_of_nexpr e))
        | _ -> Funcall (fun_symbol_to_str f, List.map expr_of_nexpr l)
        )

    | NFuncall (f, l) when funcall_arity f = FBinary -> (
    	match (f, l) with
        | (_, [_]) -> failwith "2 expected items"
        | _ -> Funcall (fun_symbol_to_str f, List.map expr_of_nexpr l)
        )
    | NFuncall (f, l) when funcall_arity f = FNary -> expr_of_nary (false, f, l)
    | NFuncall _ -> failwith "Unknown arity"
and expr_of_nary = function
    | (false, op, l) -> expr_of_nary (true, op, List.rev l)
    | (_, _, [e]) -> expr_of_nexpr e
    | (_, _, []) -> failwith "empty list"
    | (true, op, l) -> Binary (expr_of_nary (true, op, List.tl l), fun_symbol_to_binop op, (expr_of_nexpr (List.hd l)))


(** Create a list of terms from binary expression *)
let rec create_list op expr = 
  match expr with
  | Binary (a, binop, b) when op = binop && is_commutative_binop op -> (create_list op a) @ (create_list op b)
  | Binary (a, binop, b) when op = binop -> (create_list op a) @ [b]
  | _ -> [expr]
  
let rec nexpr_of_expr expr = 
  match expr with
  | Funcall (name, l) -> NFuncall (str_to_fun_symbol name, (List.map nexpr_of_expr l)) 
  | Var x -> NVar x
  | Cst (a, b) -> NCst (a, b)
  | Unary (NEG, e) -> NFuncall (FNEG, [nexpr_of_expr e])
  | Binary (_, op, _) -> let l = create_list op expr in NFuncall (binop_to_fun_symbol op, List.map nexpr_of_expr l)

let equals_constants a b = 
  match (a,b) with 
  | (NCst(ia,_), NCst(ib, _)) -> Bound_rat.equal ia ib
  | _ -> false 

let nexpr_of_int i = NCst (Bound_rat.of_int i, Int)

let expr_of_int i = Cst (Bound_rat.of_int i, Int)

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
  | FADD -> nexpr_of_zero
  | FSUB -> nexpr_of_zero
  | FDIV -> nexpr_of_int 1
  | FMUL -> nexpr_of_int 1
  | FPOW -> nexpr_of_int 1
  | _ -> failwith "Unknown neutral element"

let rec simplify_nexpr nexpr =
  match nexpr with
  | NCst _ as cst -> cst
  | NVar x -> NVar x 
  | NFuncall (_, []) -> failwith "empty list"
  | NFuncall (FNEG, [NFuncall(FNEG, [e])]) -> simplify_nexpr e
  | NFuncall (FNEG, [e]) -> NFuncall (FNEG, [simplify_nexpr e])
  | NFuncall (f, [e]) when funcall_arity f <> FUnary -> simplify_nexpr e
  | NFuncall (FSUB, h::t) when is_zero h -> NFuncall (FNEG, [simplify_nexpr (NFuncall (FADD, t))])
  | NFuncall (f, l) when funcall_arity f = FNary -> simplify_nary f l
  | NFuncall (n, l) -> NFuncall (n, (List.map simplify_nexpr l))
and simplify_nary op l =
    let simplified_list =
      match op with
      | FADD|FSUB -> delete_constant_in_nexpr_list (neutral_element op) (List.map simplify_nexpr l)
      | FMUL ->
          let nl = List.map simplify_nexpr l in 
            if List.exists is_zero nl then [nexpr_of_zero] 
            else delete_constant_in_nexpr_list (neutral_element op) nl
      | FDIV ->
          let nl = List.map simplify_nexpr l in 
          (*if List.exists is_zero (List.tl nl) then not_a_number else*)
            if is_zero (List.hd nl) then [nexpr_of_zero] 
            else ((List.hd nl)::(delete_constant_in_nexpr_list (neutral_element op) (List.tl nl)))
      | FPOW ->
          let nl = List.map simplify_nexpr l in 
            let ntl = delete_constant_in_nexpr_list (neutral_element op) (List.tl nl) in
              if is_one (List.hd nl) || List.exists is_zero ntl then [nexpr_of_int 1]
              else if is_zero (List.hd nl) then [nexpr_of_zero]
              else (List.hd nl)::ntl
      | _ -> l
    in 
      if List.length simplified_list = 0 then neutral_element op
      else if List.length simplified_list = 1 then List.hd simplified_list
      else NFuncall (op, simplified_list)  

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

let compare_fop a b =
  match (a, b) with
  | (a, b) when a = b -> 0
  | (FPOW, _) -> 1
  | (FMUL, (FDIV|FADD|FSUB|FNEG|COS|SIN)) -> 1
  | (FDIV, (FADD|FSUB|FNEG|COS|SIN)) -> 1
  | (FADD, (FSUB|FNEG|COS|SIN)) -> 1
  | (FSUB, (FNEG|COS|SIN)) -> 1
  | (FNEG, (COS|SIN)) -> 1
  | (COS, SIN) -> 1
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
          let compare_n = compare_fop na nb in
            let compare_length = compare (List.length la) (List.length lb) in
              if compare_n <> 0 then compare_n 
              else if compare_length <> 0 then compare_length
              else equals_list la lb
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
  | NFuncall (f, l) when is_commutative f -> NFuncall (f , List.sort compare_nexpr (List.map sort_nexpr l))
  | NFuncall (f, l) -> NFuncall (f, (List.map sort_nexpr l))

let is_equal_nexpr a b =
  let na = sort_nexpr (simplify_nexpr a) in
  let nb = sort_nexpr (simplify_nexpr b) in
  if compare_nexpr na nb = 0 then true
  else false