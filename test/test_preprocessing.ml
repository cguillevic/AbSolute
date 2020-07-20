(* Copyright 2020 Corentin Guillevic

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

open Lang.Ast
open Preprocessing.Nast

let rec syntax_is_equals_expr a b =
  match (a, b) with
  | (Var _, Var _) -> a = b
  | (Cst _, Cst _) -> a = b
  | (Binary (la, opa, ra), Binary (lb, opb, rb)) -> opa = opb && syntax_is_equals_expr la lb && syntax_is_equals_expr ra rb
  | (Unary (opa, ra), Unary (opb, rb)) -> opa = opb && syntax_is_equals_expr ra rb
  | (Funcall (na, la), Funcall (nb, lb)) -> na = nb && equals_list la lb
  | _ -> false
and equals_list a b =
  match (a, b) with
  | ([], []) -> true
  | (ha::ta, hb::tb) -> syntax_is_equals_expr ha hb && equals_list ta tb
  | _ -> false  
  
let rec syntax_is_equals_nexpr a b = 
  match (a, b) with
  | (NVar _, NVar _) -> a = b
  | (NCst _, NCst _) -> a = b
  | (NFuncall (na, la), NFuncall (nb, lb)) -> na = nb && equals_list la lb
  | _ -> false
and equals_list a b =
  match (a, b) with
  | ([], []) -> true
  | (ha::ta, hb::tb) -> syntax_is_equals_nexpr ha hb && equals_list ta tb
  | _ -> false  

let test_expr_of_nexpr_e1 () =
  let nexpr = NFuncall (FMUL, [NVar "x" ; nexpr_of_int 2 ; nexpr_of_int 4 ; nexpr_of_int 8]) in
  let expr_res = Binary (Binary (Binary (Var "x", MUL, expr_of_int 2), MUL, expr_of_int 4), MUL, expr_of_int 8) in 
  syntax_is_equals_expr expr_res (expr_of_nexpr nexpr)
  
let test_nexpr_of_expr_e1 () =
  let nexpr_res = NFuncall (FMUL, [NVar "x" ; nexpr_of_int 2 ; nexpr_of_int 4 ; nexpr_of_int 8]) in
  let expr = Binary (Binary (Binary (Var "x", MUL, expr_of_int 2), MUL, expr_of_int 4), MUL, expr_of_int 8) in 
  syntax_is_equals_nexpr nexpr_res (nexpr_of_expr expr)
  
let test_expr_of_nexpr_e2 () =
  let nexpr = NFuncall (FDIV, [NVar "x" ; nexpr_of_int 2 ; NFuncall (FDIV, [nexpr_of_int 3 ; nexpr_of_int 4])]) in
  let expr_res = Binary (Binary (Var "x", DIV, expr_of_int 2), DIV, Binary (expr_of_int 3, DIV, expr_of_int 4)) in 
  syntax_is_equals_expr expr_res (expr_of_nexpr nexpr)
  
let test_nexpr_of_expr_e2 () =
  let nexpr_res = NFuncall (FDIV, [NVar "x" ; nexpr_of_int 2 ; NFuncall (FDIV, [nexpr_of_int 3 ; nexpr_of_int 4])]) in
  let expr = Binary (Binary (Var "x", DIV, expr_of_int 2), DIV, Binary (expr_of_int 3, DIV, expr_of_int 4)) in 
  syntax_is_equals_nexpr nexpr_res (nexpr_of_expr expr)
  
let test_expr_of_nexpr_e3 () =
  let nexpr = NFuncall (FADD, [NVar "x" ; nexpr_of_int 2 ; NFuncall (FDIV, [nexpr_of_int 3 ; nexpr_of_int 4 ; nexpr_of_int 5]) ; NVar "y"]) in
  let expr_res = Binary (Binary (Binary (Var "x", ADD, expr_of_int 2), ADD, Binary (Binary (expr_of_int 3, DIV, expr_of_int 4), DIV, expr_of_int 5)), ADD, Var "y") in
  syntax_is_equals_expr expr_res (expr_of_nexpr nexpr)
  
let test_nexpr_of_expr_e3 () =
  let nexpr_res = NFuncall (FADD, [NVar "x" ; nexpr_of_int 2 ; NFuncall (FDIV, [nexpr_of_int 3 ; nexpr_of_int 4 ; nexpr_of_int 5]) ; NVar "y"]) in
  let expr = Binary (Binary (Binary (Var "x", ADD, expr_of_int 2), ADD, Binary (Binary (expr_of_int 3, DIV, expr_of_int 4), DIV, expr_of_int 5)), ADD, Var "y") in
  syntax_is_equals_nexpr nexpr_res (nexpr_of_expr expr)
  
let test_expr_of_nexpr_e4 () =
  let nexpr = NFuncall (FSUB, [nexpr_of_int 8 ; NFuncall (FMUL, [nexpr_of_int 3 ; NVar "x"]) ; nexpr_of_int 4]) in
  let expr_res = Binary (Binary (expr_of_int 8, SUB, Binary (expr_of_int 3, MUL, Var "x")), SUB, expr_of_int 4) in
  syntax_is_equals_expr expr_res (expr_of_nexpr nexpr)
  
let test_nexpr_of_expr_e4 () =
  let nexpr_res = NFuncall (FSUB, [nexpr_of_int 8 ; NFuncall (FMUL, [nexpr_of_int 3 ; NVar "x"]) ; nexpr_of_int 4]) in
  let expr = Binary (Binary (expr_of_int 8, SUB, Binary (expr_of_int 3, MUL, Var "x")), SUB, expr_of_int 4) in
  syntax_is_equals_nexpr nexpr_res (nexpr_of_expr expr)  

let test_simplify_e1 () =
  let e = NFuncall (FNEG, [NFuncall (FNEG, [NFuncall (FNEG, [nexpr_of_int 2])])]) in
  let res = NFuncall (FNEG, [nexpr_of_int 2]) in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

let test_simplify_e2 () =
  let e = NFuncall (FSUB, [nexpr_of_int 0 ; nexpr_of_int 2 ; nexpr_of_int 3 ; nexpr_of_int 4]) in
  let res = NFuncall(FNEG, [NFuncall (FADD, [nexpr_of_int 2 ; nexpr_of_int 3 ; nexpr_of_int 4])]) in  
  syntax_is_equals_nexpr res (simplify_nexpr e) 

let test_simplify_e3 () =
  let e = NFuncall (FSUB, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 0 ; nexpr_of_int 2 ; nexpr_of_int 0]) in
  let res = NFuncall (FSUB, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 2]) in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

let test_simplify_e4 () =
  let e = NFuncall (FADD, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 0 ; nexpr_of_int 2 ; nexpr_of_int 0]) in
  let res = NFuncall (FADD, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 2]) in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

let test_simplify_e5 () =
  let e = NFuncall (FMUL, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 1 ; nexpr_of_int 2 ; nexpr_of_int 1]) in
  let res = NFuncall (FMUL, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 2]) in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

  let test_simplify_e6 () =
  let e = NFuncall (FMUL, [nexpr_of_int 8 ; nexpr_of_int 0 ; nexpr_of_int 3; nexpr_of_int 2]) in
  let res = nexpr_of_int 0 in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

let test_simplify_e7 () =
  let e = NFuncall (FDIV, [nexpr_of_int 0 ; nexpr_of_int 4 ; nexpr_of_int 1 ; nexpr_of_int 2 ; nexpr_of_int 1]) in
  let res = nexpr_of_int 0 in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

let test_simplify_e8 () =
  let e = NFuncall (FDIV, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 1 ; nexpr_of_int 2]) in
  let res = NFuncall (FDIV, [nexpr_of_int 8 ; nexpr_of_int 4 ; nexpr_of_int 2]) in
  syntax_is_equals_nexpr res (simplify_nexpr e)  

let test_simplify_e9 () =
  let e = NFuncall (FPOW, [nexpr_of_int 1 ; nexpr_of_int 2 ; nexpr_of_int 4]) in
  let res = nexpr_of_int 1 in
  syntax_is_equals_nexpr res (simplify_nexpr e)   

let test_simplify_e10 () =
  let e = NFuncall (FPOW, [nexpr_of_int 8 ; nexpr_of_int 2 ; nexpr_of_int 0 ; nexpr_of_int 6]) in
  let res = nexpr_of_int 1 in
  syntax_is_equals_nexpr res (simplify_nexpr e)   

let test_simplify_e11 () =
  let e = NFuncall (FPOW, [nexpr_of_int 0 ; nexpr_of_int 2 ; nexpr_of_int 4]) in
  let res = nexpr_of_int 0 in
  syntax_is_equals_nexpr res (simplify_nexpr e)     

let test_equals_e1 () =
  let a = NFuncall (FADD, [NFuncall (FMUL, [nexpr_of_int 2 ; NFuncall (FADD, [NVar "x" ; NFuncall (FMUL, [nexpr_of_int 2 ; nexpr_of_int 0])])]) ; NFuncall (FDIV, [nexpr_of_int 8 ; nexpr_of_int 3])]) in
  (* a = 2*(x+2*0)+8/3  *)
  let b = NFuncall (FADD, [NFuncall (FMUL, [nexpr_of_int 2 ; NVar "x"]) ; NFuncall (FDIV, [NFuncall (FMUL, [nexpr_of_int 8 ; NFuncall (FPOW, [nexpr_of_int 10 ; nexpr_of_int 2 ; nexpr_of_int 0])]) ; NFuncall (FNEG, [NFuncall (FNEG, [nexpr_of_int 3])])])]) in
  (* b = 2*x + (8*10^2^0)/(--3) 
     a = 2*x + 8/3 = b
  *)
  is_equal_nexpr a b


let apply_test test () = Alcotest.(check bool) "test_expr_of_nexpr" true (test ())

let tests = [
  "expr_of_nexpr 1", `Quick, (apply_test test_expr_of_nexpr_e1);
  "expr_of_nexpr 2", `Quick, (apply_test test_expr_of_nexpr_e2);
  "expr_of_nexpr 3", `Quick, (apply_test test_expr_of_nexpr_e3);
  "expr_of_nexpr 4", `Quick, (apply_test test_expr_of_nexpr_e4);

  "nexpr_of_expr 1", `Quick, (apply_test test_nexpr_of_expr_e1);
  "nexpr_of_expr 2", `Quick, (apply_test test_nexpr_of_expr_e2);
  "nexpr_of_expr 3", `Quick, (apply_test test_nexpr_of_expr_e3);
  "nexpr_of_expr 4", `Quick, (apply_test test_nexpr_of_expr_e4);

  "simplify 1", `Quick, (apply_test test_simplify_e1);
  "simplify 2", `Quick, (apply_test test_simplify_e2);
  "simplify 3", `Quick, (apply_test test_simplify_e3);
  "simplify 4", `Quick, (apply_test test_simplify_e4);
  "simplify 5", `Quick, (apply_test test_simplify_e5);
  "simplify 6", `Quick, (apply_test test_simplify_e6);
  "simplify 7", `Quick, (apply_test test_simplify_e7);
  "simplify 8", `Quick, (apply_test test_simplify_e8);
  "simplify 9", `Quick, (apply_test test_simplify_e6);
  "simplify 10", `Quick, (apply_test test_simplify_e7);
  "simplify 11", `Quick, (apply_test test_simplify_e8);


  "equals 1", `Quick, (apply_test test_equals_e1);
]