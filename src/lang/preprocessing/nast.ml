(*************************************
Structure de données pour 
représentation d'expressions 
arithmétiques N-aires
**************************************)


(*************************************
Types d'ast.ml : remplacer par 
Open Lang.ast
*************************************)
type var_concrete_ty = Int
type vname = string
type i = int (*Bound_rat.t*)
type unop = NEG
type binop = ADD | SUB | MUL | DIV | POW
type expr =
  | Funcall of string * expr list
  | Unary   of unop * expr
  | Binary  of expr * binop * expr
  | Var     of vname
  | Cst     of i * var_concrete_ty

(*************************************
Types 
*************************************)

type nexpr =  
  | NFuncall of string * nexpr list
  | Nary  of binop * nexpr list
  | NVar     of vname
  | NCst     of i * var_concrete_ty

(*************************************
Auxiliaires 
*************************************)

(*Creer une NCst*)
let nexpr_of_int i = NCst(i,Int);;

(*Creer une Cst*)
let expr_of_int i = Cst(i,Int);;

(*Creer une NCst 0*)
let nexpr_of_zero = NCst(0, Int);;

(*Convertit une constante en un entier*)
let int_of_ncst c =
  match c with
  | NCst(a, _) -> a
  | _ -> failwith "not a constant"
;;

(*Teste si x = 0*)
let is_zero x = 
  match x with 
  | NCst(a,_) -> a = 0
  | _ -> false
;;

(*Teste si x = 1*)
let is_one x = 
  match x with 
  | NCst(a,_) -> a = 1
  | _ -> false
;;

(*Teste si deux constantes sont égales*)
let equals_constants a b = (int_of_ncst a) = (int_of_ncst b);; 

(*Teste si a est une constante*)
let is_constant a =
  match a with
  | NCst _ -> true
  | _ -> false
;;


(*Teste si op est une opération commutative*)
let is_commutative op =
  match op with
  | ADD | MUL -> true
  | SUB | DIV | POW -> false
;;

(*Retourne l'expression neutre de l'opération*)
let neutral_element op = 
 match op with
  |ADD -> nexpr_of_zero
  |SUB -> nexpr_of_zero
  |DIV -> nexpr_of_int 1
  |MUL -> nexpr_of_int 1
  |POW -> nexpr_of_int 1
;;

(*Applique une operation a 2 nombres*)
let appliquer_op op a b =
  match op with
  |ADD -> a + b
  |SUB -> a - b
  |DIV -> a / b
  |MUL -> a * b
  |POW -> int_of_float ((float_of_int a)**(float_of_int b))

(*
Calcule une expr composee de constante
Utile pour les tests
*)
let rec calculer_expr expr =
  match expr with
  |Unary (NEG, e) -> - (calculer_expr e)
  |Cst (i, Int) -> i
  |Binary (a, op, b) -> appliquer_op op (calculer_expr a) (calculer_expr b)
  | _ -> failwith "expr non supportee"


(*************************************
Conversion 
*************************************)

(*Convertit une nexpr en une expr*)
let expr_of_nexpr nexpr =
  let rec aux is_revert nexpr =
    match nexpr with
    | NFuncall (name, l) -> Funcall (name, (List.map (aux false) l))
    | NVar x -> Var x
    | NCst (a, b) -> Cst (a, b)
    | Nary (SUB, [e]) -> if is_revert then aux false e else Unary(NEG, (aux false e))
    | Nary (_, [e]) -> (aux false e)    
    | Nary (op, []) -> failwith "empty list"
    | Nary (op, l) -> (
                        if is_revert then Binary ((aux true (Nary (op, (List.tl l)))), op, (aux false (List.hd l))) 
                        else aux true (Nary(op, (List.rev l)))
                      ) 

  in aux false nexpr 
;;

(*Convertit une expr en une nexpr*)
let nexpr_of_expr expr = 
  let rec create_list op expr =
    match expr with
    | Binary(a, binop, b) when binop = op -> (create_list op a) @ (create_list op b)
    | _ -> [expr]
  in
  let rec convert expr =
    match expr with 
    | Funcall (name, l) -> NFuncall (name, (List.map convert l))
    | Var x -> NVar x
    | Cst (a, b) -> NCst (a, b)
    | Unary (NEG, e) -> Nary (SUB, [convert e])
    | Binary (a, op, b) when is_commutative op -> (
                             let nexpr_list = List.map convert ((create_list op a)@(create_list op b)) in
                             Nary (op, nexpr_list)
                           )
    | Binary (a, op, b) -> (
                             let nexpr_list = List.map convert ((create_list op a)@[b]) in
                             Nary (op, nexpr_list)
                           )

  in convert expr
;;

(*************************************
Simplification 
*************************************)

(*Supprime toutes les occurences de la constante de la liste*)
let delete_constant_in_nexpr_list constant nexpr_list =
  let f a = not (is_constant a && equals_constants a constant) in
  List.filter f nexpr_list;;

(*
Simplify a nexpr expression
Simplifications applied :
- --a -> a
- #a (with # equals to + or * or / or ^) -> a
- 0-a-b-c -> - (a+b+c)
- a+b+0+c -> a+b+c
- a-b-0-c -> a-b-c
- a+0+0 -> a
- a-0-0 -> a
- a*1*b -> a*b
- a*0*b -> 0
- a/1/b -> a/b
- 0/a/b -> 0
- a^0^b -> 1
- 1^a^b -> 1
- 0^a^b (with a <> 0 and b <> 0)-> 0
- a^1^b -> a^b
*)
let rec simplify_nexpr nexpr =
  match nexpr with
  | NFuncall (n, l) -> NFuncall (n, (List.map simplify_nexpr l))
  | NCst _ as cst -> cst
  | NVar x -> NVar x 
  | Nary (SUB, [(Nary (SUB, [e]))]) -> simplify_nexpr e
  | Nary (SUB, [e]) -> Nary (SUB, [simplify_nexpr e])
  | Nary (_, [e]) -> simplify_nexpr e
  | Nary (SUB, h::t) when is_zero h -> Nary (SUB, [simplify_nexpr (Nary (ADD, t))])
  | Nary (op, l) -> (
                      let simplified_list =
                      match op with
                      |ADD|SUB -> delete_constant_in_nexpr_list (neutral_element op) (List.map simplify_nexpr l)
                      |MUL -> (
                                 let nl = List.map simplify_nexpr l in 
                                 if List.exists is_zero nl then [nexpr_of_zero] 
                                 else delete_constant_in_nexpr_list (neutral_element op) nl
                              )       
                      |DIV -> (
                                 let nl = List.map simplify_nexpr l in 
                                 if is_zero (List.hd nl) then [nexpr_of_zero] 
                               (*else if List.exists is_zero (List.tl nl) then not_a_number*)
                                 else ((List.hd nl)::(delete_constant_in_nexpr_list (neutral_element op) (List.tl nl)))
                              )
                      |POW -> (
                                 let nl = List.map simplify_nexpr l in 
                                 let ntl = delete_constant_in_nexpr_list (neutral_element op) (List.tl nl) in
                                 if is_one (List.hd nl) || List.exists is_zero ntl then [nexpr_of_int 1]
                                 else if is_zero (List.hd nl) then [nexpr_of_zero]
                                 else (List.hd nl)::ntl
                              )

                                
                      in 
                        if List.length simplified_list = 0 then neutral_element op
                        else if List.length simplified_list = 1 then List.hd simplified_list
                        else Nary (op, simplified_list)
                    )
;;

(*************************************
Jeux d'essai 
*************************************)

let ne1 = Nary(ADD, [nexpr_of_int 1 ; nexpr_of_int 2 ; nexpr_of_int 3]);;
let ne2 = Nary(DIV, [nexpr_of_int 81 ; nexpr_of_int 9 ; nexpr_of_int 3]);;
let ne3 = Nary(MUL, [(Nary(DIV, [(Nary (POW, [nexpr_of_int 2 ; nexpr_of_int 3 ; nexpr_of_int 0 ; nexpr_of_int 4])) ; nexpr_of_int 1])) ; nexpr_of_int 2 ; nexpr_of_int 1 ; nexpr_of_int 3]);;
let ne4 = simplify_nexpr ne3;;

let nr1 = expr_of_nexpr ne1;;
let nr2 = expr_of_nexpr ne2;;

let e1 = Binary(Binary((expr_of_int 100), SUB, (expr_of_int 9)), SUB, (expr_of_int 10));;
let e2 = Binary(Binary((expr_of_int 81), DIV, (expr_of_int 9)), DIV, (expr_of_int 3));;
let e3 = Binary(Binary(e1, DIV, (expr_of_int 9)), DIV, (expr_of_int 3));;
let e4 = Binary(Binary((expr_of_int 8), DIV, (expr_of_int 4)), DIV, Binary((expr_of_int 9), DIV, (expr_of_int 3)));;
let e5 = Binary(expr_of_int 1 , SUB , Binary(expr_of_int 4 , SUB , expr_of_int 2));;
let e6 = Binary(Binary(expr_of_int 1 , SUB , expr_of_int 4) , SUB , expr_of_int 2);;

calculer_expr e3;;

let ne3 = nexpr_of_expr e3;;

let l1 = [nexpr_of_int 1 ; nexpr_of_int 5 ; nexpr_of_int 0 ; nexpr_of_int 1 ; nexpr_of_int 8];;

calculer_expr (expr_of_nexpr ne3);;

(*Jeux d'essai de simplification*)

let s1 = Nary (SUB, [Nary (SUB, [nexpr_of_int 1])]);;
let s2 = Nary (SUB, [Nary (SUB, [Nary (SUB, [nexpr_of_int 1])])]);;
let s3 = Nary (SUB, [Nary (SUB, [Nary (SUB, [Nary (SUB, [nexpr_of_int 1])])])]);;
let s4 = Nary (ADD, [nexpr_of_int 5]);;
let s5 = Nary (SUB, [nexpr_of_int 0 ; nexpr_of_int 4 ; nexpr_of_int 2]);;
let s6 = Nary (ADD, [nexpr_of_int 5 ; nexpr_of_int 0 ; nexpr_of_int 4 ]);;
let s7 = Nary (ADD, [nexpr_of_int 0 ; nexpr_of_int 0 ; nexpr_of_int 0 ]);;
let s8 = Nary (SUB, [nexpr_of_int 5 ; nexpr_of_int 0 ; nexpr_of_int 4 ]);;
let s9 = Nary (SUB, [nexpr_of_int 5 ; nexpr_of_int 0 ; nexpr_of_int 0 ]);;
let s10 = Nary (SUB, [nexpr_of_int 0 ; nexpr_of_int 1]);;
let s11 = Nary (MUL, [nexpr_of_int 5 ; nexpr_of_int 1 ; nexpr_of_int 4 ]);;
let s12 = Nary (MUL, [nexpr_of_int 5 ; nexpr_of_int 0 ; nexpr_of_int 4 ]);;
let s13 = Nary (DIV, [nexpr_of_int 5 ; nexpr_of_int 1 ; nexpr_of_int 4 ]);;
let s14 = Nary (DIV, [nexpr_of_int 0 ; nexpr_of_int 8 ; nexpr_of_int 4 ]);;

let s15 = Nary (POW, [nexpr_of_int 5 ; nexpr_of_int 0 ; nexpr_of_int 4 ]);;
let s16 = Nary (POW, [nexpr_of_int 1 ; nexpr_of_int 5 ; nexpr_of_int 3 ]);;
let s17 = Nary (POW, [nexpr_of_int 0 ; nexpr_of_int 8 ; nexpr_of_int 4 ]);;
let s18 = Nary (POW, [nexpr_of_int 2 ; nexpr_of_int 1 ; nexpr_of_int 3 ]);;


