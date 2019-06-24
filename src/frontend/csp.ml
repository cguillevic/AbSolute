open Tools

(** This exception is raised when a constraint is passed to an abstract domain that cannot represent this constraint. *)
exception Wrong_modelling of string

(* variables are identified by a string *)
type var = string

(* constants are rationals (the domain of the variable *)
type i = Bound_rat.t

type annot = Int | Real

(* unary arithmetic operators *)
type unop = NEG

(* binary arithmetic operators *)
type binop = ADD | SUB | MUL | DIV | POW

(* arithmetic comparison operators *)
type cmpop = EQ | LEQ | GEQ | NEQ | GT | LT

(* Expressions are parametrized by a variable identifier.
   In the logical specification, it is a string representing the textual name of the variable.
   These structures can be reused in abstract domains where the variable's ID is an integer for example (such as in Box). *)

(* numeric expressions *)
type 'var gexpr =
  | Funcall of string * ('var gexpr) list
  | Unary   of unop * 'var gexpr
  | Binary  of binop * 'var gexpr * 'var gexpr
  | Var     of 'var
  | Cst     of i * annot

(* boolean expressions *)
type 'var formula =
  | BVar of 'var
  | Cmp of cmpop * 'var gexpr * 'var gexpr
  | Equiv of 'var formula * 'var formula
  | Imply of 'var formula * 'var formula
  | And of 'var formula * 'var formula
  | Or  of 'var formula * 'var formula
  | Not of 'var formula

type 'var gbconstraint = ('var gexpr * cmpop * 'var gexpr)

type expr = var gexpr
type bformula = var formula
type bconstraint = var gbconstraint

type dom = Finite of i * i   (* [a;b] *)
         | Minf   of i       (* [-oo; a] *)
         | Inf    of i       (* [a; +oo] *)
         | Set    of i list  (* {x1; x2; ...; xn} *)
         | Top               (* [-oo; +oo] *)

(* assign *)
type assign = (annot * var * dom)

(* declarations *)
type decls =  assign list

(* statements *)
type constrs = bformula list

(* jacobian *)
type jacob = (var * expr) list

type ctrs = (bformula * jacob) list

(* constants *)
type csts = (var * (i*i)) list

(* the instance type *)
type instance = i VarMap.t

(* we can annotate a problem with information on the resolution,
   to check the soundness of the solver *)
(* A solution_info is either Some (l), where l is instance list,
   of known solution and known no goods *)
(* or None, when the problem is infeasible *)
type solution_info =
  (instance * bool) list option

(* program *)
type prog = {
    init        : decls;
    constants   : csts;
    objective   : expr;
    constraints : constrs;
    jacobian    : ctrs;
    to_draw     : var list;
    view        : jacob;
    solutions   : solution_info (* extra information about the solutions of te problem *)
  }

(* Constants *)

let constant_one = Cst (Bound_rat.one, Int)
let constant_zero = Cst (Bound_rat.zero, Int)

(*************************************************************)
(*                    PRINTING UTILITIES                     *)
(*************************************************************)

let print_unop fmt = function
  | NEG -> Format.fprintf fmt "-"

let print_binop fmt = function
  | ADD -> Format.fprintf fmt "+"
  | SUB -> Format.fprintf fmt "-"
  | MUL -> Format.fprintf fmt "*"
  | DIV -> Format.fprintf fmt "/"
  | POW -> Format.fprintf fmt "^"

let print_cmpop fmt = function
  | EQ  -> Format.fprintf fmt "="
  | LEQ -> Format.fprintf fmt "<="
  | GEQ -> Format.fprintf fmt ">="
  | NEQ -> Format.fprintf fmt "<>"
  | GT  ->  Format.fprintf fmt ">"
  | LT  -> Format.fprintf fmt "<"

let print_typ fmt = function
  | Int  ->  Format.fprintf fmt "int"
  | Real ->  Format.fprintf fmt "real"

let print_var fmt s = Format.fprintf fmt "%s" s

let print_dom fmt = function
  | Finite (a,b) ->  Format.fprintf fmt "[%s; %s]" (Bound_rat.to_string a) (Bound_rat.to_string b)
  | Minf i -> Format.fprintf fmt "[-oo; %s]" (Bound_rat.to_string i)
  | Inf i -> Format.fprintf fmt "[%s; +oo]" (Bound_rat.to_string i)
  | Set l ->
     let print_set =
       (Format.pp_print_list
          ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
          (fun fmt f -> Format.fprintf fmt "%s" (Bound_rat.to_string f)))
     in
     Format.fprintf fmt "{%a}" print_set l
  | Top -> Format.fprintf fmt "[-oo; +oo]"

let print_assign fmt assignations =
  Format.fprintf fmt "Variables:\n";
  List.iter
    (fun (a,b,c) ->
      Format.fprintf fmt "%a %a in %a\n" print_typ a print_var b print_dom c
    ) assignations

let print_cst fmt (a, b) =
  match (a, b) with
  | (a, b)  when a = b ->  Format.fprintf fmt "%a" pp_print_rat a
  | (a, b) -> Format.fprintf fmt "[%a; %a]" pp_print_rat a pp_print_rat b

let print_csts fmt (a, b) =
  Format.fprintf fmt "%a = %a" print_var a print_cst b

let rec print_all_csts fmt = function
  | [] -> ()
  | a::[] -> Format.fprintf fmt "%a" print_csts a
  | a::tl -> Format.fprintf fmt "%a " print_csts a; print_all_csts fmt tl

let print_gexpr print_var fmt e =
  let rec aux fmt = function
  | Funcall(name,args) ->
     let print_args fmt =
       Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
         aux fmt
     in
     Format.fprintf fmt "%s(%a)" name print_args args
  | Unary (NEG, e) ->
      Format.fprintf fmt "(- %a)" aux e
  | Binary (b, e1 , e2) ->
      Format.fprintf fmt "(%a %a %a)" aux e1 print_binop b aux e2
  | Var v -> Format.fprintf fmt "%a" print_var v
  | Cst (c,Int) -> Format.fprintf fmt "%d" (Bound_rat.to_int_up c)
  | Cst (c,_) -> Format.fprintf fmt "%a" pp_print_rat c
  in
  aux fmt e

let print_formula print_var fmt e =
  let rec aux fmt = function
  | Cmp (c,e1,e2) ->
    Format.fprintf fmt "%a %a %a"
      (print_gexpr print_var) e1 print_cmpop c (print_gexpr print_var) e2
  | BVar v -> Format.fprintf fmt "%a" print_var v
  | Equiv (b1,b2) ->
    Format.fprintf fmt "%a <=> %a"
      aux b1 aux b2
  | Imply (b1,b2) ->
    Format.fprintf fmt "%a => %a"
      aux b1 aux b2
  | And (b1,b2) ->
    Format.fprintf fmt "%a && %a"
      aux b1 aux b2
  | Or  (b1,b2) ->
    Format.fprintf fmt "%a || %a"
      aux b1 aux b2
  | Not b -> Format.fprintf fmt "not %a" aux b in
  aux fmt e

let print_gconstraint print_var fmt (e1,op,e2) =
  Format.fprintf fmt "%a" (print_formula print_var) (Cmp (op,e1,e2))

let print_gconstraints print_var constraints =
  List.iter (Format.printf "%a\n" (print_gconstraint print_var)) constraints

let string_of_gconstraint print_var c = begin
  print_gconstraint print_var Format.str_formatter c;
  Format.flush_str_formatter ()
end

let print_expr = print_gexpr print_var
let print_bformula = print_formula print_var
let print_bconstraint = print_gconstraint print_var
let print_bconstraints = print_gconstraints print_var
let string_of_bconstraint = string_of_gconstraint print_var

let print_constraints fmt constraints =
  List.iter
    (fun c ->
      Format.fprintf fmt "%a\n" print_bformula c
    ) constraints

let print_jacob fmt (v, e) =
  Format.fprintf fmt "\t(%a, %a)" print_var v print_expr e

let rec print_jacobian fmt = function
  | [] -> ()
  | (c, j)::tl -> Format.fprintf fmt "%a;\n" print_bformula c; (* List.iter (print_jacob fmt) j; Format.fprintf fmt "\n";*) print_jacobian fmt tl

let print_view fmt (v, e) =
  Format.fprintf fmt "%a = %a" print_var v print_expr e

let print fmt prog =
  Format.fprintf fmt "%a\n" print_assign prog.init;
  Format.fprintf fmt "%a\n" print_constraints prog.constraints

(*************************************************************)
(*                         PREDICATES                        *)
(*************************************************************)

(* checks if an expression contains a variable *)
let rec has_variable = function
  | Funcall(name,args) -> List.exists has_variable args
  | Unary (u, e) -> has_variable e
  | Binary(b, e1, e2) -> has_variable e1 || has_variable e2
  | Var _ -> true
  | Cst _ -> false

(* checks if an expression is linear *)
let rec is_linear = function
  | Unary (NEG,e) -> is_linear e
  | Binary(MUL, e1, e2) | Binary(DIV, e1, e2)
    -> not (has_variable e1 && has_variable e2) && is_linear e1 && is_linear e2
  | Binary(POW, e1, e2)
    -> not (has_variable e1 || has_variable e2)
  | Binary(_, e1, e2) -> is_linear e1 && is_linear e2
  | Var _ | Cst _ -> true
  | _ -> false

(* checks if a constraints is linear *)
let rec is_cons_linear = function
  | Cmp (_,e1,e2) -> is_linear e1 && is_linear e2
  | BVar _ -> true
  | Equiv (b1,b2)
  | Imply (b1,b2)
  | And (b1,b2)
  | Or (b1,b2) -> is_cons_linear b1 && is_cons_linear b2
  | Not b -> is_cons_linear b

(*****************************************)
(*        SYMBOLIC TRANSFORMATION        *)
(*****************************************)

(* cmp operator inversion *)
let inv = function
  | EQ  -> EQ
  | LEQ -> GEQ
  | GEQ -> LEQ
  | NEQ -> NEQ
  | GT  -> LT
  | LT  -> GT

let zero_val = Bound_rat.zero
let is_zero = Bound_rat.equal zero_val
let is_neg c = Bound_rat.sign c = -1
let one_val = Bound_rat.one

let one = Cst (one_val,Int)
let zero = Cst (zero_val,Int)
let two  = Cst ((Bound_rat.two),Int)
let sqr expr = Binary (POW, expr, two)
let plus_one expr = Binary (ADD, one, expr)

let power a b = Bound_rat.of_float ((Bound_rat.to_float_up a) ** (Bound_rat.to_float_up b))

let apply f e1 e2 b op =
  let (e1', b1) = f e1 b in
  let (e2', b2) = f e2 b in
  (Binary (op, e1', e2'), b1 || b2)

let is_cst = function
  | Cst _ -> true
  | _ -> false

let rec to_cst c b = function
  | [] -> Cst (c,Real)
  | (Cst (a, _))::t -> if b then to_cst (Bound_rat.add c a) b t else to_cst (Bound_rat.mul c a) b t
  | h::t -> to_cst c b t

let rec to_fcst c = function
  | [] -> c
  | (Cst (a,annt))::t -> to_fcst (Bound_rat.add c a) t
  | h::t -> to_fcst c t

let rec distribute (op, c) = function
  | Funcall (name, args) ->  Binary (op, Funcall(name, args), c)
  | Cst (a,annt) -> Binary (op, Cst (a,annt), c)
  | Var v -> Binary (op, Var v, c)
  | Unary (NEG, e) -> Unary (NEG, distribute (op, c) e)
  | Binary (binop, _, _) as expr when binop = POW -> Binary (op, expr, c)
  | Binary (binop, e, Cst (a,annt)) when binop = op -> Binary (op, e, Binary (MUL, Cst (a,annt), c))
  | Binary (binop, Cst (a,annt), e) when binop = op -> Binary (op, Binary (op, Cst (a,annt), c), e)
  | Binary (DIV|MUL as binop, Cst (a,annt), e) -> Binary (binop, Binary (op, Cst (a,annt), c), e)
  | Binary (DIV, e, Cst (a,annt)) -> Binary (op, e, Binary (DIV, c, Cst (a,annt)))
  | Binary (MUL, e, Cst (a,annt)) -> Binary (MUL, e, Binary (op, Cst (a,annt), c))
  | Binary (binop, e1, e2) -> Binary (binop, distribute (op, c) e1, distribute (op, c) e2)

let rec expand = function
  | Funcall (name, args) -> Funcall (name, args)
  | Cst (c,ant) -> Cst (c,ant)
  | Var v -> Var v
  | Unary (unop, e) -> Unary (unop, expand e)
  | Binary (MUL, Cst (c,ant), e) | Binary (MUL, e, Cst (c,ant)) -> distribute (MUL, Cst (c,ant)) e
  | Binary (DIV, e, Cst (c,ant)) -> distribute (DIV, Cst (c,ant)) e
  | Binary (binop, e1, e2) -> Binary (binop, expand e1, expand e2)


let join_annot a b =
  match a,b with
  | Int,Int -> Int
  | _ -> Real

(* simplifies elementary function *)
let rec simplify_expr expr change =
  (* Format.printf "  --> %a@." print_expr expr; *)
  match expr with
  | Funcall (name, args) -> (Funcall (name, args), change)
  | Cst (c,ant) -> (Cst (c,ant), change)
  | Var v -> (Var v, change)
  | Unary (NEG, e) ->
    (match e with
     | Cst (c,ant) when is_zero c -> (zero, true)
     | Cst (c,ant) -> (Cst ((Bound_rat.neg c),ant), true)
     | Unary (NEG, e') -> simplify_expr e' true
     | Binary (SUB, Cst (a,ant), Cst (b,ant')) -> (Cst ((Bound_rat.sub b a),ant), true)
     | Binary (SUB, a1, a2) -> simplify_expr (Binary (SUB, a2, a1)) true
     | _ -> let (e', b) = simplify_expr e change in (Unary (NEG, e'), b)
    )
  | Binary (b, e1, e2) ->
    (match b with
     | ADD ->
       (match e1, e2 with
        | Cst (a,ant), Cst (b,ant') -> (Cst ((Bound_rat.add a b),join_annot ant ant'), true)
        | Cst (z,annot), e2 when is_zero z -> simplify_expr e2 change
        | e1, Cst (z,annot) when is_zero z -> simplify_expr e1 change
        | e1 , Cst (c,annot) when is_neg c ->
           simplify_expr (Binary(SUB, e1, Cst ((Bound_rat.neg c),annot))) true
        | Cst (c,annot), e1 when is_neg c ->
           simplify_expr (Binary(SUB, e1, Cst ((Bound_rat.neg c),annot))) true
        | e1, Unary(NEG, e) -> simplify_expr (Binary(SUB, e1, e)) true
        | Unary(NEG, e), e2 -> simplify_expr (Binary(SUB, e2, e)) true
        | e1, e2 -> apply simplify_expr e1 e2 change ADD
       )
     | SUB ->
       (match e1, e2 with
        | Cst (a,ant), Cst (b,ant') -> (Cst ((Bound_rat.sub a b),(join_annot ant ant')), true)
        | Cst (c,annt), _ when is_zero c->
           let (e, _) = simplify_expr e2 change in (Unary (NEG, e), true)
        | _, Cst (c,ant) when is_zero c -> simplify_expr e1 change
        | e1 , Cst (c,ant') when is_neg c -> simplify_expr (Binary(ADD, e1, Cst ((Bound_rat.neg c),ant'))) true
        | Cst (c,ant), e1 when is_neg c -> simplify_expr (Unary(NEG, Binary(ADD, e1, Cst ((Bound_rat.neg c),ant)))) true
        | _, Unary(NEG, e) -> simplify_expr (Binary(ADD, e1, e)) true
        | Unary(NEG, e), _ -> simplify_expr (Unary(NEG, (Binary(ADD, e, e2)))) true
        | _, _ -> apply simplify_expr e1 e2 change SUB
       )
     | MUL ->
       (match e1, e2 with
        | Cst (a,ant), Cst (b,ant') -> (Cst ((Bound_rat.mul a b),join_annot ant ant'), true)
        | Cst (c,annot), _ when is_zero c -> (zero, true)
        | _, Cst (c,annot) when is_zero c -> (zero, true)
        | Cst (c,annot), _ when Bound_rat.equal one_val c -> simplify_expr e2 change
        | _, Cst (c,annot) when Bound_rat.equal one_val c -> simplify_expr e1 change
        | e1 , Cst (c,annot) when is_neg c -> simplify_expr (Unary(NEG, (Binary(MUL, e1, Cst ((Bound_rat.neg c),annot))))) true
        | Cst (c,annt), e1 when is_neg c -> simplify_expr (Unary(NEG, Binary(MUL, e1, Cst ((Bound_rat.neg c),annt)))) true
        | e', Unary(NEG, e) | Unary(NEG, e), e' -> simplify_expr (Unary(NEG, (Binary(MUL, e, e')))) true
        | _, _ -> apply simplify_expr e1 e2 change MUL
       )
     | DIV ->
       (match e1, e2 with
        | _, Cst (c,ant) when is_zero c -> (zero, true) (* TODO treat NaN *)
        | Cst (c,ant), _ when is_zero c -> (zero, true)
        (* | Cst a, Cst b when Bound_rat.equal a b -> (one, true)
         * | Cst a, Cst b when Bound_rat.equal a (Bound_rat.neg b) -> (Cst (Bound_rat.of_int (-1)), true)
         * | Cst a, Cst b -> (Cst (Bound_rat.div a b), true)
         * | _, Cst c when Bound_rat.equal c one_val -> simplify_expr e1 change
         * | e1, Unary(NEG, e2) | Unary(NEG, e1), e2 -> simplify_expr (Unary(NEG, (Binary(DIV, e1, e2)))) true
         * | e1 , Cst c when is_neg c -> simplify_expr (Unary(NEG, (Binary(DIV, e1, Cst (Bound_rat.neg c))))) true
         * | Cst c, e2 when is_neg c -> simplify_expr (Unary(NEG, Binary(DIV, Cst (Bound_rat.neg c), e2))) true *)
        | _, _ -> apply simplify_expr e1 e2 change DIV
       )
     | POW ->
       (match e1, e2 with
        (* | Cst a, Cst b -> (Cst (power a b), true)
         * | Cst c, _ when is_zero c -> (zero, true)
         * | _, Cst c when is_zero c -> (one, true)
         * | _, Cst c when Bound_rat.equal one_val c -> simplify_expr e1 change *)
        | _, _ -> apply simplify_expr e1 e2 change POW
       )
    )

let rec simplify_fp expr =
  let (e, b) = simplify_expr expr false in
  if b then
    simplify_fp e
  else
    e

let rec simplify_bformula = function
  | Cmp (op,e1,e2) -> Cmp (op, simplify_fp e1, simplify_fp e2)
  | BVar v -> BVar v
  | Equiv (b1,b2) -> Equiv (simplify_bformula b1, simplify_bformula b2)
  | Imply (b1,b2) -> Imply (simplify_bformula b1, simplify_bformula b2)
  | And (b1,b2) -> And (simplify_bformula b1, simplify_bformula b2)
  | Or (b1,b2) -> Or (simplify_bformula b1, simplify_bformula b2)
  | Not b -> Not (simplify_bformula b)

let left_hand_side (op, e1, e2) =
  match e1, e2 with
  | Cst (c,ant), _  when is_zero c-> (inv op, e2)
  | _, Cst (c,ant) when is_zero c -> (op, e1)
  | _, _ -> (op, simplify_fp (Binary (SUB, e1, e2)))

let rec left_hand = function
  | Cmp (op,e1,e2) -> left_hand_side (op, e1, e2)
  | BVar v -> failwith "`left_hand` on a boolean variable."
  | Equiv (b1,b2) | Imply (b1,b2) | And (b1,b2) | Or (b1,b2) ->
      left_hand b1
  | Not b -> left_hand b


(* derives a function regarding a variable *)
let rec derivate expr var =
  match expr with
  | Cst _ -> zero
  | Var v -> if var = v then one else zero
  | Unary (NEG, e) ->  Unary (NEG, derivate e var)
  | Binary (b, e1, e2) ->
    (match b with
     | ADD -> Binary (ADD, derivate e1 var, derivate e2 var)
     | SUB -> Binary (SUB, derivate e1 var, derivate e2 var)
     | MUL -> Binary (ADD, Binary (MUL, derivate e1 var, e2), Binary (MUL, e1, derivate e2 var))
     | DIV -> Binary (DIV, Binary (SUB, Binary (MUL, derivate e1 var, e2), Binary (MUL, e1, derivate e2 var)), sqr e2)
     | POW -> begin
        let rec flatten_pow e
            = function
            | 0 -> one
            | 1 -> e
            | n -> Binary (MUL, e, flatten_pow e (n-1))
        in
        match e2 with
        | Cst (i,_) -> begin
            match Polynom.RationalRing.to_int i with
            | Some i -> let expr' = flatten_pow e1 i in
                derivate expr' var
            | None -> zero
            end
        | _ -> zero
        end
    )
  | Funcall _ -> zero (* TODO IMPLEMENTATION *)

let rec derivative bformula var =
  match bformula with
  | Cmp (op,e1,e2) -> Cmp (op, derivate e1 var, derivate e2 var)
  | BVar v -> failwith "`derivative` of a boolean variable is unsupported."
  | Equiv (b1,b2) -> Equiv (derivative b1 var, derivative b2 var)
  | Imply (b1,b2) -> Imply (derivative b1 var, derivative b2 var)
  | And (b1,b2) -> And (derivative b1 var, derivative b2 var)
  | Or (b1,b2) -> Or (derivative b1 var, derivative b2 var)
  | Not b -> Not (derivative b var)

let is_arith = function
  | Cmp (_, _, _) -> true
  | _ -> false

let ctr_jacobian c vars =
  List.fold_left (
    fun l (_, v, _) ->
      let expr = if is_arith c then
          let new_c = simplify_bformula (derivative c v) in
          let (op, e) = left_hand new_c in
          e
        else zero
      in
    (v, expr)::l
  ) [] vars

let compute_jacobian csp =
  List.fold_left (
    fun l c -> (c, ctr_jacobian c csp.init)::l
  ) [] csp.constraints


(*****************************************)
(*        USEFUL FUNCTION ON AST         *)
(*****************************************)

let empty = {init = []; constraints= []; constants=[]; objective = zero; to_draw=[]; jacobian = []; view = []; solutions = Some []}

let get_vars p =
  List.map (fun (_,v,_) -> v) p.init

let add_var csp name inf sup kind =
  let assign = (kind, name, (Finite(inf,sup))) in
  {csp with init = assign::csp.init}

let add_real_var csp name inf sup = add_var csp name inf sup Real
let add_int_var csp name inf sup = add_var csp name inf sup Int

let add_constr csp c =
  let jac = List.map (
    fun (_, v, _) ->
    let new_c = simplify_bformula (derivative c v) in
    let (_, expr) = left_hand new_c in
    (v, expr)
  ) csp.init in
  {csp with constraints = c::csp.constraints; jacobian = (c, jac)::csp.jacobian}

(* converts a domain representation to a couple of constraints *)
let domain_to_constraints : assign -> bformula =
  let of_singleton v f = Cmp (EQ, Var v, Cst (f,Real)) in
  fun (_,v,d) ->
  match d with
  | Finite (l,h) -> And (Cmp (GEQ, Var v, Cst (l,Real)), (Cmp (LEQ, Var v, Cst (h,Real))))
  | Minf (i) -> Cmp(LEQ, Var v, Cst (i,Real))
  | Inf (i) -> Cmp(GEQ, Var v, Cst (i,Real))
  | Set (h::tl) ->
     List.fold_left (fun acc e ->
         Or(acc, of_singleton v e)
       ) (of_singleton v h) tl
  | _ -> Cmp(EQ, Cst ((Bound_rat.one),Int), (Cst ((Bound_rat.one),Int)))

(* iter on expr*)
let rec iter_expr f = function
  | Binary (_,e1,e2) as b -> f b; iter_expr f e1; iter_expr f e2
  | Unary (_,e) as u -> f u; iter_expr f e
  | x -> f x

(* iter on constraints *)
let rec iter_constr f_expr f_constr = function
  | Cmp (_,e1,e2) as constr ->
     f_constr constr;
     iter_expr f_expr e1;
     iter_expr f_expr e2
  | BVar _ -> ()
  | (Equiv (b1,b2) as constr)
  | (Imply (b1,b2) as constr)
  | (And (b1,b2) as constr)
  | (Or  (b1,b2) as constr) ->
     f_constr constr;
     iter_constr f_expr f_constr b1;
     iter_constr f_expr f_constr b2
  | Not b as constr ->
     f_constr constr;
     iter_constr f_expr f_constr b

(* boolean formules map *)
let rec map_constr f = function
  | Cmp (op,e1,e2) ->
     let op',e1',e2' = f (op,e1,e2) in
     Cmp(op',e1',e2')
  | BVar v -> failwith "map_constr not applicable on Boolean variables."
  | Equiv (b1,b2) -> Equiv (map_constr f b1, map_constr f b2)
  | Imply (b1,b2) -> Imply (map_constr f b1, map_constr f b2)
  | And (b1,b2) -> And (map_constr f b1, map_constr f b2)
  | Or (b1,b2) -> Or (map_constr f b1, map_constr f b2)
  | Not b -> Not (map_constr f b)

(** comparison operator negation *)
let neg = function
  | EQ  -> NEQ
  | LEQ -> GT
  | GEQ -> LT
  | NEQ -> EQ
  | GT  -> LEQ
  | LT  -> GEQ

(** constraint negation *)
let rec neg_bformula = function
  | Cmp (op,e1,e2) -> Cmp(neg op,e1,e2)
  (* Trivial negation for equiv and imply in order to keep the structure of the formula (we do not rewrite the formula into AND and OR here). *)
  | BVar v -> Not (BVar v)
  | Equiv (b1,b2) -> Not (Equiv (b1, b2))
  | Imply (b1,b2) -> Not (Imply (b1, b2))
  | And (b1,b2) -> Or (neg_bformula b1, neg_bformula b2)
  | Or (b1,b2) -> And (neg_bformula b1, neg_bformula b2)
  | Not b -> b

let neg_bconstraint (e1,op,e2) = (e1,neg op,e2)

(*****************************************)
(*        PREPROCESSING FUNCTIONS        *)
(*****************************************)

let rec replace_cst_expr (id, cst) expr =
  match expr with
  | Var v when v = id -> Cst (cst,Real)
  | Unary (op, e) -> Unary (op, replace_cst_expr (id, cst) e)
  | Binary (op, e1, e2) -> Binary (op, replace_cst_expr (id, cst) e1, replace_cst_expr (id, cst) e2)
  | Funcall (v, e) -> Funcall (v, List.map(replace_cst_expr (id, cst))e)
  | _ as e -> e

let rec replace_cst_bformula cst = function
  | Cmp (op, e1, e2) -> Cmp (op, replace_cst_expr cst e1, replace_cst_expr cst e2)
  | BVar v -> BVar v
  | Equiv (b1, b2) -> Equiv (replace_cst_bformula cst b1, replace_cst_bformula cst b2)
  | Imply (b1, b2) -> Imply (replace_cst_bformula cst b1, replace_cst_bformula cst b2)
  | And (b1, b2) -> And (replace_cst_bformula cst b1, replace_cst_bformula cst b2)
  | Or (b1, b2) -> Or (replace_cst_bformula cst b1, replace_cst_bformula cst b2)
  | Not b -> Not (replace_cst_bformula cst b)

module Variables = Set.Make(struct type t=var let compare=compare end)

let rec get_vars_expr = function
  | Cst (_,_)          -> []
  | Var v              -> [v]
  | Unary (_, e)       -> get_vars_expr e
  | Binary (_, e1, e2) -> List.rev_append (get_vars_expr e1) (get_vars_expr e2)
  | Funcall (_,args)   -> List.concat (List.map get_vars_expr args)

let get_vars_set_expr expr = Variables.of_list (get_vars_expr expr)

let rec get_vars_bformula = function
  | Cmp (_, e1, e2) -> List.append (get_vars_expr e1) (get_vars_expr e2)
  | BVar v -> [v]
  | Equiv (b1, b2)
  | Imply (b1, b2)
  | And (b1, b2)
  | Or (b1, b2) -> List.append (get_vars_bformula b1) (get_vars_bformula b2)
  | Not b -> get_vars_bformula b

let get_vars_set_bformula bformula = Variables.of_list (get_vars_bformula bformula)

let vars_of_bconstraint (e1,op,e2) = get_vars_bformula (Cmp (op,e1,e2))

(* True if the constraint is fully defined over the set of variables `vars`. *)
let is_defined_over vars (e1,op,e2) =
  List.for_all (fun v -> List.mem v vars) (get_vars_bformula (Cmp (op,e1,e2)))

let get_vars_jacob jacob =
  List.map (fun (c, j) -> (c, get_vars_set_bformula c, j)) jacob

let replace_cst_jacob (id, cst) jacob =
  List.map (fun (c, vars, j) ->
    if Variables.mem id vars then
      (replace_cst_bformula (id, cst) c, Variables.remove id vars, j)
    else (c, vars, j)
  ) jacob

let from_cst_to_expr (id, (l, u)) =
  if l = u then [(Var id, EQ, Cst (l,Real))]
  else [(Var id, GEQ, Cst (l,Real)); (Var id, LEQ, Cst (u,Real))]

let csts_to_expr csts =
  List.fold_left (fun l cst -> List.append (from_cst_to_expr cst) l) [] csts

let rec replace_var_in_expr : (var -> expr) -> expr -> expr = fun f e ->
  match e with
  | Cst (c,a) -> Cst (c,a)
  | Var v -> f v
  | Unary (op, e) -> Unary (op, replace_var_in_expr f e)
  | Binary (op, e1, e2) -> Binary (op, replace_var_in_expr f e1, replace_var_in_expr f e2)
  | Funcall (fname, args) -> Funcall (fname, (List.map (replace_var_in_expr f) args))

(* Traverse the formula `f` and raise `Wrong_modelling` if we meet a formula that has something else then conjunctions or predicates. *)
let rec mapfold_conjunction f = function
  | Cmp (op, e1, e2) -> f (e1, op, e2)
  | And (f1, f2) -> (mapfold_conjunction f f1)@(mapfold_conjunction f f2)
  | BVar v -> raise (Wrong_modelling "unsupported boolean variable")
  | Equiv (f1, f2) -> raise (Wrong_modelling "unsupported equivalence")
  | Imply (f1, f2) -> raise (Wrong_modelling "unsupported implication")
  | Or (f1, f2) -> raise (Wrong_modelling "unsupported disjunction")
  | Not f1 -> raise (Wrong_modelling "unsupported negation")
