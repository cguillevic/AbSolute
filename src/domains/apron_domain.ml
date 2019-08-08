open Apron
open Csp
open Apron_utils

(*****************************************************************)
(* Some types and values that all the domains of apron can share *)
(* These are generic and can be redefined in the actuals domains *)
(*****************************************************************)
module MAKE(AP:Apron_representation.ADomain) = struct

  module A = Abstractext

  type t = AP.t A.t

  let man = AP.get_manager

  module R = Apron_representation.MAKE(AP)

  let empty = A.top man (Environment.make [||] [||])

  let vars abs =
    let (ivars, rvars) = Environment.vars (A.env abs) in
    let iv = Array.to_list ivars |> List.map (fun v -> (Csp.Int, Var.to_string v)) in
    let rv = Array.to_list rvars |> List.map (fun v -> (Csp.Real, Var.to_string v)) in
    iv@rv

  let add_var abs (typ,v) =
    let e = A.env abs in
    let ints,reals = if typ = Int then [|Var.of_string v|],[||] else [||],[|Var.of_string v|] in
    let env = Environment.add e ints reals in
    A.change_environment man abs env false

  let var_bounds abs v =
    let var = Var.of_string v in
    let i = A.bound_variable man abs var in
    itv_to_rat i

  let bound_vars abs =
    let (ivars, rvars) = Environment.vars (A.env abs) in
    let vars = (Array.to_list ivars)@(Array.to_list rvars) in
    let itvs = List.fold_left (fun l v ->
      (Var.to_string v, itv_to_rat (A.bound_variable man abs v))::l
      ) [] vars in
    List.filter (fun (_, (l, u)) -> l = u) itvs

  let rem_var abs v =
    let var = Var.of_string v in
    let e = Environment.remove (A.env abs) (Array.of_list [var]) in
    A.change_environment man abs e false

  let is_empty a =
    A.is_bottom man a

  let join a b = A.join man a b

  let meet a b = A.meet man a b

  let prune = None

  let filter b (e1,c,e2) =
    let env = A.env b in
    let c = T.cmp_expr_to_tcons (e1,c,e2) env in
    if Tconsext.get_typ c = Tconsext.DISEQ then
      let t1,t2 = Tconsext.splitdiseq c in
      join (A.filter_tcons man b t1) (A.filter_tcons man b t2)
    else A.filter_tcons man b c

  let print = A.print


  (* Useful cross-domain conversion utilities *)

  (** computes the smallest enclosing box *)
  let to_box abs env =
    let abs' = A.change_environment man abs env false in
    A.to_lincons_array man abs' |>
    A.of_lincons_array (Box.manager_alloc ()) env

  (** computes the smallest enclosing octagon *)
  let to_oct abs env =
    let abs' = A.change_environment man abs env false in
    A.to_lincons_array man abs' |>
    A.of_lincons_array (Oct.manager_alloc ()) env

  (** computes the smallest enclosing polyhedron *)
  let to_poly abs env =
    let abs' = A.change_environment man abs env false in
    A.to_lincons_array man abs' |>
    A.of_lincons_array (Polka.manager_alloc_strict ()) env

  (** interval evaluation of an expression within an abtract domain *)
  let forward_eval abs cons =
    let ap_expr = T.expr_to_apron abs cons |> Texpr1.of_expr (A.env abs) in
    let obj_itv = A.bound_texpr man abs ap_expr in
    let obj_inf = obj_itv.Interval.inf
    and obj_sup = obj_itv.Interval.sup in
    (scalar_to_rat obj_inf, scalar_to_rat obj_sup)

  (* utilties for splitting *)
  (* Similar to `largest abs` but does not deal with variables or abstract domain.
   * Instead, it manipulates an array of intervals `tab`. *)
  let rec largest tab i max i_max =
    if i>=Array.length tab then (max, i_max)
    else
      let dim = diam_interval (tab.(i)) in
      if Mpqf.cmp dim max > 0 then largest tab (i+1) dim i
      else largest tab (i+1) max i_max

  (* Given `largest abs = (v, i, d)`, `largest` extracts the variable `v` from `abs`
   * with the largest interval `i` = [l, u], and `d` the dimension of the
   * interval (`u - l` with appropriate rounding). *)
  let largest abs : (Var.t * Interval.t * Mpqf.t) =
    let env = A.env abs in
    let box = A.to_box man abs in
    let tab = box.A.interval_array in
    let rec aux cur i_max diam_max itv_max =
      if cur>=Array.length tab then (i_max, diam_max, itv_max)
      else
        let e = tab.(cur) in
        let diam = diam_interval e in
        if Mpqf.cmp diam diam_max > 0 then aux (cur+1) cur diam e
        else aux (cur+1) i_max diam_max itv_max
    in
    let (a,b,c) = aux 0 0 (Mpqf.of_int 0) tab.(0) in
    ((Environment.var_of_dim env a),c,b)

  (* Compute the minimal and the maximal diameter of an array on intervals *)
  let rec minmax tab i max i_max min i_min =
    if i>=Array.length tab then  (max, i_max, min, i_min)
    else
      let dim = diam_interval (tab.(i)) in
      if Mpqf.cmp dim max > 0 then minmax tab (i+1) dim i min i_min
      else if Mpqf.cmp min dim > 0 then minmax tab (i+1) max i_max dim i
      else minmax tab (i+1) max i_max min i_min

  (* let p1 = (p11, p12, ..., p1n) and p2 = (p21, p22, ..., p2n) two points
   * The vector p1p2 is (p21-p11, p22-p12, ..., p2n-p1n) and the orthogonal line
   * to the vector p1p2 passing by the center of the vector has for equation:
   * (p21-p11)(x1-b1) + (p22-p12)(x2-b2) + ... + (p2n-p1n)(xn-bn) = 0
   * with b = ((p11+p21)/2, (p12+p22)/2, ..., (p1n+p2n)/2) *)
  let rec genere_linexpr gen_env size p1 p2 i list1 list2 cst =
    if i >= size then (list1, list2, cst) else
	    let ci = p2.(i) -. p1.(i) in
	    let cst' = cst +. ((p1.(i) +. p2.(i)) *. ci) in
	    let ci' = 2. *. ci in
	    let coeffi = Coeff.Scalar (Scalar.of_float ci') in
	    let list1' = List.append list1 [(coeffi, Environment.var_of_dim gen_env i)] in
	    let list2' = List.append list2 [(Coeff.neg coeffi, Environment.var_of_dim gen_env i)] in
	    genere_linexpr gen_env size p1 p2 (i+1) list1' list2' cst'

  let split abs _ (e1,e2) =
    let meet_linexpr abs man expr =
      let cons = Linconsext.make expr Linconsext.SUPEQ in
      A.filter_lincons man abs cons
    in
    let abs1 = meet_linexpr abs man e1 in
    let abs2 = meet_linexpr abs man e2 in
    [abs1; abs2]

  (************************************************)
  (* POLYHEDRIC VERSION OF SOME USEFUL OPERATIONS *)
  (************************************************)

  let get_expr man (polyad:Polka.strict Polka.t A.t) =
    let poly = A.to_generator_array man polyad in
    let gen_env = poly.Generator1.array_env in
    (*print_gen gens gen_env;*)
    let size = Environment.size gen_env in
    let gen_float_array = gen_to_array poly size in
    let (p1, _, p2, _, _) = maxdisttab gen_float_array in
    let (list1, list2, cst) = genere_linexpr gen_env size p1 p2 0 [] [] 0. in
    let cst_sca1 = Scalar.of_float (-1. *.(cst +. split_prec)) in
    let cst_sca2 = Scalar.of_float (cst +. split_prec) in
    let linexp = Linexpr1.make gen_env in
    Linexpr1.set_list linexp list1 (Some (Coeff.Scalar cst_sca1));
    let linexp' = Linexpr1.make gen_env in
    Linexpr1.set_list linexp' list2 (Some (Coeff.Scalar cst_sca2));
    (linexp, linexp')

  let is_small man polyad =
    let poly = A.to_generator_array man polyad in
    let gen_env = poly.Generator1.array_env in
    (*print_gen gens gen_env;*)
    let size = Environment.size gen_env in
    let gen_float_array = gen_to_array poly size in
    let (_p1, _i1, _p2, _i2, dist_max) = maxdisttab gen_float_array in
    (dist_max <= !Constant.precision)

  (*********************************)
  (* Sanity and checking functions *)
  (*********************************)

  (** given an abstraction and instance, verifies if the abstraction is implied
     by the instance *)
  let is_abstraction_internal poly instance =
    let env = Abstract1.env poly in
    let var_texpr =
      Tools.VarMap.fold (fun var value acc ->
          let var = Apron.Var.of_string var in
          let value = Texpr1.cst env (Coeff.s_of_mpqf value) in
          (var,value)::acc
        ) instance []
    in
    let var,texpr = List.split var_texpr in
    let varray = Array.of_list var in
    let tarray = Array.of_list texpr in
    let poly_subst = Abstract1.substitute_texpr_array man poly varray tarray None in
    Abstract1.is_top man poly_subst

  let is_abstraction poly instance =
    let instance = Tools.VarMap.map Bound_rat.to_mpqf instance in
    is_abstraction_internal poly instance

  (** Random uniform value within an interval, according to the type *)
  let spawn_itv typ (i:Interval.t) =
    let inf = Apron_utils.scalar_to_mpqf i.Interval.inf in
    let sup = Apron_utils.scalar_to_mpqf i.Interval.sup in
    match typ with
    | Environment.INT ->
       let size = Mpqf.sub sup inf |> Mpqf.to_float |> int_of_float in
       let r = Mpqf.of_int (Random.int (size+1)) in
       Mpqf.add inf r
    | Environment.REAL ->
       let r = Mpqf.of_float (Random.float 1.) in
       Mpqf.add inf (Mpqf.mul (Mpqf.sub sup inf) r)

  (** spawns an instance within a box *)
  let spawn_box box =
    let env = box.Abstract1.box1_env in
    let itvs = box.Abstract1.interval_array in
    let instance,_ =
      Array.fold_left (fun (acc,idx) i ->
          let v = Environment.var_of_dim env idx in
          let typ = Environment.typ_of_var env v in
          let instance = Tools.VarMap.add (Var.to_string v) (spawn_itv typ i) acc in
          instance,(idx+1)
        ) (Tools.VarMap.empty,0) itvs
    in instance

  (** returns a randomly uniformly chosen instanciation of the variables
      if the polyhedron has a nul volume, (e.g equalities in the constraints)
      uniformity is not guaranteed *)
  let spawn poly =
    let nb_try = 10 in
    let env = Abstract1.env poly in
    let rec retry poly n idx =
      let b = Abstract1.to_box man poly in
      let instance = spawn_box b in
      if is_abstraction_internal poly instance then instance
      else if n >= nb_try then
        (* in case we didnt manage to find an instance, we fix a variable and retry *)
        let v = Environment.var_of_dim env idx in
        let typ = Environment.typ_of_var env v in
        let v_itv = Abstract1.bound_variable man poly v in
        let v = Texpr1.var env (Environment.var_of_dim env idx) in
        let value = Texpr1.cst env (Coeff.s_of_mpqf (spawn_itv typ v_itv)) in
        let texpr = Texpr1.binop Texpr1.Sub v value Texpr1.Real Texpr1.Near in
        let tcons = Tcons1.make texpr Tcons1.EQ in
        let tearray = Tcons1.array_make env 1 in
        Tcons1.array_set tearray 0 tcons;
        let poly = Abstract1.meet_tcons_array man poly tearray in
        retry poly 0 (idx+1)
      else retry poly (n+1) idx
    in
    let res = retry poly 0 0 in
    Tools.VarMap.map Bound_rat.of_mpqf res
end
