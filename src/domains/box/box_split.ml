open Var_store
open Box_representation

module type Variable_order = functor (S: Var_store_sig) ->
sig
  module Store : Var_store_sig
  val select: Store.t -> (Store.key * Store.cell) option
end with module Store=S

module type Value_order = functor (I: Vardom_sig.Vardom_sig) ->
sig
  module I: Vardom_sig.Vardom_sig
  val select: I.t -> box_expr
end with module I=I

module type Distributor =
sig
  val distribute: box_var -> box_expr -> box_constraint list
end

module type Box_split_sig = functor (S: Var_store_sig) ->
sig
  module Store : Var_store_sig
  val split: Store.t -> box_constraint list
end with module Store=S

module Input_order(Store: Var_store_sig) =
struct
  module Store = Store
  module I = Store.I

  exception Found_var of box_var * I.t
  let select store =
    try
      Store.iter (fun v d -> if not (I.is_singleton d) then raise (Found_var (v,d))) store;
      None
    with Found_var (v,d) -> Some (v,d)
end

(* This module factorizes `First_fail` and `Anti_first_fail`. *)
module Width_order(Store: Var_store_sig) =
struct
  module I = Store.I
  module B = I.B
  let select store width_cmp =
    let size (l,h) = B.sub_up h l in
    let var =
      Store.fold (fun a v d ->
        if I.is_singleton d then a
        else
          let width = size (I.to_range d) in
          match a with
          | Some (best,_,_) when width_cmp width best -> Some (width,v,d)
          | Some _ -> a
          | None -> Some (width,v,d))
      None store in
    match var with
    | Some (_, v,d) -> Some (v,d)
    | None -> None
end

module First_fail(Store: Var_store_sig) =
struct
  module Store = Store
  module W = Width_order(Store)
  let select store = W.select store Store.I.B.lt
end

module Anti_first_fail(Store: Var_store_sig) =
struct
  module Store = Store
  module W = Width_order(Store)
  let select store = W.select store Store.I.B.gt
end

module Middle (I: Vardom_sig.Vardom_sig) =
struct
  module I = I
  module B = I.B
  let select itv =
    let open Csp in
    let (l,u) = I.to_range itv in
    Cst (B.to_rat (B.div_down (B.add_up l u) B.two), Int)
end

module Lower_bound (I: Vardom_sig.Vardom_sig) =
struct
  module I = I
  module B = I.B
  let on_bound itv select = Csp.(Cst (B.to_rat (select (I.to_range itv)), Int))
  let select itv = on_bound itv fst
end

module Upper_bound (I: Vardom_sig.Vardom_sig) =
struct
  module I = I
  module LB = Lower_bound(I)
  let select itv = LB.on_bound itv snd
end

module Assign =
struct
  let distribute var value = Csp.([(Var var, EQ, value); (Var var, NEQ, value)])
end

module Bisect =
struct
  let distribute var value = Csp.([(Var var, LEQ, value); (Var var, GT, value)])
end

module Make
  (VARIABLE: Variable_order)
  (VALUE: Value_order)
  (Distrib: Distributor)
  (Store: Var_store_sig) =
struct
  module Store = Store
  module Variable = VARIABLE(Store)
  module Value = VALUE(Store.I)

  let split store =
    match Variable.select store with
    | None -> []
    | Some (v, itv) -> Distrib.distribute v (Value.select itv)
end

module First_fail_bisect = Make(First_fail)(Middle)(Bisect)
module First_fail_LB = Make(First_fail)(Lower_bound)(Assign)
module Anti_first_fail_LB = Make(Anti_first_fail)(Lower_bound)(Assign)
module Anti_first_fail_UB = Make(Anti_first_fail)(Upper_bound)(Assign)
module MSLF_simple = First_fail_LB
