open Format
open ADCP
open Adcp_sig

module Minimize(Abs : AbstractCP) = struct

  include Splitter.Make(Abs)
  module Res = Result.Make(Abs)

  let is_small a obj =
    let (obj_inf, obj_sup) = Abs.forward_eval a obj in
    obj_sup -. obj_inf <= !Constant.precision

  let explore abs constrs obj =
    let open Res in
    let rec aux abs cstrs obj res =
      match consistency abs cstrs with
      | Empty -> res
      | Full abs' -> add_so res abs' obj
      | Maybe(a,cstrs) when stop res a || is_small a obj -> add_uo res a obj
      | Maybe(abs',cstrs)  ->
         List.fold_left (fun res elem ->
            aux elem cstrs obj (incr_step res)
	  ) res (split abs' cstrs)
    in let (_, obj_sup) = Abs.forward_eval abs obj in
    aux abs constrs obj empty_res

  let minimizing prob =
    let open Csp in
    let abs = init prob in
    Format.printf "abs = %a\tvolume = %f@." Abs.print abs (Abs.volume abs);
    let res =  explore abs prob.constraints prob.objective in
    Format.printf "\noptimization ends\n%!%a" Res.print res;
    res

    let minimizing_various prob =
    let open Csp in
    let abs = init prob in
    printf "abs = %a" Abs.print abs;
    if not (Abs.is_bottom abs) then
      let cons = List.filter (fun exp -> not (is_cons_linear exp)) prob.constraints in
      printf "\nconstraints = [";
      List.iter (Format.printf "%a ;" (print_bexpr)) prob.constraints;
      printf "]@.";
      printf "non linear constraints = [";
      List.iter (Format.printf "%a ;" (print_bexpr)) cons;
      printf "]@.";
      let res = explore abs prob.constraints prob.objective in
      printf "solving ends\n%!";
      let nb_sols = res.nb_sure + res.nb_unsure in
      match nb_sols with
      | 0 -> printf "No solutions - #created nodes: %d@." res.nb_steps
      | 1 -> printf "Unique solution - #created nodes: %d@." res.nb_steps
      | _ -> printf "#solutions: %d - #created nodes: %d@." nb_sols res.nb_steps
    else
      printf "No Solutions - #created nodes: 0@."
end

(*
module Box = Minimize(Abstract_box.BoxF)
module BoxCP = Minimize(BoxCP)
module Oct = Minimize(OctBoxCP)
module Poly = Minimize(PolyCP)

module BoxNOct = Minimize(VariousDA.BoxNOct)
module BoxNPoly = Minimize(VariousDA.BoxNPoly)
module OctNPoly = Minimize(VariousDA.OctNPoly)*)