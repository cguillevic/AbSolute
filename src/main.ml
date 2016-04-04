open Apron
open ADCP
open Itv
open Bot

let solving = ref true 

let parse_args () =
  let rec doit args = match args with
  | "-precision"::x::r 
  | "-p"::x::r -> Constant.precision := float_of_string x; doit r
  | "-max_sol"::x::r -> Constant.max_sol := int_of_string x; doit r
  | "-max_iter"::x::r -> Constant.max_iter := int_of_string x; doit r
  | "-domain_s"::x::r -> Constant.domain_solving := x; doit r
  | "-domain_m"::x::r -> Constant.domain_minimizing:= x; doit r
  | "-visualization"::r 
  | "-v"::r ->Constant.visualization:=true; doit r
  | x::r -> Constant.problem:=x; doit r
  | [] -> ()
  in Array.to_list Sys.argv |> List.tl |> doit

let main =
  let open Constant in
  parse_args ();
  solving := false;(*Constant.problem <> "test";*)
  let prob = File_parser.parse !problem in
  if !Constant.visualization then Vue.create_window 800 800;
  (* Syntax.print Format.std_formatter prob; *)
  if !solving then
    match !domain_solving with
    | "box" -> Solver.Box.solving prob
    | "boxCP" -> Solver.BoxCP.solving prob
    | "oct" -> Solver.Oct.solving prob
    | "poly" -> Solver.Poly.solving prob 
    | "boxNoct" -> Solver.BoxNOct.solving_various prob
    | "boxNpoly" -> Solver.BoxNPoly.solving_various prob
    | "octNpoly" -> Solver.OctNPoly.solving_various prob
    | _ -> "domain undefined"^(!domain_solving) |> failwith
  else
    match !domain_minimizing with
    | "box" -> Minimizer.Box.minimizing prob
    | "boxCP" -> Minimizer.BoxCP.minimizing prob
    | "oct" -> Minimizer.Oct.minimizing prob
    | "poly" -> Minimizer.Poly.minimizing prob 
    | "boxNoct" -> Minimizer.BoxNOct.minimizing_various prob
    | "boxNpoly" -> Minimizer.BoxNPoly.minimizing_various prob
    | "octNpoly" -> Minimizer.OctNPoly.minimizing_various prob
    | _ -> "domain undefined"^(!domain_minimizing) |> failwith
