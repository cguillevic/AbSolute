(* Copyright 2019 Pierre Talbot

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

(* Documentation taken from the APRON project.

   We consider matrices of 2n*2n upper bounds.
   Let us denote by (i,j) the matrix element at line i, column j; the matrix
   induces the following constraints:
     Vj-Vi <= (2i,2j)
     Vj+Vi <= (2i+1,2j)
    -Vj-Vi <= (2i,2j+1)
    -Vj+Vi <= (2i+1,2j+1)

   Actually, this representation is redudant, and so, we manipulate
   2x2 block lower-triangular matrices.
   Only elements (i,j) such that j/2 <= i/2 are represented:

       j ->  0 1 2 3 4 5
            ___
        0  |_|_|
        1  |_|_|___
  i ->  2  |_|_|_|_|
        3  |_|_|_|_|___
        4  |_|_|_|_|_|_|
        5  |_|_|_|_|_|_|


                 j
             0     -2x0
            2x0      0
       i
           x0-x1  -x0-x1      0   -2x1
           x0+x1  -x0+x1     2x1    0

   Elements such that j/2 > i/2 are retreived by coherence: (i,j) = (j^1,i^1)
*)

open Core
open Bounds

(** A variable is represented by its position in the DBM (line, column). *)
type dbm_var = {
  l: int;
  c: int;
}

(** Constraint of the form `±x - ±y <= d`. *)
type 'b dbm_constraint = {
  v: dbm_var;
  d: 'b;
}

(** An interval view of a variable in the DBM with its lower and upper bounds. *)
type dbm_interval = {
  lb: dbm_var;
  ub: dbm_var;
}

(** Create a variable position in the DBM by taking into account the coherence. *)
val make_var: int -> int -> dbm_var

(** Given a dimension `k`, it gives a canonical representation of this variable in the DBM (which is arbitrarily the lower bound of the interval). *)
val make_canonical_var: int -> dbm_var

(** If `v` is the position of a lower bound, it returns the position of its associated upper bound, and conversly.
    For example given `x - y`, it returns the variable representing `-x + y` which is represented by the element in its diagonal on the same plane. *)
val inv: dbm_var -> dbm_var
val is_lower_bound: dbm_var -> bool
val is_upper_bound: dbm_var -> bool
val as_interval: dbm_var -> dbm_interval

(** `true` if the variable is in a rotated plane. *)
val is_rotated: dbm_var -> bool

(** Retrieve the event index of a variable. *)
val event_of_var: dbm_var -> int list

module type Fold_interval_sig =
sig
  val fold: ('a -> dbm_interval -> 'a) -> 'a -> int -> 'a
end

module Fold_intervals : Fold_interval_sig
module Fold_intervals_canonical : Fold_interval_sig
module Fold_intervals_rotated : Fold_interval_sig

module type DBM_sig =
sig
  module B: Bound_sig.S
  type bound = B.t
  type t

  (** Initialize a DBM of dimension `n`. *)
  val init: int -> t

  (** Initialize an empty DBM. *)
  val empty: t

  (** Increase the dimension of the DBM by one.
      We return the interval of the canonical interval in this dimension. *)
  val extend: ?ty:Types.var_ty -> t -> (t * dbm_var * Types.var_abstract_ty)

  (** Low level access to a cell of the DBM where `get m l c` returns DBM[l][c].
      Precondition: `c/2 <= l/2` (always ensured if `dbm_var` is built with `make_var`). *)
  val get : t -> dbm_var -> bound

  (** Monotonic write: we update the cell at (l,c) only if the value passed as argument is smaller than the one in the DBM.
      Precondition on the variable: same as `get`. *)
  val set : t -> bound dbm_constraint -> t

  (** Returns the interval value of a pair of DBM variables.
      Precisely, it returns (-dbm[lb], dbm[ub]).
      See also `Interval_view_dbm` and `Octagon.project` to recover an "interval" interpretation of these bounds. *)
  val project: t -> dbm_interval -> (bound * bound)

  (** Return `n` copies of the current DBM with the assumption that this one will not be used anymore.
      See `Abstract_domain.lazy_copy`. *)
  val lazy_copy : t -> int -> t list
  val copy : t -> t

  (** The dimension of the DBM is its number of variables. *)
  val dimension: t -> int

  (** Low-level representation of the DBM as a list. *)
  val to_list: t -> bound list

  (** See `DBM.print`. *)
  val print: Format.formatter -> t -> unit

  (** The events returned correspond to the position of the variables in the DBM. *)
  val delta: t -> t * int list

  (** True if some deltas were created. *)
  val has_changed: t -> bool
end

module Make(B:Bound_sig.S) : DBM_sig
module MakeCopy(B:Bound_sig.S) : DBM_sig
module MakeTrailing(B:Bound_sig.S) : DBM_sig
