(* Visitor for expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open E_t


val hyp_rename : Util.hint -> hyp -> hyp
val hyp_of_bound_full: bound -> hyp
val hyps_of_bounds: bounds -> hyp list
val hyps_of_bounds_full: bounds -> hyp list
val hyps_of_bounds_unditto: bounds -> hyp list
val hyps_of_bounds_as_arity_0: bounds -> hyp list
val map_bound_domains:
    (expr -> expr) -> bounds -> bounds
val map_bounds:
    (Util.hint -> Util.hint) -> (expr -> expr) -> bounds -> bounds
val rename_bound: bound -> Util.hint -> bound
val rename_bounds: bounds -> Util.hints -> bounds

type 's scx = 's * hyp Deque.dq

val adj  : 's scx -> hyp -> 's scx
val adjs : 's scx -> hyp list -> 's scx
val adj_unboundeds_unchecked: 's scx -> bounds -> 's scx

class virtual ['s] map : object
  method expr     : 's scx -> expr -> expr
  method pform    : 's scx -> pform -> pform
  method sel      : 's scx -> sel -> sel
  method sequent  : 's scx -> sequent -> 's scx * sequent
  method defn     : 's scx -> defn -> defn
  method defns    : 's scx -> defn list -> 's scx * defn list
  method bounds   : 's scx -> bound list -> 's scx * bound list
  method bound    : 's scx -> bound -> 's scx * bound
  method exspec   : 's scx -> exspec -> exspec
  method instance : 's scx -> instance -> instance
  method hyp      : 's scx -> hyp -> 's scx * hyp
  method hyps     : 's scx -> hyp Deque.dq -> 's scx * hyp Deque.dq
  method adj      : 's scx -> hyp -> 's scx
  method adjs     : 's scx -> hyp list -> 's scx
end

class virtual ['s] iter : object
  method expr     : 's scx -> expr -> unit
  method pform    : 's scx -> pform -> unit
  method sel      : 's scx -> sel -> unit
  method sequent  : 's scx -> sequent -> 's scx
  method defn     : 's scx -> defn -> 's scx
  method defns    : 's scx -> defn list -> 's scx
  method bounds   : 's scx -> bounds (*list*) -> 's scx
  method bound    : 's scx -> bound -> 's scx
  method exspec   : 's scx -> exspec -> unit
  method instance : 's scx -> instance -> unit
  method hyp      : 's scx -> hyp -> 's scx
  method hyps     : 's scx -> hyp Deque.dq -> 's scx
end

class virtual ['s] map_visible_hyp : ['s] map
class virtual ['s] iter_visible_hyp : ['s] iter

class virtual ['s] map_rename : object
    inherit ['s] map
    method rename : ctx -> hyp -> Util.hint -> hyp * Util.hint
    method renames : ctx -> hyp list -> Util.hints -> hyp list * Util.hints
end

val set_to_list: ('a, 'b) Hashtbl.t -> 'a list
val collect_unprimed_vars: ctx -> expr -> string list
val collect_primed_vars: ctx -> expr -> string list
