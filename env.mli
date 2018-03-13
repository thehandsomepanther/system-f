(*
 * Environments
 *)

(* The type of variables, which are bound by environments. *)
type var = Var.t

(* The type of an environment mapping var to 'a. *)
type 'a t

(* Throw when lookup fails. *)
exception Unbound_variable of var

(* The empty environment. *)
val empty : 'a t

(* Looks up a variable in an environment. *)
val lookup : 'a t -> var -> 'a option

(* Maps over the elements in the environment *)
val map : (var -> 'a -> 'b) -> 'a t -> 'b t

(* Looks up a variable in an environment, throwing UnboundVariable if
  * not found. *)
val lookup_exn : 'a t -> var -> 'a

(* Extends an environment with a single binding. *)
val extend : 'a t -> var -> 'a -> 'a t

(* Extends an environment with a list of pairs of bindings. Later
 * bindings take precedence. *)
val extend_list : 'a t -> (var * 'a) list -> 'a t

(* Extends an environment given a list of variables and corresponding
 * list of things to bind them to. *)
val extend_lists : 'a t -> var list -> 'a list -> 'a t
