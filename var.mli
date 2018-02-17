(*
 * Variables
 *)

(* Variables are represented as strings. *)
type t = string

(* Sets of variables. *)
module Set : Core.Set.S with type Elt.t = t

(* Given a suggested variable name and a set of names to avoid,
 * generates a fresh name. *)
val fresh : t -> Set.t -> t

(* Given a list of suggested variable names and a set of names to avoid,
 * generates a list of fresh names of the same length. *)
val fresh_list : t list -> Set.t -> t list

(* Generates the given number of fresh variable names. *)
val fresh_n : int -> Set.t -> t list
