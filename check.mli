(*
 * Type checking
 *)

open Syntax

(* Thrown on type errors. *)
exception Type_error of string

(* Returns the type of an expression or throws Type_error. *)
val tc : int * typ Env.t -> exp -> typ
