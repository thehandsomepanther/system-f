(*
 * Printing
 *
 * We print types, via s-expressions.
 *)
open Core
open Syntax

module S = Sexp

(* Converts a type to its s-expression representation. *)
let rec type_to_sexp = function
  | IntT ->
      S.Atom "int"
  | ArrT(ts, tr) ->
      S.List (S.Atom "->" :: List.map ~f:type_to_sexp (ts @ [tr]))
  | TupT ts ->
      S.List (S.Atom "*" :: List.map ~f:type_to_sexp ts)

(* Prints a type as a string. *)
let type_to_string t = S.to_string_hum (type_to_sexp t)
