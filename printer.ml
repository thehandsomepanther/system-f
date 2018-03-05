(*
 * Printing
 *
 * We print types, via s-expressions.
 *)
open Core
open Syntax
open Var

module S = Sexp

(* Converts a type to its s-expression representation. *)
let rec type_to_sexp type_env = function
  | IntT ->
      S.Atom "int"
  | ArrT(ts, tr) ->
      S.List (S.Atom "->" :: List.map ~f:(type_to_sexp type_env) (ts @ [tr]))
  | TupT ts ->
      S.List (S.Atom "*" :: List.map ~f:(type_to_sexp type_env) ts)
  | VarT n ->
      (match List.nth type_env n with
        | Some x -> S.Atom x
        | None -> S.Atom ("?" ^ Int.to_string n))
  | AllT (n, t) ->
      let tvs = Var.fresh_n n (Var.Set.of_list type_env) in
      S.List [S.Atom "all";
              S.List (List.map ~f:(fun s -> S.Atom s) tvs);
              type_to_sexp (List.append (List.rev tvs) type_env) t]

(* Prints a type as a string. *)
let type_to_string t = S.to_string_hum (type_to_sexp [] t)
