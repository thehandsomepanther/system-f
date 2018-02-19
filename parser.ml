(*
 * Parsing of types and expressions.
 *
 * We parse via the Core s-expression library. That is, first we read
 * the input to an s-expression, and then we pattern match the
 * s-expression to build abstract syntax.
 *)
open Core
open Syntax

module S = Sexp

exception Bad_syntax of string * S.t

(* Raises a syntax error. *)
let stx_err exp got = raise (Bad_syntax(exp, got))

(* Parses a type from an s-expression. *)
let rec type_of_sexp = function
  | S.Atom "int" -> IntT
  | S.Atom n ->
      (try VarT (Int.of_string n)
       with Failure _ ->
         stx_err "type variable reference or 'int'" (S.Atom n))
  | S.List (S.Atom "->" :: args) as t0 ->
      (match List.rev (List.map ~f:type_of_sexp args) with
       | last :: init -> ArrT(List.rev init, last)
       | [] -> stx_err "return type" t0)
  | S.List (S.Atom "tup" :: args) ->
      TupT(List.map ~f:type_of_sexp args)
  | S.List (S.Atom "all" :: arg :: []) ->
      AllT (type_of_sexp arg)
  | s -> failwith ("could not parse type: " ^ S.to_string s)

(* Parses a type from a string, via an s-expression. *)
let type_of_string s = type_of_sexp (S.of_string s)

(* Keywords, which cannot be identifiers. *)
let keywords = ["let"; "let*"; "-"; "if0"; "tup"; "prj"; "lam"; "fix"]

(* Is the given string a keyword? *)
let is_keyword = List.mem ~equal:(=) keywords

(* Raises a syntax error if given a keyword; otherwise does nothing. *)
let assert_not_keyword x =
  if is_keyword x
  then stx_err "identifier" (S.Atom x)

(* Parses a bindings of a variable to a thing, given a function for
 * parsing the thing. *)
let binding_of_sexp x_of_sexp = function
  | S.List [S.Atom x; e] ->
      assert_not_keyword x;
      (x, x_of_sexp e)
  | s -> stx_err "binding" s

(* Parses a list of bindings, given a function for parsing the
 * right-hand-side of one binding. *)
let bindings_of_sexps x_of_sexp = List.map ~f:(binding_of_sexp x_of_sexp)

(* Parses an expression from an s-expression. *)
let rec expr_of_sexp sexp0 =
  match sexp0 with
  | S.Atom s ->
      (try IntE (Int.of_string s)
       with Failure _ ->
         assert_not_keyword s;
         VarE s)
  | S.List ss ->
      match ss with
      | [] -> stx_err "expression" sexp0
      | [S.Atom "let"; S.List bindings; body] ->
          LetE(bindings_of_sexps expr_of_sexp bindings, expr_of_sexp body)
      | [S.Atom "let*"; S.List bindings; body] ->
          let bindings' = bindings_of_sexps expr_of_sexp bindings in
          List.fold_right ~f:(fun b e' -> LetE([b], e'))
                          ~init:(expr_of_sexp body)
                          bindings'
      | [S.Atom "-"; e1; e2] ->
          SubE(expr_of_sexp e1, expr_of_sexp e2)
      | [S.Atom "if0"; e1; e2; e3] ->
          If0E(expr_of_sexp e1, expr_of_sexp e2, expr_of_sexp e3)
      | (S.Atom "tup" :: es) ->
          TupE(List.map ~f:expr_of_sexp es)
      | [S.Atom "prj"; e; S.Atom ix] ->
          let ix = try int_of_string ix
                   with Failure _ -> stx_err "integer" (S.Atom ix) in
          PrjE(expr_of_sexp e, ix)
      | [S.Atom "lam"; S.List bindings; body] ->
          LamE(bindings_of_sexps type_of_sexp bindings, expr_of_sexp body)
      | [S.Atom "fix"; S.Atom x; t; e] ->
          assert_not_keyword x;
          FixE(x, type_of_sexp t, expr_of_sexp e)
      | S.Atom op :: _ when is_keyword op ->
          stx_err op sexp0
      | [S.Atom "Lam"; body] ->
          LAME(expr_of_sexp body)
      | [S.Atom "@"; e; t] ->
          APPE(expr_of_sexp e, type_of_sexp t)
      | e0 :: es ->
          AppE(expr_of_sexp e0, List.map ~f:expr_of_sexp es)

(* Parses an expression from a string, via s-expression. *)
let expr_of_string s = expr_of_sexp (S.of_string s)
