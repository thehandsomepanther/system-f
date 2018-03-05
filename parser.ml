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

let check_equal_any () = Testing.make_check_equal ~test_module:"Parser" ()

let check_equal_t = Testing.make_check_equal ~test_module:"Parser"
                                             ~to_string:Printer.type_to_string
                                             ()

exception Bad_syntax of string * S.t

(* Raises a syntax error. *)
let stx_err exp got = raise (Bad_syntax(exp, got))

(* Keywords, which cannot be identifiers. *)
let keywords = ["let"; "let*"; "-"; "if0"; "tup"; "prj"; "lam"; "fix"; "int"]

(* Is the given string a keyword? *)
let is_keyword = List.mem ~equal:(=) keywords

(* Raises a syntax error if given a keyword; otherwise does nothing. *)
let assert_not_keyword x =
  if is_keyword x
  then stx_err "identifier" (S.Atom x)

(* Parses a list of (type) variables *)
let type_var_of_sexp = function
  | S.Atom x -> (assert_not_keyword x; x)
  | s -> stx_err "type variable" s

(* Parses a type from an s-expression. *)
let rec type_of_sexp type_env = function
  | S.Atom "_" -> HoleT
  | S.Atom "int" -> IntT
  | S.Atom x ->
      assert_not_keyword x;
      (match (List.findi type_env ~f:(fun _ var -> x = var)) with
        | Some (ix, _) -> VarT ix
        | _ -> stx_err "Unbound type variable" (S.Atom x))
  | S.List (S.Atom "->" :: args) as t0 ->
      (match List.rev (List.map ~f:(type_of_sexp type_env) args) with
       | last :: init -> ArrT(List.rev init, last)
       | [] -> stx_err "return type" t0)
  | S.List (S.Atom "tup" :: args) ->
      TupT(List.map ~f:(type_of_sexp type_env) args)
  | S.List [S.Atom "all"; S.List new_type_vars; arg] ->
      let btv = List.map ~f:type_var_of_sexp new_type_vars in
      AllT (List.length btv,
            type_of_sexp ((List.rev btv) @ type_env)
                         arg)
  | s -> failwith ("could not parse type: " ^ S.to_string s)

(* Parses a type from a string, via an s-expression. *)
let type_of_string s = type_of_sexp [] (S.of_string s)

let () =
  check_equal_t ~name:"type_of_sexp; a, b, c ⊢ a : *"
    (fun () -> type_of_sexp ["c"; "b"; "a"] (S.Atom "a"))
    (VarT 2)

let () =
  check_equal_t ~name:"type_of_sexp; all(c d). all(a b). a -> c"
    (fun () -> type_of_string "(all (c d) (all (a b) (-> a c)))")
    (AllT (2, AllT (2, ArrT ([VarT 1], VarT 3))))

(* Parses a bindings of a variable to a thing, given a function for
 * parsing the thing. *)
let bindings_of_let_sexp (x_of_sexp, t_of_sexp) = function
  | S.List [S.Atom x; e; t] ->
      assert_not_keyword x;
      (x, x_of_sexp e, t_of_sexp t)
  | S.List [S.Atom x; e] ->
      assert_not_keyword x;
      (x, x_of_sexp e, HoleT)
  | s -> stx_err "let(*) binding" s

(* Parses a list of bindings, given a function for parsing the
 * right-hand-side of one binding. *)
let bindings_of_let_sexps xt_of_sexp = List.map ~f:(bindings_of_let_sexp xt_of_sexp)

let bindings_of_lam_sexp t_of_sexp = function
  | S.Atom x ->
      assert_not_keyword x;
      (x, HoleT)
  | S.List [S.Atom x; t] ->
      assert_not_keyword x;
      (x, t_of_sexp t)
  | s -> stx_err "lambda arguments" s

let bindings_of_lam_vars t_of_sexp = List.map ~f:(bindings_of_lam_sexp t_of_sexp)

(* Parses an expression from an s-expression. *)
let rec expr_of_sexp type_env sexp0 =
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
          LetE(bindings_of_let_sexps
                 (expr_of_sexp type_env, type_of_sexp type_env)
                 bindings,
               expr_of_sexp type_env body)
      | [S.Atom "let*"; S.List bindings; body] ->
          let bindings' = bindings_of_let_sexps
                            (expr_of_sexp type_env, type_of_sexp type_env)
                            bindings in
          List.fold_right ~f:(fun b e' -> LetE([b], e'))
                          ~init:(expr_of_sexp type_env body)
                          bindings'
      | [S.Atom "-"; e1; e2] ->
          SubE(expr_of_sexp type_env e1, expr_of_sexp type_env e2)
      | [S.Atom "if0"; e1; e2; e3] ->
          If0E(expr_of_sexp type_env e1, expr_of_sexp type_env e2, expr_of_sexp type_env e3)
      | (S.Atom "tup" :: es) ->
          TupE(List.map ~f:(expr_of_sexp type_env) es)
      | [S.Atom "prj"; e; S.Atom ix] ->
          let ix = try int_of_string ix
                   with Failure _ -> stx_err "integer" (S.Atom ix) in
          PrjE(expr_of_sexp type_env e, ix)
      | [S.Atom "lam"; S.List bindings; body] ->
          LamE(bindings_of_lam_vars (type_of_sexp type_env) bindings,
               expr_of_sexp type_env body)
      | [S.Atom "fix"; S.Atom x; t; e] ->
          assert_not_keyword x;
          FixE(x, type_of_sexp type_env t, expr_of_sexp type_env e)
      | S.Atom op :: _ when is_keyword op ->
          stx_err op sexp0
      | [S.Atom "Lam"; S.List new_type_vars; body] ->
          let btv = List.map ~f:type_var_of_sexp new_type_vars in
          LAME(List.length btv,
               expr_of_sexp ((List.rev btv) @ type_env)
                            body)
      | S.Atom "@" :: e :: ts ->
          APPE(expr_of_sexp type_env e, List.map ~f:(type_of_sexp type_env) ts)
      | e0 :: es ->
          AppE(expr_of_sexp type_env e0, List.map ~f:(expr_of_sexp type_env) es)

(* Parses an expression from a string, via s-expression. *)
let expr_of_string s = expr_of_sexp [] (S.of_string s)

let () =
  check_equal_any () ~name:"expr_of_string  Lam(a). (lambda(x:a). x)"
    (fun () -> expr_of_string "(Lam (a) (lam ((x a)) x))")
    (LAME (1, LamE (["x", VarT 0], VarE "x")))

let () =
  check_equal_any () ~name:"expr_of_string  (lambda(x:int  y:_). x)"
    (fun () -> expr_of_string "(lam ((x int)  y) x)")
    (LamE ([("x", IntT); ("y", HoleT)], VarE "x"))

let () =
  check_equal_any () ~name:"expr_of_string  (let ((f (lam (x) x) (-> int int))) 0)"
    (fun () -> expr_of_string "(let ((f (lam (x) x) (-> int int))) 0)")
    (LetE (["f",
            LamE (["x", HoleT], VarE "x"),
            ArrT ([IntT], IntT)],
      IntE 0))

let () =
  check_equal_any ()
    ~name:"Lam(a,r). (lam ([k : all(s). (a -> s) -> s])   k [r])"
    (fun () -> expr_of_string
                  ("(Lam (a r) " ^
                   "   (lam ((k (all (s) (-> (-> a s) s))))" ^
                   "      (@ k r)))"))
    (LAME (2,
      LamE (["k", AllT (1, ArrT ([ArrT ([VarT 2], VarT 0)], VarT 0))],
       APPE (VarE "k", [VarT 0]))))
