open Core

(* Variables *)
type var = Var.t

(* Types *)
(* Invariant: refs in the HoleT must _NOT_ be shared. *)
type typ = IntT
         | ArrT of typ list * typ
         | TupT of typ list
         | VarT of int
         | AllT of int * typ
         | HoleT of typ option ref

(* Expressions *)
type exp =
         | VarE of var
         | LetE of (var * exp * typ) list * exp
         | IntE of int
         | SubE of exp * exp
         | If0E of exp * exp * exp
         | TupE of exp list
         | PrjE of exp * int
         | LamE of (var * typ) list * exp
         | AppE of exp * exp list
         | FixE of var * typ * exp
         | LAME of int * exp
         | APPE of exp * typ list
         | HoleE of exp ref

module S = Sexp

(* Converts a type to its s-expression representation. *)
let rec sexp_of_sexp type_env = function
  | IntT ->
      S.Atom "int"
  | ArrT(ts, tr) ->
      S.List (S.Atom "->" :: List.map ~f:(sexp_of_sexp type_env) (ts @ [tr]))
  | TupT ts ->
      S.List (S.Atom "*" :: List.map ~f:(sexp_of_sexp type_env) ts)
  | VarT n ->
      (match List.nth type_env n with
        | Some x -> S.Atom x
        | None -> S.Atom ("?" ^ Int.to_string n))
  | AllT (n, t) ->
      let tvs = Var.fresh_n n (Var.Set.of_list type_env) in
      S.List [S.Atom "all";
              S.List (List.map ~f:(fun s -> S.Atom s) tvs);
              sexp_of_sexp ((List.rev tvs) @ type_env) t]
  | HoleT {contents = Some t} ->
      sexp_of_sexp type_env t
  | HoleT {contents = None} ->
      S.Atom "_"

(* Prints a type as a string. *)
let string_of_type t = S.to_string_hum (sexp_of_sexp [] t)

(* Reveal the outtermost constructor, quotient HoleT links *)
let rec view_type = function
  | HoleT {contents = Some t} -> view_type t
  | t -> t

let rec type_has_hole = function
  | IntT -> false
  | ArrT (ts, tr) -> type_has_hole tr || List.exists ts ~f:type_has_hole
  | TupT ts -> List.exists ts ~f:type_has_hole
  | VarT _ -> false
  | AllT (_, t) -> type_has_hole t
  | HoleT {contents = None} -> true
  | HoleT {contents = Some t} -> type_has_hole t

(* Check if r appears anywhere in t (using physical equality) *)
let ref_occurs_in r t =
  let rec do_check = function
    | IntT -> false
    | ArrT (ts, tr) -> List.exists ~f:do_check (tr :: ts)
    | TupT ts -> List.exists ~f:do_check ts
    | VarT _ -> false
    | AllT (_, t) -> do_check t
    | HoleT r' ->
        if phys_equal r r'
        then true
        else (match !r' with None -> false | Some t -> do_check t)
  in do_check t

(* Given a type without holes, remove all HoleT {contents = Some _} indirections. *)
let rec normalize_complete_type = function
  | IntT -> IntT
  | ArrT (ts, tr) -> ArrT (List.map ~f:normalize_complete_type ts,
                           normalize_complete_type tr)
  | TupT ts -> TupT (List.map ~f:normalize_complete_type ts)
  | VarT n -> VarT n
  | AllT (n, t) -> AllT (n, normalize_complete_type t)
  | HoleT {contents = Some t} -> normalize_complete_type t
  | HoleT {contents = None} ->
      failwith "got type with holes in normalize_complete_type"

(* Computes the free variables of an expression. *)
let rec fv e0 =
  let module Set = Var.Set in
  let remove_bindings remv bindings fvset =
    List.fold ~f:Set.remove ~init:fvset (List.map ~f:remv bindings) in
  match e0 with
  | VarE x -> Set.singleton x
  | LetE(bindings, body) -> remove_bindings (fun (x,_,_) -> x) bindings (fv body)
  | IntE _ -> Set.empty
  | SubE(e1, e2) -> Set.union (fv e1) (fv e2)
  | If0E(e1, e2, e3) -> Set.union_list [fv e1; fv e2; fv e3]
  | TupE es -> Set.union_list (List.map ~f:fv es)
  | PrjE(e, _) -> fv e
  | LamE(bindings, body) -> remove_bindings fst bindings (fv body)
  | AppE(e, es) -> Set.union_list (List.map ~f:fv (e :: es))
  | FixE(x, _, e) -> Set.remove (fv e) x
  | LAME (_, e) -> fv e
  | APPE (e, _) -> fv e
  | HoleE e -> fv (!e)
