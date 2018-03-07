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

let rec type_has_hole = function
  | IntT -> false
  | ArrT (ts, tr) -> type_has_hole tr || List.exists ts ~f:type_has_hole
  | TupT ts -> List.exists ts ~f:type_has_hole
  | VarT _ -> false
  | AllT (_, t) -> type_has_hole t
  | HoleT {contents = None} -> true
  | HoleT {contents = Some t} -> type_has_hole t

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
