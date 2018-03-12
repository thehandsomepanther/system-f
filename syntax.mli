open Core

(* Variables *)
type var = Var.t

(* Types *)
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

val string_of_type : typ -> string
val view_type : typ -> typ
val type_has_hole : typ -> bool
val ref_occurs_in : typ option ref -> typ -> bool
val normalize_complete_type : typ -> typ
val fv : exp -> Var.Set.t
