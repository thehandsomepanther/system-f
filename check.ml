open Core
open Syntax

exception Type_error of string

let check_equal_t = Testing.make_check_equal ~test_module:"Check"
                                             ~to_string:Printer.type_to_string ()

(* Throws a type error contrasting what we got and expected. *)
let got_exp got exp =
  raise (Type_error ("got " ^ Printer.type_to_string got ^
                     " where " ^ exp ^ " expected"))

let got_hole msg =
  raise (Type_error ("got unelided type holes in " ^ msg))

(* Asserts that the given type is int. *)
let assert_int = function
  | IntT -> ()
  | t    -> got_exp t "int"

(* Asserts that the given type is a function type. *)
let assert_arr = function
  | ArrT _ -> ()
  | t      -> got_exp t "arrow type"

(* Asserts that two types are the same. *)
let assert_same_type t1 t2 =
  if t1 = t2
  then ()
  else raise (Type_error ("type mismatch: " ^
                          Printer.type_to_string t1 ^ " ≠ " ^
                          Printer.type_to_string t2))

let rec assert_hole_type_equals_complete_type t1 t2 =
  match t1, t2 with
    | HoleT, _ -> ()
    | ArrT (ts1, tr1), ArrT (ts2, tr2) ->
        assert_hole_type_equals_complete_type tr1 tr2;
        List.iter2_exn ~f:assert_hole_type_equals_complete_type ts1 ts2
    | TupT ts1, TupT ts2 ->
        List.iter2_exn ~f:assert_hole_type_equals_complete_type ts1 ts2
    | AllT (n1, t1), AllT (n2, t2) ->
        if n1 = n2
            then ()
            else assert_same_type t1 t2;
        assert_hole_type_equals_complete_type t1 t2
    | t1, t2 -> assert_same_type t1 t2

let assert_complete_type ?(context = "") t =
  if type_has_hole t
  then got_hole (if String.is_empty context then "" else (context ^ ": ") ^
                 Printer.type_to_string t)
  else ()

let assert_same_len n ls =
    if (List.length ls) = n
    then ()
    else raise (Type_error ("arity mismatch: expected " ^
                            string_of_int n ^
                            ", got " ^
                            string_of_int (List.length ls)))

(* Projects the `i`th element of a tuple type. *)
let prj_tup t0 i = match t0 with
  | TupT ts as t ->
      (match List.nth ts i with
       | Some t -> t
       | None   ->
           got_exp t ("tuple of size at least " ^ string_of_int (i + 1)))
  | t -> got_exp t "tuple type"

(* Unpacks an arrow type of arity `i`. *)
let un_arr i = function
  | ArrT(ts, tr) as t ->
      if i = List.length ts
      then (ts, tr)
      else got_exp t ("arrow of arity " ^ string_of_int i)
  | t -> got_exp t "arrow type"

let un_tup i = function
  | TupT ts as t ->
      if i = List.length ts
      then ts
      else got_exp t ("tuple type of " ^ string_of_int i ^ " element(s)")
  | t -> got_exp t "tuple type"

(* Unpacks an universal type. *)
let un_all = function
  | AllT (n, t) -> (n, t)
  | t -> got_exp t "universal type"

(* shift_type tau depth shift
   shift_type (forall (0 -> 1))  0  5) = forall (0 -> 6)
   shift_type (AllT (ArrT ([VarT 0], VarT 1))) 0 5
   = (AllT (ArrT ([VarT 0], VarT 6)))
*)
let rec shift_type tau depth shift =
    match tau with
    | IntT -> IntT
    | ArrT (ts, tr) ->
      ArrT (List.map ~f:(fun t -> shift_type t depth shift) ts,
            shift_type tr depth shift)
    | TupT ts ->
      TupT (List.map ~f:(fun t -> shift_type t depth shift) ts)
    | VarT m ->
      if m >= depth
          then VarT (m+shift)
          else VarT m
    | AllT (n, t) ->
      AllT (n, (shift_type t (depth+n) shift))
    | HoleT -> got_hole "shift_type"

(* type_subst tau1 [a := tau]
   type_subst  tau1 [n := tau]
   means substitue tau for (VarT n) in tau1
   where n counts how many lambdas to look (outwards)
*)
let rec type_subst tau1 n tau =
    match tau1 with
    | IntT -> IntT
    | ArrT (ts, tr) ->
        ArrT (List.map ~f:(fun t -> type_subst t n tau) ts,
              type_subst tr n tau)
    | TupT ts ->
        TupT (List.map ~f:(fun t -> type_subst t n tau) ts)
    | VarT m -> (* More Arithmetic TODO *)
        if n = m
            then shift_type tau 0 m
            else if n < m
                     then VarT (m-1)
                     else VarT m
    | AllT (m, t) ->
        AllT (m, (type_subst t (n+m) tau))
    | HoleT -> got_hole ("type_subst (" ^ Printer.type_to_string tau1 ^
                         ") " ^ string_of_int n ^ " (" ^
                         Printer.type_to_string tau ^ ")")

let rec type_substs tau1 n ts =
    match (n, ts) with
    | (-1, []) -> tau1
    | (n, (t :: ts)) -> type_substs (type_subst tau1 n t) (n-1) ts
    | _ -> invalid_arg ("type_substs: number of type variables " ^
                        "and number of supplied types do not match")

let () =
  (*
      (\. \. (0 -> 1)) (\. 1 -> 0)
   => (\. (0 -> 1))   [0  :=   (\. 1 -> 0)]
   => \. (0 -> (\. 2 -> 0))
   *)
  check_equal_t ~name:"type_subst test 1"
                (fun () ->
                  type_subst (AllT (1, ArrT ([VarT 0], VarT 1)))
                              0
                              (AllT (1, ArrT ([VarT 1], VarT 0))))
                (AllT (1, ArrT ([VarT 0], AllT (1, ArrT ([VarT 2], VarT 0)))))

let () =
  (*
      (\. \. (2 -> 1)) (\. 1 -> 0)
   => (\. (2 -> 1))   [0  :=   (\. 1 -> 0)]
   => \. (1 -> (\. 2 -> 0))
   *)
  check_equal_t ~name:"type_subst test 1"
                (fun () ->
                  type_subst (AllT (1, ArrT ([VarT 2], VarT 1)))
                              0
                              (AllT (1, ArrT ([VarT 1], VarT 0))))
                (AllT (1, ArrT ([VarT 1], AllT (1, ArrT ([VarT 2], VarT 0)))))

(* Kind checks a type in the given type environment *)
(*
   Since we only have kinds, *, type environments degenerates to
   be isomorphic to natural numbers. Moreover, as we don't allow
   the user to type in de Bruijn indices directly, this check
   becomes redundant.
 *)
let rec kc typevars_env = function
  | IntT -> ()
  | ArrT (ts, tr) ->
        List.iter ts ~f:(kc typevars_env);
        kc typevars_env tr
  | TupT ts -> List.iter ts ~f:(kc typevars_env)
  | VarT n when (n < typevars_env) -> ()
  | VarT n -> raise (Type_error ("unbound type variable: de Bruijn index " ^
                                 Int.to_string n))
  | AllT (n, t) -> kc (n+typevars_env) t
  | HoleT -> got_hole "kc"

let rec infer_elided_type_and_extend (typevars_env , termvars_env as env) xets =
  let xts = List.map ~f:(fun (x, e, t) -> (x, tc_check env e t)) xets in
  let termvars_env' = Env.extend_list termvars_env xts in
  (typevars_env, termvars_env')

(* Infers the type of a term in the given environment. We require that
   tc_infer always returns a type without any holes. *)
and tc_infer (typevars_env , termvars_env as env) = function
  | VarE x ->
      (match Env.lookup termvars_env x with
       (* Invariant: t should always be a complete type. Types with holes
          should never make their way into the environment. *)
       | Some t -> assert_complete_type ~context:("the type of " ^ x) t;
                   t
       | None   -> raise (Type_error ("unbound variable: " ^ x)))
  | LetE(xes, body) ->
      tc_infer (infer_elided_type_and_extend env xes) body
  | IntE _ -> IntT
  | SubE(e1, e2) ->
      assert_int (tc_infer env e1);
      assert_int (tc_infer env e2);
      IntT
  | If0E(e1, e2, e3) ->
      assert_int (tc_infer env e1);
      let t2 = tc_infer env e2 in
      let t3 = tc_infer env e3 in
      assert_same_type t2 t3;
      t2
  | TupE(es) ->
      TupT(List.map ~f:(tc_infer env) es)
  | PrjE(e, ix) ->
      prj_tup (tc_infer env e) ix
  | LamE(xts, body) ->
      List.iter xts
        ~f:(fun (x, t) ->
             assert_complete_type ~context:("the type of argument " ^ x ^
                                            " in (lam (" ^
                                            String.concat ~sep:" "
                                              (List.map ~f:fst xts) ^
                                            ") ...)")
                                  t;
             kc typevars_env t);
      let termvars_env' = Env.extend_list termvars_env xts in
      let tr   = tc_infer (typevars_env , termvars_env') body in
      ArrT(List.map ~f:snd xts, tr)
  | AppE(e0, es) ->
      let (tas, tr) = un_arr (List.length es) (tc_infer env e0) in
      let _         = List.map2_exn ~f:(tc_check env) es tas in
      tr
  | FixE(x, t, e) ->
      assert_complete_type t
        ~context:("the type of " ^ x ^ " in (fix " ^ x ^ " ...)");
      kc typevars_env t;
      assert_arr t;
      let termvars_env' = Env.extend termvars_env x t in
      let t'   = tc_infer (typevars_env , termvars_env') e in
      assert_same_type t t';
      t
  | LAME (n, e) ->
      let t = tc_infer (n+typevars_env, termvars_env) e in
      AllT (n, t)
  | APPE (e, ts) ->
      List.iter ts ~f:(kc typevars_env);
      let tall = tc_infer env e in
      let (n, tau1) = un_all tall in
      assert_same_len n ts;
      type_substs tau1 (n-1) ts

(* Type check the given term against the given type in the given environment.
   Return the new type with all type holes filled up. *)
and tc_check (typevars_env , termvars_env as env) exp typ =
  match (exp, typ) with
  | exp, HoleT -> tc_infer env exp
  | LetE(xes, body), typ ->
      tc_check (infer_elided_type_and_extend env xes) body typ
  | If0E(e1, e2, e3), typ ->
      let _ = tc_check env e1 IntT in
      let t2 = tc_check env e2 typ in
      let t3 = tc_check env e3 typ in
      assert_same_type t2 t3;
      t2
  | TupE(es), typ ->
      let ts = un_tup (List.length es) typ in
      TupT (List.map2_exn ~f:(tc_check env) es ts)
  | LamE(xts, body), typ ->
      let (ts, tr) = un_arr (List.length xts) typ in
      List.iter2_exn xts ts
        ~f:(fun (x, t) t' ->
              assert_complete_type ~context:("the annotated type of " ^ x ^
                                             " in (lam (" ^
                                             String.concat ~sep:" "
                                               (List.map ~f:fst xts) ^
                                             ") ...)")
                                   t';
              assert_hole_type_equals_complete_type t t');
      let new_xts = List.map2_exn ~f:(fun (x, _) t' -> x, t') xts ts in
      let termvars_env' = Env.extend_list termvars_env new_xts in
      ArrT (ts, tc_check (typevars_env , termvars_env') body tr)
  | FixE(x, HoleT, e), typ ->
      assert_arr typ;
      let termvars_env' = Env.extend termvars_env x typ in
      tc_check (typevars_env , termvars_env') e typ
  | LAME (n, e), typ ->
      let (m, t) = un_all typ in
      if n = m
          then AllT (n, tc_check (n+typevars_env, termvars_env) e t)
          else got_exp typ
                       ("Lam that takes " ^ string_of_int m ^ " type variables")
  | _ ->
      let typ' = tc_infer env exp in
      assert_hole_type_equals_complete_type typ typ';
      typ

let () =
  check_equal_t
    ~name:"tc_check propagates type informations into lambdas"
    (fun () -> tc_check (0, Env.empty)
                 (LamE ([("x", HoleT)], VarE "x"))
                 (ArrT ([IntT], IntT)))
    (ArrT ([IntT], IntT))

let () =
  check_equal_t
    ~name:"tc_check propagates type informations into Lambdas"
    (fun () -> tc_check (0, Env.empty)
                 (LAME (1, LamE ([("y", HoleT)], VarE "y")))
                 (AllT (1, ArrT ([VarT 0], VarT 0))))
    (AllT (1, ArrT ([VarT 0], VarT 0)))

let () =
  check_equal_t
    ~name:"tc_check propagates type informations back from lambda body"
    (fun () -> tc_check (0, Env.empty)
                 (LamE ([("x", HoleT)], VarE "x"))
                 (ArrT ([IntT], HoleT)))
    (ArrT ([IntT], IntT))
