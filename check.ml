open Core
open Syntax

exception Type_error of string

let check_equal_t = Testing.make_check_equal ~test_module:"Check"
                                             ~to_string:Syntax.string_of_type ()

(* Throws a type error contrasting what we got and expected. *)
let got_exp got exp =
  raise (Type_error ("got " ^ Syntax.string_of_type got ^
                     " where " ^ exp ^ " expected"))

let got_hole msg =
  raise (Type_error ("got type with holes in " ^ msg))

(* Asserts that the given type is int. *)
let assert_int t0 = match view_type t0 with
  | IntT -> ()
  | t    -> got_exp t "int"

(* Asserts that the given type is a function type. *)
let assert_arr t0 = match view_type t0 with
  | ArrT _ -> ()
  | t      -> got_exp t "arrow type"

(* Assert that r does not appear anywhere in t (using physical equality) *)
let assert_holes_not_occurs_in r t =
    if ref_occurs_in r t
        then failwith ("Occurrence check failed: the reference holding " ^
                       string_of_type (HoleT r) ^
                       " appears in the type " ^
                       string_of_type t)
        else ()

(* Asserts that two types are the same. *)
let assert_same_type t1 t2 =
  let rec do_assert = function
    | t1, HoleT {contents = Some t2} -> do_assert (t1, t2)
    | HoleT {contents = Some t1}, t2 -> do_assert (t1, t2)
    (* From now on, both sides are _not_ of form HoleT {contents = Some _} *)
    | HoleT ({contents = None}),       HoleT ({contents = None}) ->
       raise (Type_error ("cannot resolve type holes in " ^
                          Syntax.string_of_type t1 ^ " and " ^
                          Syntax.string_of_type t2))
    (* If the above pattern does not match, then at least one side is _not_
       of form (HoleT {contents = None}). Combining with the first two
       patterns, we know that at least one side is not (HoleT _). *)
    | HoleT ({contents = None} as r1), t2 ->
        assert_holes_not_occurs_in r1 t2;
        r1 := Some t2
    | t1,                              HoleT ({contents = None} as r2) ->
        assert_holes_not_occurs_in r2 t1;
        r2 := Some t1
    | IntT, IntT -> ()
    | ArrT (ts1, tr1), ArrT (ts2, tr2) when List.length ts1 = List.length ts2 ->
        List.iter2_exn ~f:(fun t1 t2 -> do_assert (t1, t2)) ts1 ts2;
        do_assert (tr1, tr2)
    | TupT ts1, TupT ts2 when List.length ts1 = List.length ts2 ->
        List.iter2_exn ~f:(fun t1 t2 -> do_assert (t1, t2)) ts1 ts2;
    | VarT n1, VarT n2 when n1 = n2 -> ()
    | AllT (n1, t1), AllT (n2, t2) when n1 = n2 ->
        do_assert (t1, t2)
    | _ ->
       raise (Type_error ("type mismatch: " ^
                          Syntax.string_of_type t1 ^ " ≠ " ^
                          Syntax.string_of_type t2))
  in do_assert (t1, t2)

let assert_complete_type ?(context = "") t =
  if type_has_hole t
  then got_hole ((if String.is_empty context then "" else (context ^ ": ")) ^
                 Syntax.string_of_type t)
  else ()

let assert_same_len n ls =
    if (List.length ls) = n
    then ()
    else raise (Type_error ("arity mismatch: expected " ^
                            string_of_int n ^
                            ", got " ^
                            string_of_int (List.length ls)))

(* Projects the `i`th element of a tuple type. *)
let prj_tup t0 i = match view_type t0 with
  | TupT ts as t ->
      (match List.nth ts i with
       | Some t -> t
       | None   ->
           got_exp t ("tuple of size at least " ^ string_of_int (i + 1)))
  | t -> got_exp t "tuple type"

(* Unpacks an arrow type of arity `i`. *)
let un_arr i t0 = match view_type t0 with
  | ArrT(ts, tr) as t ->
      if i = List.length ts
      then (ts, tr)
      else got_exp t ("arrow of arity " ^ string_of_int i)
  | t -> got_exp t "arrow type"

let un_tup i t0 = match view_type t0 with
  | TupT ts as t ->
      if i = List.length ts
      then ts
      else got_exp t ("tuple type of " ^ string_of_int i ^ " element(s)")
  | t -> got_exp t "tuple type"

(* Unpacks an universal type. *)
let un_all t0 = match view_type t0 with
  | AllT (n, t) -> (n, t)
  | t -> got_exp t "universal type"

(* Generates a list of n HoleEs *)
let gen_holes n = List.init n ~f:(fun _ -> HoleT(ref None))

let rec inst_all holes n = function
  | IntT -> IntT
  | ArrT (ts, tr) -> ArrT(List.map ~f:(inst_all holes n) ts, (inst_all holes n) tr)
  | TupT ts -> TupT(List.map ~f:(inst_all holes n) ts)
  | VarT m ->
      if m < n
      then VarT(m)
      else List.nth_exn holes (m - n)
  | AllT (m, t) -> AllT(n, inst_all holes (n + m) t)
  | HoleT {contents = Some t} -> inst_all holes n t
  | HoleT {contents = None} -> got_hole "inst_all"

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
    | HoleT {contents = Some t} ->
      shift_type t depth shift
    | HoleT {contents = None} -> got_hole "shift_type"

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
    | HoleT {contents = Some t} ->
        type_subst t n tau
    | HoleT {contents = None} ->
               got_hole ("type_subst (" ^ Syntax.string_of_type tau1 ^
                         ") " ^ string_of_int n ^ " (" ^
                         Syntax.string_of_type tau ^ ")")

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
  | HoleT {contents = Some t} -> kc typevars_env t
  | HoleT {contents = None} -> got_hole "kc"

let rec infer_elided_type_and_extend (typevars_env , termvars_env as env) xets =
  let xts = List.map xets
              ~f:(fun (x, e, t) ->
                   tc_check env e t;
                   assert_complete_type ~context:("the type of let-binding " ^ x) t;
                   (x, t)) in
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
  | AppE(HoleE e0, es) as e ->
      (match view_type (tc_infer env (!e0)) with
        | AllT (n, ArrT(ts1, tr1)) ->
            let tas = List.map ~f:(tc_infer env) es in
            let holes = gen_holes n in
            let ts2 = List.map ~f:(inst_all holes 0) ts1 in
            let tr2 = inst_all holes 0 tr1 in
            let tr  = HoleT (ref None) in
            assert_same_type (ArrT (ts2, tr2)) (ArrT (tas, tr));
            List.iter holes
              ~f:(assert_complete_type
                   ~context:("inferred type application of " ^
                             Syntax.string_of_type (AllT (n, ArrT(ts1, tr1))) ^
                             " to " ^
                             String.concat ~sep:", " (List.rev_map ~f:Syntax.string_of_type holes)));
            e0 := APPE((!e0), List.rev holes);
            (* Just sanity check; should not go in to infinite loop since
               we have instantiated the type parameters. *)
            tc_infer env e
        | t0 ->
            let (tas, tr) = un_arr (List.length es) t0 in
            let _         = List.map2_exn ~f:(tc_check env) es tas in
            tr)
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
      let termvars_env' =
        Env.map (fun _ t -> shift_type t 0 1) termvars_env in
      let t = tc_infer (n+typevars_env, termvars_env') e in
      AllT (n, t)
  | APPE (e, ts) ->
      List.iter ts ~f:(kc typevars_env);
      let tall = tc_infer env e in
      let (n, tau1) = un_all tall in
      assert_same_len n ts;
      type_substs tau1 (n-1) ts
  | HoleE e ->
      tc_infer env (!e)

(* Type check the given term against the given type in the given environment.
   Return the new type with all type holes filled up. *)
and tc_check (typevars_env , termvars_env as env) exp typ =
  match (exp, typ) with
  | exp, HoleT ({contents = None} as r) -> r := Some (tc_infer env exp)
  | exp, HoleT ({contents = Some t}) -> tc_check env exp t
  | LetE(xes, body), typ ->
      tc_check (infer_elided_type_and_extend env xes) body typ
  | If0E(e1, e2, e3), typ ->
      tc_check env e1 IntT;
      tc_check env e2 typ;
      tc_check env e3 typ
  | TupE(es), typ ->
      let ts = un_tup (List.length es) typ in
      List.iter2_exn ~f:(tc_check env) es ts
  | LamE(xts, body), typ ->
      let (ts, tr) = un_arr (List.length xts) typ in
      List.iter2_exn xts ts
        ~f:(fun (x, t) t' ->
              assert_same_type t t';
              assert_complete_type ~context:("the type of " ^ x ^
                                             " in (lam (" ^
                                             String.concat ~sep:" "
                                               (List.map ~f:fst xts) ^
                                             ") ...)")
                                   t);
      let termvars_env' = Env.extend_list termvars_env xts in
      tc_check (typevars_env , termvars_env') body tr
  | FixE(x, HoleT ({contents = None} as r), e), typ ->
      assert_holes_not_occurs_in r typ;
      r := Some typ;
      assert_arr typ;
      let termvars_env' = Env.extend termvars_env x typ in
      tc_check (typevars_env , termvars_env') e typ
  | LAME (n, e), typ ->
      let (m, t) = un_all typ in
      if n = m
          then
            let termvars_env' =
              Env.map (fun _ t -> shift_type t 0 1) termvars_env in
            tc_check (n+typevars_env, termvars_env') e t
          else got_exp typ
                       ("Lam that takes " ^ string_of_int m ^ " type variables")
  | HoleE e, typ ->
      tc_check env (!e) typ
  | exp, typ ->
      let typ' = tc_infer env exp in
      assert_same_type typ typ'

let () =
  check_equal_t
    ~name:"tc_check propagates type information into lambdas"
    (fun () -> let t = ArrT ([IntT], IntT) in
               tc_check (0, Env.empty)
                 (LamE ([("x", HoleT (ref None))], VarE "x"))
                 t;
               t)
    (ArrT ([IntT], IntT))

let () =
  check_equal_t
    ~name:"tc_check propagates type information into Lambdas"
    (fun () -> let t = AllT (1, ArrT ([VarT 0], VarT 0)) in
               tc_check (0, Env.empty)
                  (LAME (1, LamE ([("y", HoleT (ref None))], VarE "y")))
                  t;
               normalize_complete_type t)
    (AllT (1, ArrT ([VarT 0], VarT 0)))

let () =
  check_equal_t
    ~name:"tc_check propagates type information back from lambda body"
    (fun () -> let t = ArrT ([IntT], HoleT (ref None)) in
               tc_check (0, Env.empty)
                 (LamE ([("x", HoleT (ref None))], VarE "x"))
                 t;
               normalize_complete_type t)
    (ArrT ([IntT], IntT))

let () =
  check_equal_t
    ~name:"tc_infer correctly opens a term inside big Lambda"
    (fun () ->
      tc_infer (0, Env.empty)
        (LAME (1,
          LamE (["x", VarT 0],
            LAME (1,
              LamE (["y", VarT 0],
                VarE "x"))))))
    (* This is the representation of type ∀ α. α → ∀ β. β → α,
       the 'delayed' versino of ∀ α β. α → β → α *)
    (AllT (1, ArrT ([VarT 0], AllT (1, (ArrT ([VarT 0], VarT 1))))))

let () =
  (* The tc_check version of the tc_infer test above. *)
  check_equal_t
    ~name:"tc_check correctly opens a term inside big Lambda"
    (fun () ->
      let t = AllT (1,
                ArrT ([VarT 0], AllT (1,
                                  (ArrT ([VarT 0], HoleT (ref None)))))) in
      tc_check (0, Env.empty)
        (LAME (1,
          LamE (["x", HoleT (ref None)],
            LAME (1,
              LamE (["y", HoleT (ref None)],
                VarE "x")))))
        t;
      normalize_complete_type t)
    (AllT (1, ArrT ([VarT 0], AllT (1, (ArrT ([VarT 0], VarT 1))))))
