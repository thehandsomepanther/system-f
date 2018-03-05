open Core
open Syntax

(* Values are the result of evaluation. *)
type value =
         | IntV of int
         | TupV of value array
         | CloV of env * var list * exp
         | TypV

 and env = value Env.t

(* Value printing: *)
let string_of_value v =
  let module B = Bigbuffer in
  let buf = B.create 16 in
  let rec loop = function
    | IntV z -> B.add_string buf (string_of_int z)
    | TupV vs ->
        B.add_string buf "(tup";
      Array.iter vs ~f:(fun v -> B.add_char buf ' '; loop v);
      B.add_char buf ')'
    | CloV _ -> B.add_string buf "#<function>"
    | TypV -> B.add_string buf "#<type>"
  in loop v; B.contents buf

(* Exception thrown in cases that should not be possible in well-typed
 * programs. *)
exception Can't_happen of string

(* Evaluation, the heart of the interpreter: *)
let rec eval env = function
  | VarE var ->
      Env.lookup_exn env var
  | LetE(bindings, body) ->
      let bindings' = List.map ~f:(fun (x, e, _) -> (x, eval env e)) bindings in
      let env' = Env.extend_list env bindings' in
        eval env' body
  | IntE z ->
      IntV z
  | SubE(e1, e2) ->
      (match eval env e1, eval env e2 with
       | IntV z1, IntV z2 -> IntV (z1 - z2)
       | _ -> raise (Can't_happen "ints expected"))
  | If0E(cond, zero, non_zero) ->
      (match eval env cond with
       | IntV 0 -> eval env zero
       | IntV _ -> eval env non_zero
       | _ -> raise (Can't_happen "int expected"))
  | TupE es ->
      let vs = List.map ~f:(eval env) es in
        TupV (Array.of_list vs)
  | PrjE(e, i) ->
      (match eval env e with
       | TupV vs -> vs.(i)
       | _ -> raise (Can't_happen "tuple expected"))
  | LamE(bindings, body) ->
      CloV(env, List.map ~f:(fun (x, _) -> x) bindings, body)
  | AppE(e0, es) ->
      let v0 = eval env e0 in
      let vs = List.map ~f:(eval env) es in
        (match v0 with
         | CloV(env, xs, body) ->
            let env = Env.extend_lists env xs vs in
              eval env body
         | _ -> raise (Can't_happen "closure expected"))
  | FixE(x, (ArrT(ts, _) as t), e) ->
      let ys = Var.fresh_n (List.length ts) (fv e) in
      let v = CloV(env, ys,
                   AppE(FixE(x, t, e), List.map ~f:(fun x -> VarE x) ys)) in
        eval (Env.extend env x v) e
  | FixE(_, _, _) ->
      raise (Can't_happen "fix requires function type")
  | LAME (n, body) ->
      let ys = Var.fresh_n n (fv body) in
      CloV(env, ys, body)
  | APPE (e0, ts) ->
      let v0 = eval env e0 in
        (match v0 with
         | CloV(env, xs, body) ->
             let env = Env.extend_lists env xs (List.map ~f:(fun _ -> TypV) ts) in
             eval env body
         | _ -> raise (Can't_happen "closure expected"))
