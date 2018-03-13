open Core

(* Environments. See env.mli for interface. *)

type var = Var.t

(* We'll represent environments as association lists where earlier
 * bindings shadow later ones. *)
type 'a t = (var * 'a) list

exception Unbound_variable of var

let empty = []

let map g xs = List.map ~f:(fun (x, v) -> (x, g v)) xs

let rec lookup env x = match env with
  | [] -> None
  | (y, v) :: rest -> if x = y then Some v else lookup rest x

let lookup_exn env x =
  match lookup env x with
  | None   -> raise (Unbound_variable x)
  | Some v -> v

let extend env x v =
  (x, v) :: env

let extend_list env =
  List.fold ~f:(fun env' (x, v) -> extend env' x v) ~init:env

let extend_lists env =
  List.fold2_exn ~f:extend ~init:env
