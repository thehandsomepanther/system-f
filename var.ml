open Core

(* Variables are represented as strings. *)
type t = string

(* Sets of variables are sets of strings. *)
module Set = Set.Make(String)

(* Removes any digits from the end of a string. *)
let remove_trailing_digits x =
  let cs = String.to_list x in
  let cs' = List.rev (List.drop_while ~f:Char.is_digit (List.rev cs)) in
    String.concat (List.map ~f:(String.make 1) cs')

let fresh suggestion0 fvset =
  let suggestion = remove_trailing_digits suggestion0 in
  let okay x = not (Set.mem fvset x) in
  let rec count_from i =
    let x = suggestion ^ string_of_int i in
    if okay x then x else count_from (i + 1) in
  if okay suggestion then suggestion else count_from 0

let fresh_list suggestions fvset =
  let each (fvset', acc) x =
    let x' = fresh x fvset' in
    (Set.add fvset' x', x' :: acc) in
  List.rev (snd (List.fold ~f:each ~init:(fvset, []) suggestions))

(* Generates a list of length `n0`, counting from `start` to `limit` and
 * repeating as necessary. *)
let count_cycle ?(start = 0) ~limit n0 =
  let rec loop i n acc =
    match n with
    | 0 -> List.rev acc
    | _ when i < limit -> loop (i + 1) (n - 1) (i :: acc)
    | _ -> loop start n acc
  in loop start n0 []

(* Makes a string list of length `n` that repeats the alphabet as many
 * times as necessary. *)
let make_list n =
  List.map ~f:(fun i -> String.make 1 (Char.of_int_exn i))
           (count_cycle ~start:97 ~limit:(97 + 26) n)

let fresh_n n fvset = fresh_list (make_list n) fvset
