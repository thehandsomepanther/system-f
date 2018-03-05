open Core

exception Check_equal_fail of string * string * string * string
exception Check_equal_exc of string * string * string * string

(*
    make_check_equal : ?string -> ?('a -> string) -> unit -> ?string ->
                       (unit -> 'a) -> 'a ->
                       unit
 *)
let make_check_equal ?(test_module = "")
                     ?(to_string = (fun _ -> "#<abstr>"))
                     ()
                     ?(name = "")
                     compute_actual
                     expected =
    let actual = (try compute_actual ()
                  with any_exn ->
                      raise (Check_equal_exc (test_module,
                                              name,
                                              to_string expected,
                                              Exn.to_string any_exn))) in
    if actual = expected
      then ()
      else raise (Check_equal_fail (test_module,
                                    name,
                                    to_string actual,
                                    to_string expected))
