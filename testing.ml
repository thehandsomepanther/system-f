open Core

exception Check_equal_fail of string * string * string * string

let make_check_equal ?(test_module = "")
                     ?(to_string = (fun _ -> "#<abstr>"))
                     ()
                     ?(name = "")
                     actual
                     expected =
    if actual = expected
      then ()
      else raise (Check_equal_fail (test_module,
                                    name,
                                    to_string actual,
                                    to_string expected))
