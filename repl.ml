open Core

let check_equal_t = Testing.make_check_equal ~test_module:"Repl"
                                             ~to_string:Printer.type_to_string ()

let check_equal_any () = Testing.make_check_equal ~test_module:"Repl" ()

(* Prints a message to stderr and flushes it. *)
let warn s =
  Out_channel.output_string Out_channel.stderr s;
  Out_channel.flush Out_channel.stderr

(* Reads one expression from stdin. Tries again on error, but returns
 * None on EOF. *)
let rec read () =
  try
    print_string "> ";
    Out_channel.flush stdout;
    Some (Parser.expr_of_sexp (Sexp.input_sexp In_channel.stdin))
  with
  | End_of_file -> None
  | Sexp.Parse_error(e) ->
      warn ("Read error: " ^ e.err_msg ^ "\n");
      read ()
  | Parser.Bad_syntax(exp, got) ->
      warn ("Syntax error: expecting " ^ exp ^ ", got:\n");
      Sexp.output_hum_indent 2 Out_channel.stderr got;
      warn "\n";
      read ()

(* A read-eval-print-loop. *)
let rec repl () =
  match read () with
  | None -> ()
  | Some e ->
      (try
        let t = Check.tc Env.empty e in
        print_string (" : " ^ Printer.type_to_string t ^ "\n");
        let v = Eval.eval Env.empty e in
        print_string ("-> " ^ Eval.string_of_value v ^ "\n");
      with Check.Type_error msg ->
        warn ("type error: " ^ msg ^ "\n"));
      repl ()

let () =
  check_equal_any () (fun () -> Parser.expr_of_string "(Lam (α β) 5)")
                     (LAME(2, IntE 5))

let () =
  check_equal_t (fun () -> Check.tc Env.empty (LAME (2, (IntE 5))))
                (Syntax.AllT (2, Syntax.IntT))
