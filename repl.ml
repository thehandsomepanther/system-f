open Core

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

