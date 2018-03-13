# STLC Interpreter

This directory contains an interpreter and type checker for the
simply-typed λ calculus, written in OCaml.

## Installation

First install OPAM, the OCaml package manager; this will install OCaml.
On Linux and OS X, there are [binary distributions][OPAM] available, and
it should be easy. Windows is a bit harder because it isn't directly
supported by OPAM, but you can [install via Cygwin][OPAM-Cygwin], which
sets up a Linux environment on Windows.

Then, use OPAM to install the Core libraries:

<pre>
$ opam install core
</pre>

Once OPAM and Core are installed, it should be possible to build in this
directory by running make:

<pre>
$ make
</pre>

## Running

Run

<pre>
$ make test
</pre>

to run automated tests, or

<pre>
$ ./main.byte
</pre>

to get a REPL. See examples in the `tests/` subdirectory.

## Testing in REPL

Use the following directives in `coretop` to load all required modules.

```
$ coretop
#mod_use "var.ml";;
#mod_use "testing.ml";;
#mod_use "env.ml";;
#mod_use "syntax.ml";;
#use "check.ml";;
```

[OPAM]: https://opam.ocaml.org/doc/Install.html

[OPAM-Cygwin]: https://fdopen.github.io/opam-repository-mingw/installation/
