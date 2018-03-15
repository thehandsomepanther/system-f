# System-F with bidirectional type inference

This project implements System-F with bidirectional type inference and type application synthesis as described in Pierce and Turner's *Local Type Inference*. Our system can handle the following cases:

- omit type annotations on lambda functions when they are at the argument position in some function application
- when applying a function of type `(all (a) (t1 -> t2))`, we will try to infer the type of arguments, then use the type of arguments to determine what `a` should be instantiated to and insert the corresponding type application
- when checking a lambda term against a universal type, we automatically insert type abstraction

## Syntax

- `(Lam (x1 x2 ... xn) e)` means `Λx1x2…xn.e`,
- `(@ e t1 t2 ... tn)` means `e[t1][t2]…[tn]` and
- `(all (a1 a2 ... an) t)` means `∀a1a2…an.t`.

## Tests

These features are demonstrated in the following tests:

- `tests/forall_annotated.stlc`: basics of System-F
- `tests/forall_bidir.stlc`: shows that we can omit type annotations on lambda functions
- `tests/application.stlc`: shows that we can omit type applications when they can be inferred
- `tests/forall_nested.stlc`: shows that we correctly implement types using De Bruijn indices


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
