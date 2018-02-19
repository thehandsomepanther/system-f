# To Do

1. Measure the run time of `examples/factorial.stlc`. Computing the
   factorial of 5 is pretty fast. How about 8?

2. You can make factorial go faster by taking advantage of your
   computer's multiplication instruction. To do so, modify the
   interpeter to add a multiplication form that is interpreted by
   OCaml's multiplication operation.

3. Modify `examples/factorial.stlc` to take advantage of the new
   multiplication built-in, and time it again.

# system f & bidirectional checking

* 1 type vars -> many type vars
* add bidirectional inference to omit lambda types
* add bidirectional inference to infer type applications
