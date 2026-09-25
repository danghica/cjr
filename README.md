# cjr

Mechanization of the performance-parity Cangjie fragment (Cangjie Radical) in Coq with [Iris](https://iris-project.org/).

The language is sequential and monomorphic. Mutable `var` bindings are stack slots, `CPointer` blocks are a raw word heap, and final class fields live on a separate object heap. The program logic is Iris's weakest precondition over an evaluation-context semantics.

## Build

The development is checked with Coq 8.20.1, coq-stdpp 1.12.0, and coq-iris 4.4.0.

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.20.1 coq-stdpp.1.12.0 coq-iris.4.4.0
eval $(opam env)
coq_makefile -f _CoqProject -o Makefile
make
```

## Layout

- `theories/lang.v` — syntax, three-region state, small-step semantics
- `theories/primitive_laws.v` — points-to facts and weakest-precondition rules
- `theories/adequacy.v` — a proved specification does not get stuck
- `theories/examples/` — local arithmetic, stack structs, raw blocks, classes, framing, and a hand-written vtable

Generics, inheritance, `enum`/`match`, concurrency, garbage collection, and a translation from full Cangjie are out of scope.
