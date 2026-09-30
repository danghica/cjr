# cjr

This is a mechanization of a performance-parity Cangjie fragment (called Cangjie Radical) in Coq with [Iris](https://iris-project.org/). 
This allows the formal specification and proof of cjr programs using Iris.  

The language is sequential and monomorphic. Mutable `var` bindings are stack slots, `CPointer` blocks are a raw word heap, and final class fields live on a separate object heap. The program logic is Iris's weakest precondition over an evaluation-context semantics.

Actual compilable and executable Cangjie code is extracted from the the verification files using a Galina printer. 

## Build

The development is checked with Coq 8.20.1, coq-stdpp 1.12.0, and coq-iris 4.4.0.

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.20.1 coq-stdpp.1.12.0 coq-iris.4.4.0
eval $(opam env)
coq_makefile -f _CoqProject -o Makefile
make
make verify    # optional: coqchk + Print Assumptions audit (see Makefile.local-late)
```

Coq is invoked with `-w +admitted-proof` (and a few other promoted warnings in `_CoqProject`), so `Admitted` and similar bypasses fail at compile time. We do not use `-w +all` here: on Coq 8.20 it turns a benign Iris/stdlib `Fin.vo` notice into a build error. `make verify` runs `coqchk` on all `.vo` files (Coq 8.20 has no `--admit-opaque` switch; opaque `Qed` proofs are checked unless you pass `-admit`) and checks that representative adequacy theorems print **Closed under the global context** (`theories/verify_assumptions.v`).

## Layout

- `theories/lang.v` — syntax, three-region state, small-step semantics
- `theories/primitive_laws.v` — points-to facts and weakest-precondition rules
- `theories/adequacy.v` — a proved specification does not get stuck
- `theories/examples/` — local arithmetic, stack structs, raw blocks, classes, framing, and a hand-written vtable

Generics, inheritance, `enum`/`match`, concurrency, garbage collection, and a translation from full Cangjie are out of scope.

## Extracted Cangjie

`make cj` prints each file in `theories/examples/` to `generated/cj/`. Counts are `wc -l` of the whole file. A `.v` file includes the program, the specification, and the proofs.

| Spec | Lines | Extracted | Lines | Spec / extracted |
|---|---:|---|---:|---:|
| `theories/examples/arith.v` | 78 | `generated/cj/arith.cj` | 18 | 4.3 |
| `theories/examples/struct_upd.v` | 57 | `generated/cj/struct_upd.cj` | 27 | 2.1 |
| `theories/examples/cell.v` | 35 | `generated/cj/cell.cj` | 15 | 2.3 |
| `theories/examples/swap.v` | 40 | `generated/cj/swap.cj` | 18 | 2.2 |
| `theories/examples/sum_block.v` | 90 | `generated/cj/sum_block.cj` | 20 | 4.5 |
| `theories/examples/class_upd.v` | 45 | `generated/cj/class_upd.cj` | 23 | 2.0 |
| `theories/examples/frame_call.v` | 37 | `generated/cj/frame_call.cj` | 20 | 1.9 |
| `theories/examples/vtable.v` | 70 | `generated/cj/vtable.cj` | 33 | 2.1 |
| `theories/examples/list.v` | 227 | `generated/cj/list.cj` | 54 | 4.2 |
| `theories/examples/array.v` | 354 | `generated/cj/array.cj` | 39 | 9.1 |
| `theories/examples/array_list.v` | 2416 | `generated/cj/array_list.cj` | 153 | 15.8 |
| `theories/examples/qsort.v` | 1749 | `generated/cj/qsort_array.cj` (76), `generated/cj/qsort_array_list.cj` (153) | 229 | 7.6 |
| `theories/examples/hash_map.v` | 2395 | `generated/cj/hash_map.cj` | 375 | 6.4 |
| **Total** | **7593** | | **1024** | **7.4** |
