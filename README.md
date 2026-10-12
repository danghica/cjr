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

Coq is invoked with `-w +admitted-proof` (and a few other promoted warnings in `_CoqProject`), and `make verify` additionally rejects `Admitted` and declared `Axiom` bypasses in the source. We do not use `-w +all` here: on Coq 8.20 it turns a benign Iris/stdlib `Fin.vo` notice into a build error. `make verify` runs `coqchk` on all `.vo` files (Coq 8.20 has no `--admit-opaque` switch; opaque `Qed` proofs are checked unless you pass `-admit`) and checks that representative adequacy theorems print **Closed under the global context** (`theories/verify_assumptions.v`).

`make verify` streams its complete build and check output to the terminal and
`build/verify.log`, with UTC start/end times and the exit status. The latest log
is version controlled; include it in commits after verification. Logging does
not change a failed check into a successful one. Override the destination with
`make verify VERIFY_LOG=/path/to/verify.log` for temporary runs.

User prompts are recorded in `logs/prompts.txt` with UTC recording timestamps.
Repository agent guidance requests logging each new prompt using
`python3 scripts/log_prompt.py` with its exact text on standard input. This is
an agent workflow, not a desktop-wide prompt interception hook.

## Readable Rocq specifications

`rocq-readable` generates linked, proof-free HTML from Rocq declarations, with
a dependency hierarchy, a flat Index, and cached English explanations through
the user's Codex CLI (`--explanations offline` disables model requests). Formal
rendering remains deterministic. Its project boundary is the
current directory and its subdirectories: it discovers all `.v` files, including
ones absent from `_CoqProject`. Library names stay unlinked. See
[the renderer documentation](tools/rocq_readable/README.md) for dictionary editing,
scope formatting, and coverage limitations.

```sh
opam install coq-lsp.0.2.5+8.20
eval $(opam env)
make                         # refresh dependencies and symbol information
make readable                # example/*/docs/rocq/ and shared generated/spec-html/
make readable-test            # includes real-backend integration tests
./rocq-readable render example/misc/rocq/swap.v --name swap_wp --output /tmp/swap.html
```

The backend is optional for the proof build. Installation can rebuild Coq's
dependencies; if existing `.vo` files subsequently report inconsistent
assumptions, rebuild this development with `make -B`.

## Layout

- `theories/lang.v` — syntax, three-region state, small-step semantics
- `theories/primitive_laws.v` — points-to facts and weakest-precondition rules
- `theories/adequacy.v` — a proved specification does not get stuck
- `example/` — self-contained example directories: quadtree, array, array_list, list, list_rev, qsort, hash_map, most_frequent, and misc. Each owns its Rocq sources, generated code, tests, available benchmarks, and offline reports.
- `tools/extraction/rocq/` — shared printer and aggregate extraction driver

Open [all example reports](example/index.html). `make readable EXPLANATIONS=offline` regenerates the example and shared-library pages using existing explanation caches; `make project-report EXPLANATIONS=offline` also assembles reports. `make test` runs the runtime suites; `make benchmark` explicitly runs timed benchmarks.

Generics, inheritance, `enum`/`match`, concurrency, garbage collection, and a translation from full Cangjie are out of scope.

## Extracted Cangjie

`make cj` prints each file in `example/*/rocq/` to `example/*/extracted/`. Counts are `wc -l` of the whole file. A `.v` file includes the program, the specification, and the proofs.

| Spec | Lines | Extracted | Lines | Spec / extracted |
|---|---:|---|---:|---:|
| `example/misc/rocq/arith.v` | 94 | `example/misc/extracted/arith.cj` | 18 | 5.2 |
| `example/misc/rocq/struct_upd.v` | 57 | `example/misc/extracted/struct_upd.cj` | 27 | 2.1 |
| `example/misc/rocq/cell.v` | 35 | `example/misc/extracted/cell.cj` | 15 | 2.3 |
| `example/misc/rocq/swap.v` | 40 | `example/misc/extracted/swap.cj` | 18 | 2.2 |
| `example/misc/rocq/sum_block.v` | 90 | `example/misc/extracted/sum_block.cj` | 20 | 4.5 |
| `example/misc/rocq/class_upd.v` | 45 | `example/misc/extracted/class_upd.cj` | 23 | 2.0 |
| `example/misc/rocq/frame_call.v` | 37 | `example/misc/extracted/frame_call.cj` | 20 | 1.9 |
| `example/misc/rocq/vtable.v` | 70 | `example/misc/extracted/vtable.cj` | 33 | 2.1 |
| `example/list/rocq/list.v` | 227 | `example/list/extracted/list.cj` | 54 | 4.2 |
| `example/list_rev/rocq/list_rev.v` | 287 | `example/list_rev/extracted/list_rev.cj` | 65 | 4.4 |
| `example/array/rocq/array.v` | 354 | `example/array/extracted/array.cj` | 39 | 9.1 |
| `example/array_list/rocq/array_list.v` | 2340 | `example/array_list/extracted/array_list.cj` | 127 | 18.4 |
| `example/qsort/rocq/qsort.v` | 1749 | `example/qsort/extracted/qsort_array.cj` (76), `example/qsort/extracted/qsort_array_list.cj` (135) | 211 | 8.3 |
| `example/hash_map/rocq/hash_map.v` | 2684 | `example/hash_map/extracted/hash_map.cj` | 245 | 11.0 |
| **Total** | **8109** | | **915** | **8.9** |


The shared `hm_tactics.v` evaluation-context automation adds 110 supporting lines outside the example counts above.

## In-place list reversal

`example/list_rev/rocq/list_rev.v` reuses `list.is_list`, reverses existing cons links, and proves `reverse_spec` and `reverse_twice_spec` without admissions or additional axioms. The loop theorem establishes an empty remainder and a reversed accumulator. One fresh empty sentinel separates the two owned chains.

The tutorial includes a detailed subsection for each definition and lemma, complete checked proof listings, and explanations of the invariant, each memory step, the induction, and the final scope cleanup. `make cj` includes the standalone `example/list_rev/extracted/list_rev.cj`; `example/list_rev/test/list_rev_test.cj` covers six runtime cases, including changes observed through references to the original nodes. See `paper/test-history.md` for the dated results.

## Verified hash map

`example/hash_map/rocq/hash_map.v` now proves every operation and its supporting kernels without admissions. A bounded probe wraps indexes safely, searches beyond tombstones for existing keys, and returns a precise finite-map lookup result. Insertion grows only for a missing key at the half-full limit; rehashing preserves every live entry, skips tombstones, and restores placement under doubled capacity. The stored size agrees with the finite map throughout.

The tutorial explains the representation, remainder and probe invariants, array ownership, insertion and removal proofs, rehash induction, and client compositions in detail. The generated implementation uses `ProbeResult` and `Int64Option` value structs. `example/hash_map/test/hash_map_test.cj` contains 17 runtime cases, including collisions, wraparound, negative and extreme Int64 keys, signed remainder, zero-filled allocation, iterative lookup, zero values, tombstone reuse, and repeated growth. `make verify` audits the public contracts and supporting kernels in addition to the existing adequacy and reversal theorems.

Primitive signed remainder (`RemOp`, printed as `%`) follows division truncated toward zero. Its WP rule requires a nonzero divisor. HashMap bucket normalization now uses one remainder and at most one addition, with a proof that the result equals mathematical modulo for positive capacity; it no longer iterates in proportion to the key magnitude. Collision chains still use linear probing without hash mixing.

`add_spec` and its client theorems retain the resulting capacity existentially because insertion can grow. `grow(minCap)` performs one doubling; the retained argument does not promise arbitrary minimum capacity. The CJR integer model is unbounded; the proof does not establish absence of `Int64` overflow for arbitrary machine inputs.

# Methodology 


## Overview and Core Problem

This project evaluates the verifiability of agentic code generation by addressing a specific research question: **Can agent-generated code be trusted, and what constitutes the minimal specification and artifact surface that requires manual inspection by a qualified human?**

The project is structured into two components:

1. **The verification framework**: A mechanized operational semantics and separation logic for a core fragment of Cangjie, formalized in Rocq using the Iris framework.
2. **The synthesized examples**: Individual data structures and algorithms synthesized end-to-end from informal prompts into verified Rocq developments, which are subsequently extracted to Cangjie for compilation, testing, and benchmarking.

Both components are generated using language model agents (such as Codex or Cursor). The manual inspection burden differs substantially between the foundational framework and the individual synthesized examples.

---

## Architecture and Workflow

```
[Informal Prompt]
       │
       ▼ (Agent Synthesis)
[Rocq Formalization]
  ├── Program Definition (Deep Embedding)
  ├── Formal Specification
  ├── Machine-Checked Proof: Program ⊨ Specification
  └── Machine-Checked Proof: Specification ⊨ Validating Properties
       │
       ▼ (Extraction / Pretty-Printing)
[Extracted Cangjie Source]
       │
       ├── Compiles via Cangjie Toolchain
       └── Executes Test Cases & Benchmarks (Partial Correctness Sanity Check)

```

For each example:

* **Synthesis:** An informal prompt defines data structures, algorithms, and expected validating properties (e.g., associativity of list concatenation). The agent synthesizes the complete Rocq formalization: the program, the specification, the proof that the program satisfies the specification, and the proof that the validating properties follow from the specification.
* **Extraction and Execution:** The formal Rocq AST is extracted (pretty-printed) to concrete Cangjie syntax, compiled, executed against test suites, and benchmarked.
* **Vacuity Detection:** Because Iris provides partial correctness guarantees, testing and benchmarking serve as empirical guards against non-termination, divergence, or vacuous proofs.

---

## The Trusted Computing Base (TCB)

The foundational assumptions of the project rely on the correctness of established verification infrastructure:

* **Rocq and Iris:** The Rocq kernel, the Iris framework, and standard mechanized soundness results are trusted. All strict safety flags in Rocq are enforced (e.g., verifying `Print Assumptions` to ensure no ad-hoc axioms, admits, or unsafe escape hatches bypass proof obligations).
* **The Cangjie Toolchain:** The Cangjie compiler, runtime, and execution target are assumed to be correct.

---

## Human Inspection Requirements

The surface that requires careful manual review is strictly bounded and partitioned between the framework and the generated instances.

### 1. The Framework Inspection Burden

The framework defines the semantic foundation. All items below must be audited whenever the framework undergoes non-trivial modification:

* **Syntax Correspondence (Section 3):** Inspect the formal Rocq abstract syntax to verify that it accurately reflects the intended Cangjie fragment. In particular, verify the binding mechanisms (Section 3.5), which model the non-trivial scoping and variable binding semantics of Cangjie.
* **Operational Semantics (Sections 4 & 5):** Review the small-step operational semantics and state transitions to ensure that the definitions accurately capture Cangjie execution behavior and contain no degeneracies or inaccurate behaviour.
* **Separation Logic Construction (Section 6):** Verify that the instantiation of the Iris base logic—including the definitions of resources, points-to predicates, and weakest preconditions—is sound and faithful to the operational model.
* **Adequacy Theorem (Section 7):** Check the formal statement of the adequacy theorem directly. Ensure that the mechanized theorem yields a genuine semantic safety guarantee linking weakest preconditions in Iris to the operational behavior of the language.

### 2. The Per-Example Inspection Burden

For each newly synthesized program or substantial iteration, manual auditing is restricted strictly to specifications and empirical harnesses:

* **Formal Specifications and Validating Properties:** Inspect the formalized specifications and formal validating theorem statements to confirm that they accurately express the intent of the informal prompt.
* *Exclusion:* **Machine-checked proofs do not require manual review.** Proof validity is guaranteed by the Rocq proof checker.


* **Test Suites and Benchmarking Suites:** Verify that the generated test cases and benchmark inputs are meaningful and provide non-trivial test coverage.
* *Exclusion:* **The generated Cangjie source code does not require manual review for correctness.** Because the source is extracted from verified Rocq definitions, semantic compliance is handled by the framework. Reviewers should note that extracted code may not follow human-idiomatic Cangjie programming patterns.

> **Note:** Agents have been instructed to produce vernacular explanations of the formalisations. They are not part of the TCB and are only meant to aid the understanding of the formal Rocq code which must be inspected carefully. 


HashMap reads use a separately verified bounded while loop that returns an option directly; insertion and removal retain the slot-aware probe. The printer emits `calloc` for primitive allocation, matching the core's zero-filled memory on successful native allocations.

ArrayList growth and suffix removal retain their proved CJR copy loops. The printer recognizes these exact method bodies and lowers their disjoint or left-overlapping copies to native `memmove`, with a positive-length guard. Other forward-copy loops are unchanged. Native tests cover repeated front-removal/append cycles, middle removal after growth, zeroed tails, and empty copies.

## Quadtree example

The self-contained integer-point example lives in [example/quadtree/](example/quadtree/README.md).
Its offline report is [example/quadtree/index.html](example/quadtree/index.html); regenerate all
artifacts with `make quadtree-report`.

Project-wide offline report generation and benchmark execution, normalization,
charts, metadata, and link validation live under `tools/project_tools/`. Each
example keeps only its formal development, extracted program, harnesses, and
configuration. Use `make benchmark` for the root CJR benchmark suites and
`make project-report` to rebuild the root specification index.
