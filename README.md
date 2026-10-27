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
- `example/` — self-contained example directories: quadtree, array, array_list, list, list_rev, qsort, hash_map, most_frequent, aes_ige, and misc. Each owns its Rocq sources, generated code, tests, available benchmarks, and offline reports.
- `tools/extraction/rocq/` — shared printer and aggregate extraction driver

Open [all example reports](example/index.html). `make readable EXPLANATIONS=offline` regenerates the example and shared-library pages using existing explanation caches; `make project-report EXPLANATIONS=offline REPORT_FLAGS=--allow-stale` also assembles reports. `make test` runs the runtime suites; `make benchmark` explicitly runs timed benchmarks.

Generics, inheritance, `enum`/`match`, concurrency, garbage collection, and a translation from full Cangjie are out of scope.

## Extracted Cangjie

`make cj` generates the Cangjie files linked below. All links are relative to
this repository. Counts are `wc -l` of the complete files; Rocq counts include
programs, specifications, and proofs. For multi-file developments, counts sum
the files in the linked source directories listed in `_CoqProject`, excluding
extraction drivers. The most-frequent count includes `mf_memory.v`.

| Example | Rocq source | Lines | Extracted Cangjie | Lines | Rocq / Cangjie |
|---|---|---:|---|---:|---:|
| [arith](example/misc/README.md) | [arith.v](example/misc/rocq/arith.v) | 124 | [arith.cj](example/misc/extracted/arith.cj) | 22 | 5.6 |
| [struct_upd](example/misc/README.md) | [struct_upd.v](example/misc/rocq/struct_upd.v) | 57 | [struct_upd.cj](example/misc/extracted/struct_upd.cj) | 27 | 2.1 |
| [cell](example/misc/README.md) | [cell.v](example/misc/rocq/cell.v) | 35 | [cell.cj](example/misc/extracted/cell.cj) | 15 | 2.3 |
| [swap](example/misc/README.md) | [swap.v](example/misc/rocq/swap.v) | 40 | [swap.cj](example/misc/extracted/swap.cj) | 18 | 2.2 |
| [sum_block](example/misc/README.md) | [sum_block.v](example/misc/rocq/sum_block.v) | 90 | [sum_block.cj](example/misc/extracted/sum_block.cj) | 20 | 4.5 |
| [class_upd](example/misc/README.md) | [class_upd.v](example/misc/rocq/class_upd.v) | 45 | [class_upd.cj](example/misc/extracted/class_upd.cj) | 23 | 2.0 |
| [frame_call](example/misc/README.md) | [frame_call.v](example/misc/rocq/frame_call.v) | 37 | [frame_call.cj](example/misc/extracted/frame_call.cj) | 20 | 1.9 |
| [vtable](example/misc/README.md) | [vtable.v](example/misc/rocq/vtable.v) | 70 | [vtable.cj](example/misc/extracted/vtable.cj) | 33 | 2.1 |
| [list](example/list/README.md) | [list.v](example/list/rocq/list.v) | 227 | [list.cj](example/list/extracted/list.cj) | 54 | 4.2 |
| [list_rev](example/list_rev/README.md) | [list_rev.v](example/list_rev/rocq/list_rev.v) | 287 | [list_rev.cj](example/list_rev/extracted/list_rev.cj) | 65 | 4.4 |
| [array](example/array/README.md) | [array.v](example/array/rocq/array.v) | 354 | [array.cj](example/array/extracted/array.cj) | 39 | 9.1 |
| [array_list](example/array_list/README.md) | [array_list.v](example/array_list/rocq/array_list.v) | 2340 | [array_list.cj](example/array_list/extracted/array_list.cj) | 130 | 18.0 |
| [qsort](example/qsort/README.md) | [qsort.v](example/qsort/rocq/qsort.v) | 1749 | [qsort_array.cj](example/qsort/extracted/qsort_array.cj), [qsort_array_list.cj](example/qsort/extracted/qsort_array_list.cj) | 213 | 8.2 |
| [hash_map](example/hash_map/README.md) | [hash_map.v](example/hash_map/rocq/hash_map.v) | 2962 | [hash_map.cj](example/hash_map/extracted/hash_map.cj) | 290 | 10.2 |
| [most_frequent](example/most_frequent/README.md) | [rocq/](example/most_frequent/rocq/) | 2395 | [most_frequent.cj](example/most_frequent/extracted/most_frequent.cj) | 143 | 16.7 |
| [quadtree](example/quadtree/README.md) | [spec/](example/quadtree/spec/), [algorithm/](example/quadtree/algorithm/), [proof/](example/quadtree/proof/) | 1471 | [quadtree.cj](example/quadtree/extracted/quadtree.cj) | 386 | 3.8 |
| [aes_ige](example/aes_ige/README.md) | [rocq/](example/aes_ige/rocq/) | 3690 | [aes_ige.cj](example/aes_ige/extracted/aes_ige.cj) | 3394 | 1.1 |
| **Total** | | **15973** | | **4892** | **3.3** |

The shared [hm_tactics.v](example/hash_map/rocq/hm_tactics.v) evaluation-context
automation adds 110 supporting lines outside these counts.

## Authenticator core

The [memory-only authenticator core](example/authenticator/README.md) implements
SHA-1, HMAC, HOTP/TOTP, Base32 enrollment, and account sessions as extracted CJR.
Its documentation separates checked pure/kernel proofs from the remaining
whole-core Iris refinement obligations. No front-end adapters are included.
Run `make -C example/authenticator test` for independent runtime checks.

## Integer and bitwise operators

The core supports addition, subtraction, multiplication, signed remainder, integer comparison
and equality, Boolean conjunction, and the new integer bitwise XOR and AND.
`BitXorOp` evaluates with `Z.lxor`, uses Rocq expression notation `e1 .^ e2`,
and prints Cangjie `^`; `BitAndOp` evaluates with `Z.land`, uses `e1 .& e2`,
and prints `&`. `wp_bitxor` and `wp_bitand` specialize `wp_binop` and require
no numeric side condition. Boolean `AndOp` remains separate and prints `&&`.
`MulOp` evaluates with `Z.mul`, uses expression notation `e1 * e2`, and prints Cangjie `*`; `wp_mul` has no numeric side condition. Bitwise OR, complement, and shifts are not implemented.

Integers in the model are unbounded signed Rocq integers, while extracted
integer values are `Int64`; the model does not automatically truncate to 64
bits or establish absence of overflow. AES keeps bytes in 0..255: XOR combines
bytes, `x & 255` masks to eight bits, and `x & 128` tests the high bit. Byte
doubling uses addition, masking, and conditional XOR with 27, so AES needs no
multiplication, division, or shift primitive.

## In-place list reversal

`example/list_rev/rocq/list_rev.v` reuses `list.is_list`, reverses existing cons links, and proves `reverse_spec` and `reverse_twice_spec` without admissions or additional axioms. The loop theorem establishes an empty remainder and a reversed accumulator. One fresh empty sentinel separates the two owned chains.

The tutorial includes a detailed subsection for each definition and lemma, complete checked proof listings, and explanations of the invariant, each memory step, the induction, and the final scope cleanup. `make cj` includes the standalone `example/list_rev/extracted/list_rev.cj`; `example/list_rev/test/list_rev_test.cj` covers six runtime cases, including changes observed through references to the original nodes. See [the reversal test history](example/list_rev/test/history.md) for the dated results.

## Verified hash map

`example/hash_map/rocq/hash_map.v` now proves every operation and its supporting kernels without admissions. A bounded probe wraps indexes safely, searches beyond tombstones for existing keys, and returns a precise finite-map lookup result. Insertion grows only for a missing key at the half-full limit; rehashing preserves every live entry, skips tombstones, and restores placement under doubled capacity. The stored size agrees with the finite map throughout.

The tutorial explains the representation, remainder and probe invariants, array ownership, insertion and removal proofs, rehash induction, and client compositions in detail. The generated implementation uses `ProbeResult` and `Int64Option` value structs. `example/hash_map/test/hash_map_test.cj` contains 18 runtime cases, including collisions, wraparound, negative and extreme Int64 keys, signed remainder, zero-filled allocation, iterative lookup, zero values, tombstone reuse, and repeated growth. `make verify` audits the public contracts and supporting kernels in addition to the existing adequacy and reversal theorems.

Primitive signed division (`DivOp`, printed as `/`) uses `Z.quot`; signed remainder (`RemOp`, printed as `%`) uses `Z.rem`. Both truncate toward zero and require a nonzero divisor. `wp_div` and `wp_rem` expose these primitive contracts. Machine overflow, including minimum `Int64` divided by -1, remains a caller-side obligation.

Primitive signed remainder (`RemOp`, printed as `%`) follows division truncated toward zero. Its WP rule requires a nonzero divisor. HashMap bucket normalization now uses one remainder and at most one addition, with a proof that the result equals mathematical modulo for positive capacity; it no longer iterates in proportion to the key magnitude. HashMap now hashes keys as `((k % 2147483647) * 1000000007) % 2147483647` before bucket normalization. Reducing before multiplication keeps the product within `Int64` for every input key (`hash_product_int64`); capacity-spaced keys no longer systematically collide. Collision chains still use linear probing, and the hash is not adversarially secure.

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

## AES encryption and IGE chaining

[The AES-IGE example](example/aes_ige/README.md) implements concrete
AES-128/192/256, key expansion, block encryption/decryption, and
OpenSSL-compatible Infinite Garble Extension (IGE). The implementation uses
SubBytes, ShiftRows, MixColumns, and AddRoundKey, with 10/12/14 rounds for
16/24/32-byte keys; the final round omits MixColumns. Each logical byte occupies
one `Int64` word. The [offline report](example/aes_ige/docs/report.html) and the
paper's AES section explain the specification and exact proof coverage.

The pure Rocq specification proves both AES inverse compositions, bijectivity,
transformation inverse laws, byte range preservation, both IGE inverse
compositions with final-IV agreement, length preservation, empty identity, and
chunk composition. These results use concrete cipher definitions without
assuming AES correctness. Iris refinement contracts cover caller-owned key expansion, all three AES
block variants, and both IGE loops, including their supporting byte and block
operations. Client contracts prove both implementation round trips, final-IV
agreement, empty identity, and chunk composition. Invalid-argument contracts
prove rejection before raw-buffer access. These guarantees require the stated
buffer ownership and bounds preconditions.

`aesExpandKey` writes a forward schedule into a 240-word buffer and returns
10/12/14 (zero for an invalid key length). `aesEncryptBlock` and
`aesDecryptBlock` process 16 words; `aesIgeEncrypt` and `aesIgeDecrypt` process
a nonnegative multiple of 16 logical bytes and update a 32-word IV. Reserve
64 words for workspace; all buffers must be disjoint, large enough, and contain
byte-valued inputs, with the schedule and round count matching the key.
The IV is `previous ciphertext || previous plaintext`. Restore the original IV
for decryption; retain the updated IV when continuing in chunks. Invalid round
counts or message lengths return false without changing output or IV.

The recorded runtime suite contains 15 passing cases, including NIST block
known-answer vectors for all key sizes, OpenSSL IGE fixtures, inverse S-box
checks, chunking, final IVs, invalid arguments, and buffer guards. The
[performance report](example/aes_ige/benchmark/results/report.html) compares
extracted Cangjie with the native OpenSSL C API after checking complete outputs
and final IVs. It reuses schedules and includes IV reset and output checksums
in timings. CJR's word-per-byte representation and OpenSSL's packed bytes,
algorithms, and toolchains differ, so the comparison does not isolate language
overhead or establish hardware AES use.

From `example/aes_ige`, run `make build`, `make verify`, `make extract`,
`make test`, `make benchmark`, and `make docs EXPLANATIONS=offline` as needed.
The implementation provides no padding, authentication, or in-place operation.
Its branch-based S-box is not constant-time; there is no side-channel or
cryptographic security theorem.

## Documentation refresh

The [PDF tutorial](paper/cjr-tutorial.pdf) and [hash-map benchmark report](example/hash_map/benchmark/results/report.html)
include the bounded multiplicative hash and the October 16 measurements.
The PDF uses saved October 12 observations for the other container suites;
refreshing documentation preserves each run's date and source hashes.

The hash change speeds up capacity-spaced CJR lookups by 38-658 times versus
the immediately preceding CJR baseline. Ordinary hits and builds cost 10-37%
more, and misses at larger sizes roughly double. These are workload-specific
tradeoffs. Build-and-scan includes construction, insertion, growth, and a
lookup of every key, normalized by the number of keys. The corrected HTML
charts position dots by measured time and display IQR endpoints on the same
axis; raw samples and numerical summaries were unaffected by the plotting bug.

```sh
make project-report EXPLANATIONS=offline REPORT_FLAGS=--allow-stale  # regenerate HTML from saved timings
python3 paper/update_benchmarks.py        # requires ReportLab; figures and table
make cj                                  # extract and rebuild the PDF twice
```
