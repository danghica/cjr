# Integer-point quadtrees

Open `index.html` for the offline report and declaration index. All example
sources and artifacts live here; CJR/Iris and the syntax-directed Cangjie
printer are shared with the parent project.

From this directory, `make build`, `make verify`, `make extract`, `make test`,
`make benchmark`, and `make docs` run individual stages. `make report` runs
these stages in order and assembles the report. Documentation, benchmark
execution, result normalization, charts, report pages, metadata, and link
validation are provided by the project-wide tools under `../../tools/project_tools/`.
This directory contains the quadtree configuration and benchmark harnesses.
`make assemble` assembles already current artifacts; stale hashes or missing
destinations are errors. Historical benchmark provenance is preserved and labelled; relocation does not count as a new measurement.

Open [all examples](../index.html). Set `EXPLANATIONS=offline` when rendering from existing explanation caches.

Benchmark charts are generated as local SVGs by the shared Python tooling; no
network access is required.

Set `COQC`, `COQCHK`, `CJC`, `CANGJIE_HOME`, and `SDKROOT` to select the tools.
The default compiler is Cangjie 1.0.5 at
`~/cangjiebuild/software/cangjie/bin/cjc`. On newer macOS, the bundled LLVM
cannot read Apple's arm64e.x1 TAPI labels. Without an explicit `SDKROOT`, the
runner copies SDK linker stubs into a temporary directory, removes unsupported
arm64e.x1 targets, and normalizes arm64e labels to arm64. Exported symbols are
unchanged; the installed SDK is never modified. This choice is recorded.

`make(depth)` requires a depth from 0 through 30. Insertions return whether a
new point was added; rejected coordinates and duplicates preserve the tree.
Rectangles are half-open, including when endpoints extend outside the domain.
Range queries allocate a duplicate-free linked list and preserve every tree
field. Result order is unspecified by the API. No deletion, expansion, or
executable union is provided.

The set model proves the algebraic laws modulo represented point sets.
The reference model proves subdivision, uniqueness and bounded depth.
Verification coverage in the report distinguishes reference-model proofs from
Iris contracts for the extracted CJR program. Partial correctness of an Iris
WP means that, if the operation returns, its postcondition holds.

Runtime checks use a seeded independent flat-set oracle and structural snapshots.
Benchmarks compare the unchanged extracted program to an independent native
quadtree and a hash-indexed flat collection. Datasets contain 256, 4096, or
16384 unique points over a depth-30 domain. Uniform points span the domain;
clustered points lie in a 256-square; shared-prefix points fill a 128-wide grid
near the origin. Each implementation receives two warmup batches, independent
calibration toward 20 ms, and seven trials in each of three fresh processes.
Implementation order rotates by trial and process. Construction and range
repetitions are capped using a 262144-point allocation budget; allocation and
GC remain part of timing. Full result validation runs outside timing and
checked checksums are consumed within each timed batch. Smaller capped batches
can fall short of 20 ms. Medians and IQR summarize the 21 observations per
workload and implementation. No speedup claim is inferred from these local
measurements.

The readable documentation selects the model, algorithm, and proof modules.
The generated `proof/audit.v` contains only `Print Assumptions` commands and
has no declaration pages; it remains part of verification, and is excluded
from coq-lsp documentation rendering to avoid repeating the full audit.
