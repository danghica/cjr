# array_list

All example-specific assets live here. Existing Rocq definitions, specifications, and proofs remain together in `rocq/`, with their original `cjr.examples.*` import names. Generated Cangjie is in `extracted/`, runtime tests in `test/`, and rendered specifications and dependency diagrams in `docs/rocq/`. Existing benchmarks and papers are under `benchmark/` and `docs/`.

Open [the offline report](index.html) or [all examples](../index.html). From this directory run `make build`, `make extract`, `make test`, `make docs`, or `make assemble`. Set `EXPLANATIONS=offline` to reuse explanation caches without model requests. `make benchmark` runs timed measurements only where a harness exists. Shared libraries and sibling examples are resolved through the repository build configuration.
