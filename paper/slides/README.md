# CJR slide deck

`cjr.pptx` is an editable 28-slide, 16:9 presentation for a 40–45 minute talk to
programmers unfamiliar with formal methods. Speaker notes contain explanations,
repository and external sources, benchmark provenance, and unrounded quartiles.
No PDF is produced.

## Rebuild

The generator uses the bundled `@oai/artifact-tool`, not python-pptx. On this
machine run from the repository root:

```sh
/Users/danghica/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node paper/slides/build.mjs
```

The finalizer deliberately refuses to overwrite a final deck. To rebuild for
comparison, select a new filename:

```sh
CJR_SLIDES_OUTPUT=/Users/danghica/cjr/paper/slides/.build/rebuilt.pptx \
/Users/danghica/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node paper/slides/build.mjs
```

`content.mjs` contains the slide narrative and notes. `build.mjs` contains layout,
editable chart construction, preview rendering and package validation. Charts
read the recorded summaries under each example's benchmark directory. Their
workbooks contain literal values rounded to 12 significant digits for Excel
compatibility. Notes retain the original unrounded data. Local preview PNGs,
layouts, drafts and validation receipts are private build products in `.build/`.

On another installation, set `CJR_RUNTIME_ROOT` to the bundled dependency root
and `CJR_PRESENTATIONS_SKILL` to the presentations skill directory. Optional
`CJR_NODE_MODULES` and `CJR_RUNTIME_PYTHON` override their individual paths.
Arial and Menlo are the selected fonts; PowerPoint on machines without Menlo may
substitute a local monospace font.

## Benchmark evidence

The checked-in deck predates the October 16 hashmap hash change and chart fix.
Its benchmark narrative is a saved presentation snapshot. Current hashmap
measurements and interpretation are in the [PDF tutorial](../cjr-tutorial.pdf)
and [hashmap README](../../example/hash_map/README.md). The latest saved list
and quadtree results retain their historical measurement dates. Rebuilding a
deck reads the current summaries, so its narrative and notes must also be
reviewed for consistency. The reversal benchmark is new and reproducible:

```sh
make -C example/list_rev benchmark
make -C example/list_rev assemble
```

Its harness checks complete sequences outside timing and compares the unchanged
extracted program with an independent native algorithm. See the benchmark's
README for units, protocol and comparator differences. Repository proof checks:

```sh
PATH=/Users/danghica/.opam/default/bin:$PATH make verify
```

## Rocq-readable assets

The two screenshots illustrate real local renderer output. To recapture after a
documentation update, run `assets/capture.cjs` with the bundled Node executable.
This uses headless Chrome. Override `PLAYWRIGHT_MODULE` and `CHROME` on another
machine. Recapturing is optional for a normal deck rebuild. The statement image
is explicitly an excerpt; its surrounding typeclass context remains in the
slide caption and notes. The full original capture is also retained.

Proofs establish CJR safety and partial correctness. Neither the renderer nor
this deck proves a translation into native Cangjie correct.
