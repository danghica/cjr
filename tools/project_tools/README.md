# Shared project tools

`benchmark.py` runs project-configured Cangjie benchmark jobs, parses their
machine-readable output, writes normalized `raw.csv`, medians/IQR in
`summary.json`, compiler and source provenance in `metadata.json`, local SVG
charts, and a static HTML report. The suite configuration owns only compiler
arguments, harness inputs, output parsing, workload labels, and protocol
description. Run it from the repository root:

```sh
python3 tools/project_tools/benchmark.py run path/to/benchmark.config.json
python3 tools/project_tools/benchmark.py plot path/to/benchmark.config.json
python3 tools/project_tools/benchmark.py report path/to/benchmark.config.json
```

Configuration paths are relative to the `project_root` value (the directory
containing the config by default). The runner accepts `CJC`, `CANGJIE_HOME`,
and `SDKROOT` environment overrides and rejects source or output paths outside
that project boundary.

`docs.py` builds source metadata, generic test-report pages, a project report
index from the declaration navigation emitted by `rocq-readable`, and checks
all generated HTML links and fragments:

```sh
python3 tools/project_tools/docs.py metadata path/to/project.config.json
python3 tools/project_tools/docs.py test-report path/to/project.config.json
python3 tools/project_tools/docs.py report path/to/project.config.json
```

An example config supplies its output paths, declaration-group patterns,
artifact labels, and short project description. Its proofs, extracted source,
test cases, benchmark harnesses, and workload definitions stay with that
example. All generated report pages and assets are static and work offline.

`support.py` shares compiler selection and source-provenance helpers used by
project-instance test, verification, and extraction adapters.

## Example dispatch

Examples and their artifacts live under `example/<name>/`. Run `python3 -m tools.project_tools.examples readable --explanations offline`, `test`, or `report` from the repository root; `--example <name>` limits the action. The `benchmark` command explicitly collects new timings; `report` only redraws saved measurements. Shared extraction code is in `tools/extraction/rocq/`, and the benchmark timing helper is `tools/project_tools/benchmark_common.cj`. Historical mixed-suite records are in `paper/benchmark-history/` and `paper/test-history.md`; they retain their original provenance.
