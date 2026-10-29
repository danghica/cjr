# CJR workspace

> [!IMPORTANT]
> **New development has moved to three repositories.** This repository preserves the original CJR history and serves as a migration record. Follow the repositories below for all new work:
>
> - [**cjr-core**](https://github.com/danghica/cjr-core) — the CJR framework, shared tools, and introductory examples.
> - [**cjr-collections**](https://github.com/danghica/cjr-collections) — data structures and algorithms.
> - [**cjr-crypto**](https://github.com/danghica/cjr-crypto) — AES/IGE and the authenticator application.

The development is now three independent local Git repositories:

- [CJR Core documentation](cjr-core/docs/index.html): semantics, Iris logic, generic source layer, extraction printers, misc examples, and introductory generics. The only copy of rocq_readable lives here.
- [CJR Collections documentation](cjr-collections/docs/index.html): arrays, polymorphic arrays, array lists, linked lists/reversal, quicksort, hash maps, most-frequent, and quadtrees.
- [CJR Crypto documentation](cjr-crypto/docs/index.html): AES/IGE and the authenticator core, CLI, and macOS UI.

Each directory is a separate Git repository with its own README, offline HTML documentation, paper/tutorial.pdf and editable LaTeX, runtime tests, and benchmarks. They are ignored by this parent repository; commit work inside the relevant child. The three repositories are public on GitHub under [danghica](https://github.com/danghica).

Collections pins core; crypto pins both core and collections. Dependency versions are in each dependencies.lock.json. Sibling directories are the default; CJR_CORE_DIR and CJR_COLLECTIONS_DIR can select other checkouts at the pinned versions.

Inside a child, run make dependencies, make test, make benchmark, make docs, or make paper. These runtime and documentation commands do not check proofs. make build, make extract, make verify, and make readable explicitly invoke the proof toolchain.

## Migration record

The original monolith was committed first at `e07ccfb365e019f440480d6357d0251187acc8da`. Its entire tracked state, including previous uncommitted generic work and the historical verification log, remains recoverable from this checkpoint.

The parent keeps prompt logging instructions, scripts/log_prompt.py, logs/prompts.txt, and the original build/verify.log. migration-manifest.json maps original files to their new homes and records source/destination hashes. migration-status.json records the final child commits and validation results.

Proofs were not revalidated during this split. Historical proof reports retain their original evidence. Current runtime, frontend, documentation, and benchmark results live in the corresponding child repositories.
