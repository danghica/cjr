# Rocq Readable

A local, deterministic specification renderer for Coq 8.20.1 and CJR/Iris.
Rocq parses the source; the tool turns the concrete AST into a linked document
tree. No generative model, model credentials, network request, or remote asset
is involved in rendering or learning rules.

## Installation and commands

Python 3.10 or newer and `coq-lsp.0.2.5+8.20` are required. Activate the opam
switch with `eval $(opam env)`. If `coq-lsp` is absent from PATH, the CLI also
checks the default opam switch. A different backend release is rejected.

Run `./rocq-readable` from this repository, `python3 -m tools.rocq_readable`,
or install the Python package with `python3 -m pip install .` to obtain the
`rocq-readable` command. The installed command treats its invocation directory
as the project root.

```sh
rocq-readable build --output generated/spec-html
rocq-readable build --output generated/spec-html --strict
rocq-readable render theories/examples/swap.v --name swap_wp --output /tmp/swap.html
rocq-readable build --dictionary ./my-renderings.json --learn
```

`make readable` and `make readable-test` provide repository shortcuts.
Integration tests require the backend; tests report a skip when it is missing.

Whole-project output contains `index.html`, one page per `.v` file, `style.css`,
and `report.json`. The directory structure mirrors the source tree. Individual
rendering produces a standalone HTML file with embedded CSS and a sibling
`.report.json`; it does not overwrite an unrelated index or stylesheet.

`--name` accepts a short or qualified name. Ambiguous short names are rejected.
Single-declaration rendering stops after the declaration, so its proof can be
absent or invalid. Earlier commands and proofs may still need checking to
establish the declaration's environment.

## Project boundary and links

Discovery walks the current directory recursively, including hidden directories
and unlisted `.v` files. Git metadata, the selected output directory, and
symlinks are excluded. Neither source discovery nor symbol links follow paths
outside this root.

The nearest ancestor `_RocqProject` or `_CoqProject` within the root supplies
backend configuration; `_RocqProject` takes precedence when both exist. These
files configure parsing rather than limit the discovered inventory. Dependencies
must already be available to Rocq; generation does not build or install them.

Compiled `.glob` files provide exact global identities, notation scopes,
constructors, fields, and lexical reference data. They are used only when their
source digest matches and project configuration/import timestamps remain current.
Without a fresh `.glob`, the tool asks coq-lsp for symbol
destinations and leaves ambiguous or unavailable references unlinked. Run the
normal project build for the most complete link coverage. Dictionary renaming
changes display text without changing the destination.

All emitted links are relative and point to generated project declarations or
local binders. Library references and references whose project destination is
not generated remain plain text. An individual page links only to declarations
and binders included in that page. Qualified Rocq identities determine stable,
ASCII declaration anchors.

## Scope and logical fidelity

Four-space indentation determines multiline scope; colons introduce blocks and
dedentation closes them. Multiline calls have no enclosing parentheses. Scope
brackets appear only when the whole expression fits on a single line. Brackets
inside data literals retain their data meaning. HTML preserves whitespace and
scrolls horizontally instead of wrapping lines at narrow screen widths.

The renderer keeps parameters, explicit types, inferred-type holes, implicit
markers, context assumptions, and original declaration names. It distinguishes
ordinary implication, consuming implication, entailment, conjunction, separating
conjunction, pure assertions, persistence, and later modalities. Explicit WP
masks, stuckness arguments, and postcondition binders stay in the document.
Iris WP specifications express partial correctness, not termination.

Gallina's `arrow(A, B)` retains the distinction from resource-consuming
implication. In propositions it means ordinary implication; in types it means
a function type. The concrete AST alone does not establish which interpretation
applies, so the renderer does not guess from the spelling of its arguments.

Built-in rules cover common Gallina/stdlib forms and CJR/Iris ownership and WP
notation. Other functions remain calls. Unmapped notation retains its exact
grammar key and every substitution slot. Unsupported AST forms retain a marked
original-source fragment. Every declaration has an expandable proof-free source
excerpt. Original-source displays retain Rocq syntax and its original brackets.

Rendering does not unfold predicates, simplify terms, erase technical premises,
or certify a user's interpretation. The output is an auditable presentation,
not a formally verified translation or a replacement for proof checking.

## Dictionary and interactive learning

The default version-controlled dictionary is `renderings.json` beside this
document. Use `--dictionary` to select another file; a nonexistent path starts
an empty dictionary. Ordinary rendering never writes the dictionary.

The JSON root has exactly `version: 1` and a `rules` array. Each rule has:

- `kind`: `application` or `notation`.
- `key`: the resolved function identity or exact parsed notation grammar key.
- `arity`: the number of substitution slots.
- `label`: the displayed name.
- `layout`: `call` (inline when it fits) or `block` (always indented).
- `slots`: a permutation containing every slot number exactly once.
- Optional `scope` and `entry` selectors for notation matching. `null` selects
  the absence of scope/entry information; omitting a selector matches any value.
- Optional `identity` matches Rocq's exact resolved notation identity, separating
  identical grammar keys and scopes declared in different modules. Seeded rules
  use it when that information is available.

```json
{
  "version": 1,
  "rules": [
    {
      "kind": "application",
      "key": "cjr.primitive_laws.raw_mapsto",
      "arity": 2,
      "label": "owns_raw",
      "layout": "call",
      "slots": [0, 1]
    }
  ]
}
```

Templates are structured labels/layouts, not executable code or raw HTML.
The renderer preserves each child document's symbols, binders, links, and nested
scope. Duplicate selectors, ambiguous equally specific matches, missing slots,
extra slots, unknown fields, and malformed files are rejected.

With `--learn`, choose a numbered encountered construct to teach or replace.
The CLI shows the source and every numbered slot, accepts JSON containing
`label`, `layout`, and `slots`, then writes a local HTML preview. A rule is saved
only after answering `y` to its acceptance prompt. Blank input skips a template;
`done` exits learning. `remove NUMBER` previews a deletion for confirmation.
EOF or interruption cancels learning without saving an unaccepted rule.
For single-page rendering, previews live in a dedicated `.preview` directory.

Scope and binder slots remain present, but user-authored labels and permutations
require human review: preserving the tree's content does not prove that arbitrary
wording conveys its meaning correctly.

## Errors, limits, and verification

File-level parser/context errors are displayed in the generated page and report;
other files still generate. Any failed file returns exit status 1. `--strict`
also returns 1 for unmapped notation or unsupported declarations/terms. Missing
dependencies, backend errors, and timeouts are reported rather than guessed.
No proof admissions are introduced; coq-lsp's failed-Qed admission recovery is
explicitly disabled.

`--timeout SECONDS` bounds each backend request (default 600 seconds). Large
developments may need a larger value because the backend checks earlier proofs
and maintains their document states. Partial HTML is not presented as complete
coverage; consult `report.json` before using it for review.

Tests use actual Rocq ASTs and check project boundaries, digest validation,
scope layout, rule learning/reloading, HTML escaping, local shadowing, cross-file
and constructor/field links, proof omission, deterministic generation, and
representative CJR contracts. The renderer is optional and does not change the
existing proof verification targets.
