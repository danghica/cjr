"""CLI orchestration. Source and dictionaries are never changed by rendering."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from urllib.parse import unquote, urlparse

from .ast import Adapter, declarations, value, walk
from .backend import Backend, BackendError
from .dictionary import Dictionary, DictionaryError
from .html import CSS, index, page, shell
from .layout import anchor, render_html
from .project import Glob, Source, configuration, discover, inside


DEFAULT_DICTIONARY = Path(__file__).with_name("renderings.json")


def resolve_missing(backend, source):
    """Ask Rocq for destinations when no digest-verified .glob is available."""
    if source.glob.valid:
        return {}
    result = {}
    nodes = []
    for declaration in source.declarations:
        for term in [declaration.body, declaration.type, declaration.binders, declaration.context,
                     *[c.type for c in declaration.children]]:
            for node in walk(term):
                expr = value(node)
                if isinstance(node, dict) and isinstance(expr, list) and expr[0] in ("CRef", "CPatAtom"):
                    if expr[1]:
                        nodes.append(expr[1])
    for node in nodes:
        loc = node.get("loc")
        if not loc or loc["bp"] in result:
            continue
        prefix = source.text.encode()[:loc["bp"]].decode()
        lines = prefix.split("\n")
        position = {"line": len(lines) - 1, "character": len(lines[-1].encode("utf-16-le")) // 2}
        location = backend.request("textDocument/definition", {"textDocument": {"uri": source.path.as_uri()}, "position": position})
        if isinstance(location, list):
            location = location[0] if len(location) == 1 else None
        if location and "uri" in location:
            url = urlparse(location["uri"])
            target = Path(unquote(url.path)).resolve()
            if url.scheme == "file" and not url.netloc and inside(target, source.root):
                result[loc["bp"]] = (target, location["range"]["start"])
    return result


def prepare(paths, root, timeout, selected=None):
    sources, resolutions = [], {}
    for path in paths:
        try:
            source = Source.load(path, root)
        except (OSError, ValueError) as exc:
            source = Source(path, root, "", ".".join(path.relative_to(root).with_suffix("").parts), Glob())
            source.errors.append(f"cannot load source/configuration: {exc}")
            sources.append(source)
            print(f"  error in {source.relative}: {exc}", file=sys.stderr)
            continue
        sources.append(source)
        print(f"Parsing {source.relative}", file=sys.stderr, flush=True)
        workspace = configuration(path, root).parent
        try:
            with Backend(workspace, timeout) as backend:
                document, diagnostics = backend.document(path, source.text, selected=selected, model=source)
                declarations(source, document)
                errors = [d for d in diagnostics if d.get("severity") == 1]
                source.errors.extend(f"line {d['range']['start']['line'] + 1}: {d['message']}" for d in errors[:8])
                if len(errors) > 8:
                    source.errors.append(f"{len(errors) - 8} additional errors")
                if document.get("completed", {}).get("status") == ["Failed"] and not errors:
                    source.errors.append("Rocq could not finish parsing this source")
                resolutions[path] = resolve_missing(backend, source)
        except (BackendError, ValueError, KeyError, IndexError) as exc:
            source.errors.append(str(exc))
            print(f"  error: {exc}", file=sys.stderr)
    return sources, resolutions


def identities(sources):
    return {decl.identity for source in sources for declaration in source.declarations
            for decl in (declaration, *declaration.children)}


def resolved_identities(resolutions, sources):
    result = {}
    by_path = {s.path: s for s in sources}
    for path, references in resolutions.items():
        result[path] = {}
        for offset, (target, position) in references.items():
            source = by_path.get(target)
            if not source:
                continue
            candidates = []
            for declaration in source.declarations:
                for decl in (declaration, *declaration.children):
                    loc = decl.name_node.get("loc") or {}
                    if loc.get("line_nb", 0) - 1 == position["line"]:
                        candidates.append(decl.identity)
            # .glob-free LSP definitions return sentence starts. Never guess
            # when a line contains more than one destination.
            if len(candidates) == 1:
                result[path][offset] = candidates[0]
    return result


def learning(dictionary, encounters, output):
    items = sorted(encounters.items(), key=lambda x: str(x[0]))
    print("\nRendering dictionary: choose a number to teach/replace, 'remove NUMBER', or 'done'.")
    for i, (key_parts, _) in enumerate(items, 1):
        kind, key, arity, scope, entry = key_parts[:5]
        print(f"{i}: {kind} {key!r} ({arity} slots, scope={scope!r})")
    while True:
        try:
            choice = input("rule> ").strip()
            if choice in ("", "done", "quit"):
                return
            removing = choice.startswith("remove ")
            number = int(choice.split()[-1]) - 1
            if number < 0 or number >= len(items):
                raise DictionaryError("select a listed rule number")
            key_parts, (label, children, source) = items[number]
            kind, key, arity, scope, entry = key_parts[:5]
            selector = {"kind": kind, "key": key, "arity": arity, "scope": scope, "entry": entry}
            if kind == "notation" and label.identity:
                selector["identity"] = label.identity
            current = dictionary.match(kind, key, arity, scope, entry, label.identity)
            if removing:
                if current and input(f"Remove {current['label']!r}? [y/N] ").lower() == "y":
                    dictionary.remove(current)
                    dictionary.save()
                continue
            print("Original:", source)
            for i, child in enumerate(children):
                print(f"Slot {i}:\n{child.plain()}")
            print('Enter JSON: {"label":"readable_name", "layout":"call" or "block", "slots":[all slot numbers]}; blank skips.')
            text = input("template> ").strip()
            if not text:
                continue
            fields = json.loads(text)
            if not isinstance(fields, dict) or set(fields) - {"label", "layout", "slots"}:
                raise DictionaryError("template accepts only label, layout, and slots")
            from .dictionary import validate
            rule = validate({**selector, **fields})
            document = dictionary.apply(rule, label, children)
            preview = output / "rule-preview.html"
            output.mkdir(parents=True, exist_ok=True)
            (output / "style.css").write_text(CSS)
            preview.write_text(shell("Rendering rule preview", '<h1>Rendering rule preview</h1><pre>' + render_html(document, preview, {}) + '</pre>', preview, output))
            print(document.plain())
            print(f"HTML preview: {preview}")
            if input("Save this rule? [y/N] ").lower() == "y":
                dictionary.replace(rule)
                dictionary.save()
        except (EOFError, KeyboardInterrupt):
            print("\nLearning cancelled; unaccepted rules were not saved.")
            return
        except (ValueError, DictionaryError) as exc:
            print(f"Invalid rule: {exc}")


def generate(sources, resolutions, dictionary, output, single=None, learn=False):
    known = identities(sources)
    resolved = resolved_identities(resolutions, sources)
    outputs = {s.path: single if single else output / s.relative.with_suffix(".html") for s in sources}
    symbols = {}
    for source in sources:
        for declaration in source.declarations:
            for decl in (declaration, *declaration.children):
                if decl.identity in symbols:
                    raise ValueError(f"duplicate Rocq identity {decl.identity}; check project load-path mappings")
                symbols[decl.identity] = (outputs[source.path], anchor(decl.identity))
    encounters = {}
    def render():
        documents, coverage = {}, {}
        for source in sources:
            adapter = Adapter(source, dictionary, known, resolved.get(source.path))
            documents[source.path] = [adapter.declaration(d) for d in source.declarations]
            coverage[source.path] = adapter.coverage
            encounters.update(adapter.encounters)
        return documents, coverage
    documents, coverage = render()
    if learn:
        learning(dictionary, encounters, single.with_suffix(".preview") if single else output)
        documents, coverage = render()
    output.mkdir(parents=True, exist_ok=True)
    if not single:
        (output / "style.css").write_text(CSS)
    for source in sources:
        target = outputs[source.path]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(page(source, documents[source.path], target, output, symbols, coverage[source.path], standalone=bool(single)))
    if not single:
        (output / "index.html").write_text(index(sources, outputs, output))
    report = {"version": 1, "files": [{"file": str(s.relative), "errors": s.errors,
                "unsupported": sorted(set(coverage[s.path])), "declarations": len(s.declarations)} for s in sources]}
    report_path = single.with_suffix(".report.json") if single else output / "report.json"
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    return coverage


def main(argv=None):
    parser = argparse.ArgumentParser(description="Render proof-free Rocq specifications as linked, offline HTML")
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("build", "render"):
        command = commands.add_parser(name)
        if name == "render":
            command.add_argument("file", type=Path)
            command.add_argument("--name", required=True)
        command.add_argument("--output", type=Path, default=Path("generated/spec-html") if name == "build" else None,
                             required=name == "render")
        command.add_argument("--dictionary", type=Path, default=DEFAULT_DICTIONARY)
        command.add_argument("--learn", action="store_true")
        command.add_argument("--strict", action="store_true")
        command.add_argument("--timeout", type=float, default=600, help="backend request timeout in seconds")
    args = parser.parse_args(argv)
    root = Path.cwd().resolve()
    destination = args.output.resolve()
    output = destination if args.command == "build" else destination.parent
    try:
        if args.timeout <= 0:
            raise ValueError("timeout must be positive")
        if args.command == "build" and output == root:
            raise ValueError("output must be a separate directory, not the project root")
        dictionary = Dictionary(args.dictionary.resolve())
        if args.command == "render":
            path = args.file.resolve()
            if not inside(path, root) or path.suffix != ".v" or not path.is_file():
                raise ValueError("input must be a .v file within the current directory")
            if destination.name in ("index.html", "rule-preview.html") or destination.suffix != ".html":
                raise ValueError("single output must be a .html file other than index.html or rule-preview.html")
            paths = [path]
        else:
            paths = discover(root, output)
        if not paths:
            raise ValueError("no Rocq .v sources found beneath the current directory")
        sources, resolutions = prepare(paths, root, args.timeout,
                                       selected=args.name if args.command == "render" else None)
        if args.command == "render":
            candidates = [d for d in sources[0].declarations if d.identity == args.name or d.name == args.name]
            if len(candidates) != 1:
                raise ValueError(f"expected one declaration named {args.name!r}; candidates: " +
                                 ", ".join(d.identity for d in candidates or sources[0].declarations))
            sources[0].declarations = candidates
        coverage = generate(sources, resolutions, dictionary, output,
                            single=destination if args.command == "render" else None, learn=args.learn)
        errors = sum(bool(s.errors) for s in sources)
        unsupported = sum(len(c) for c in coverage.values())
        result = destination if args.command == "render" else output / "index.html"
        print(f"Generated {result} ({len(sources)} files, {errors} with errors, {unsupported} unmapped/unsupported constructs)")
        return 1 if errors or args.strict and unsupported else 0
    except (OSError, ValueError, BackendError) as exc:
        print(f"rocq-readable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
