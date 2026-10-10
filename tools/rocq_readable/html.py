"""Portable static HTML; all navigation is relative to generated pages."""
from __future__ import annotations

import html
import os
from pathlib import Path
from urllib.parse import quote

from .layout import Token, anchor, render_html, tokens_html


def source_excerpt(source, decl, document, current, symbols):
    data = decl.source.encode()
    start, end = decl.source_start, decl.source_start + len(data)
    bindings = {token.anchor for _, tokens in document.lines() for token in tokens if token.anchor}
    local = {identity: f"{anchor(decl.identity)}-binder-{offset}"
             for offset, (identity, kind) in source.glob.definitions.items()
             if kind in ("binder", "var") and f"{anchor(decl.identity)}-binder-{offset}" in bindings}
    tokens, cursor = [], start
    for offset, (stop, identity, kind) in sorted(source.glob.references.items()):
        if offset < cursor or offset < start or stop > end:
            continue
        tokens.append(Token(data[cursor - start:offset - start].decode()))
        text = data[offset - start:stop - start].decode()
        tokens.append(Token(text, local=local.get(identity)) if kind == "var" else Token(text, identity=identity))
        cursor = stop
    tokens.append(Token(data[cursor - start:].decode()))
    return tokens_html(tokens, current, symbols)


CSS = """/* Offline, indentation-preserving specification pages. */
:root { color-scheme: light; font-family: system-ui, sans-serif; color: #203044; background: #f3f5f7; }
body { margin: 0; } main { max-width: 1080px; margin: auto; padding: 36px 24px 72px; }
header { margin-bottom: 32px; border-bottom: 2px solid #183c52; padding-bottom: 20px; }
.eyebrow { color: #42716c; text-transform: uppercase; letter-spacing: .12em; font-size: .75rem; font-weight: 700; }
h1 { font-size: 2rem; overflow-wrap: anywhere; } h2 { font-size: 1.25rem; margin-top: 0; }
a { color: #006a75; text-decoration-thickness: 1px; text-underline-offset: 3px; }
a:hover { color: #003e49; background: #e2f3ef; } a:focus-visible { outline: 2px solid #006a75; }
article, .panel { background: white; padding: 24px; border: 1px solid #d8e1e5; border-radius: 8px; margin: 20px 0; }
article:target, span:target { outline: 2px solid #67aaa0; scroll-margin-top: 20px; }
pre { font: 14px/1.65 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; white-space: pre; overflow-x: auto; tab-size: 4; }
pre a { text-decoration-style: dotted; } .external { color: #526276; } .unsupported, .error { color: #94392c; }
.meta, .notice { color: #586778; font-size: .9rem; } .notice { line-height: 1.5; }
details { border-top: 1px solid #e1e7eb; padding-top: 12px; } summary { cursor: pointer; font-size: .85rem; color: #586778; }
nav ul, .files { padding-left: 22px; line-height: 1.9; } .count { color: #586778; font-size: .85rem; }
@media(max-width: 600px) { main { padding: 20px 12px; } article { padding: 16px; } h1 { font-size: 1.5rem; } }
"""


def relative(target, current):
    return quote(os.path.relpath(target, current.parent).replace(os.sep, "/"), safe="/")


def shell(title, body, current, output, standalone=False):
    stylesheet = relative(output / "style.css", current)
    style = f'<style>{CSS}</style>' if standalone else f'<link rel="stylesheet" href="{stylesheet}">'
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} — Rocq Readable</title>{style}</head>
<body><main>{body}</main></body></html>
'''


def page(source, documents, current, output, symbols, coverage, standalone=False):
    declarations = source.declarations
    nav = "".join(f'<li><a href="#{anchor(d.identity)}">{html.escape(d.name)}</a> <span class="count">{html.escape(d.kind)}</span></li>' for d in declarations)
    navigation = '' if standalone else f'<p><a href="{relative(output / "index.html", current)}">Project index</a></p>'
    body = f'''<header><div class="eyebrow">Rocq Readable · specification reference</div>
{navigation}
<h1>{html.escape(str(source.relative))}</h1><p class="meta">{len(declarations)} declarations · proofs omitted</p>
<p class="notice">Indentation determines multiline scope. Brackets delimit scope only within a line.
WP contracts express partial correctness, without a termination guarantee. Unlinked names may belong to external libraries or remain unresolved.
Rendering rules are presentation choices reviewed by their authors.</p></header>'''
    if source.errors:
        body += '<section class="panel error"><h2>Source errors</h2><ul>' + ''.join('<li>' + html.escape(e) + '</li>' for e in source.errors) + '</ul></section>'
    if coverage:
        body += f'<p class="notice">Incomplete rendering: {len(coverage)} unsupported or unmapped constructs. Original syntax is retained where needed.</p>'
    body += '<nav aria-label="Declarations"><ul>' + nav + '</ul></nav>'
    for decl, document in zip(declarations, documents):
        body += f'<article id="{anchor(decl.identity)}"><h2>{html.escape(decl.name)}</h2><p class="meta">{html.escape(decl.identity)}'
        if decl.section:
            body += ' · ' + html.escape(decl.section)
        body += '</p><pre class="pseudocode">' + render_html(document, current, symbols) + '</pre>'
        body += '<details><summary>Original declaration (proof-free)</summary><pre>' + source_excerpt(source, decl, document, current, symbols) + '</pre></details></article>'
    return shell(str(source.relative), body, current, output, standalone)


def index(sources, outputs, output):
    current = output / "index.html"
    count = sum(len(s.declarations) for s in sources)
    body = f'''<header><div class="eyebrow">Rocq Readable</div><h1>Project specifications</h1>
<p class="meta">{len(sources)} source files · {count} declarations · deterministic rendering</p>
<p class="notice">Sources are discovered beneath the invocation directory. Symbol links remain within these generated files; library references are unlinked.</p></header>
<section class="panel"><h2>Source files</h2><ul class="files">'''
    for source in sources:
        target = outputs[source.path]
        status = " · source errors" if source.errors else ""
        body += f'<li><a href="{relative(target, current)}">{html.escape(str(source.relative))}</a> <span class="count">{len(source.declarations)} declarations{status}</span></li>'
    return shell("Project specifications", body + '</ul></section>', current, output)
