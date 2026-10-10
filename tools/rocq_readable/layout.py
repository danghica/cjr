"""A semantic document tree: links survive layout and user templates."""
from __future__ import annotations

from dataclasses import dataclass, field
import html
import hashlib
from pathlib import Path
import os
from urllib.parse import quote


@dataclass(frozen=True)
class Token:
    text: str
    identity: str | None = None
    anchor: str | None = None
    local: str | None = None
    css: str = ""


@dataclass
class Doc:
    label: Token
    children: list[Doc] = field(default_factory=list)
    block: bool = False
    raw: bool = False

    def inline(self):
        if self.block or self.raw and "\n" in self.label.text:
            return None
        parts = [child.inline() for child in self.children]
        if any(part is None for part in parts):
            return None
        if not self.children:
            return [self.label]
        tokens = [self.label, Token("(")]
        for i, part in enumerate(parts):
            if i:
                tokens.append(Token(", "))
            tokens.extend(part)
        return [*tokens, Token(")")]

    def lines(self, indent=0, width=92):
        inline = self.inline()
        if inline is not None and indent * 4 + sum(len(t.text) for t in inline) <= width:
            return [(indent, inline)]
        if self.raw:
            return [(indent, [Token(line, css="unsupported")]) for line in self.label.text.splitlines()]
        if not self.children:
            # A long identifier or literal is a single unbreakable token.
            return [(indent, [self.label])]
        return [(indent, [self.label, Token(":")]),
                *(line for child in self.children for line in child.lines(indent + 1, width))]

    def plain(self):
        return "\n".join("    " * level + "".join(t.text for t in tokens) for level, tokens in self.lines())


def leaf(text, **kwargs):
    return Doc(Token(text, **kwargs))


def anchor(identity: str):
    # ASCII anchors avoid URL-fragment decoding differences for Unicode
    # names and Rocq's notation identities.
    return "symbol-" + hashlib.sha256(identity.encode()).hexdigest()[:24]


def tokens_html(tokens, current: Path, symbols: dict[str, tuple[Path, str]]):
    result = []
    for token in tokens:
        text = html.escape(token.text)
        if token.identity and token.identity in symbols:
            target, target_anchor = symbols[token.identity]
            relative = "" if target == current else quote(os.path.relpath(target, current.parent).replace(os.sep, "/"), safe="/")
            text = f'<a href="{relative}#{target_anchor}" title="{html.escape(token.identity, quote=True)}">{text}</a>'
        elif token.local:
            text = f'<a href="#{html.escape(token.local, quote=True)}">{text}</a>'
        elif token.identity:
            text = f'<span class="external" title="External or unresolved: {html.escape(token.identity, quote=True)}">{text}</span>'
        if token.anchor:
            text = f'<span id="{html.escape(token.anchor, quote=True)}">{text}</span>'
        if token.css:
            text = f'<span class="{html.escape(token.css, quote=True)}">{text}</span>'
        result.append(text)
    return "".join(result)


def render_html(doc: Doc, current, symbols):
    return "\n".join("    " * level + tokens_html(tokens, current, symbols)
                     for level, tokens in doc.lines())
