"""Behavior tests using real Rocq ASTs, plus filesystem/template invariants."""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import hashlib
from html.parser import HTMLParser
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import unquote, urlparse

from tools.rocq_readable.ast import Adapter, declarations
from tools.rocq_readable.backend import Backend, BackendError, executable
from tools.rocq_readable.cli import DEFAULT_DICTIONARY, generate, learning, main, prepare
from tools.rocq_readable.dictionary import Dictionary, DictionaryError, validate
from tools.rocq_readable.layout import Doc, Token, anchor, leaf
from tools.rocq_readable.project import Glob, Source, configuration, discover


ROOT = Path(__file__).resolve().parents[1]


class HTMLInventory(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids, self.links = [], []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.append(attrs["id"])
        if "href" in attrs:
            self.links.append(attrs["href"])


def audit_links(output):
    inventories = {p.resolve(): HTMLInventory(p.read_text()) for p in output.rglob("*.html")}
    for path, inventory in inventories.items():
        if len(set(inventory.ids)) != len(inventory.ids):
            raise AssertionError(f"duplicate anchors in {path}")
        for link in inventory.links:
            url = urlparse(link)
            if url.scheme or url.netloc:
                raise AssertionError(f"external link {link}")
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            if not target.is_relative_to(output.resolve()) or not target.exists():
                raise AssertionError(f"missing/outside destination {link} in {path}")
            if url.fragment and unquote(url.fragment) not in inventories[target].ids:
                raise AssertionError(f"missing anchor {link} in {path}")


class FilesystemAndRules(unittest.TestCase):
    def test_discover_unlisted_hidden_nested_and_boundary(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as outside:
            root = Path(tmp)
            (root / "_CoqProject").write_text("listed.v\n")
            for name in ["listed.v", "unlisted.v", "nested/a.v", ".hidden/b.v", "output/omit.v", ".git/omit.v"]:
                p = root / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("Definition x := 0.\n")
            external = Path(outside) / "external.v"
            external.write_text("Definition x := 1.\n")
            (root / "external").symlink_to(outside, target_is_directory=True)
            (root / "linked.v").symlink_to(external)
            self.assertEqual([str(p.relative_to(root)) for p in discover(root, root / "output")],
                             [".hidden/b.v", "listed.v", "nested/a.v", "unlisted.v"])
            (root / "nested/_RocqProject").write_text("-Q . Nested\n")
            self.assertEqual(configuration(root / "nested/a.v", root), root / "nested/_RocqProject")

    def test_glob_must_match_source_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "a.v"
            data = b"Definition x := 0.\n"
            path.with_suffix(".glob").write_text("DIGEST " + hashlib.md5(data).hexdigest() + "\nFA\ndef 11:11 <> x\n")
            self.assertTrue(Glob.load(path, data).valid)
            self.assertFalse(Glob.load(path, data + b"\n").valid)

    def test_changed_project_dependency_invalidates_resolution_data(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "_CoqProject").write_text("-Q . P\n")
            (root / "A.v").write_text("Definition x := 0.\n")
            (root / "A.vo").write_bytes(b"compiled dependency")
            path = root / "B.v"
            data = b"From P Require Import A.\nDefinition y := A.x.\n"
            path.write_bytes(data)
            glob = path.with_suffix(".glob")
            glob.write_text("DIGEST " + hashlib.md5(data).hexdigest() + "\nFP.B\nR22:22 P.A <> <> lib\ndef 35:35 <> y\n")
            self.assertTrue(Source.load(path, root).glob.valid)
            newer = glob.stat().st_mtime + 2
            os.utime(root / "A.vo", (newer, newer))
            self.assertFalse(Source.load(path, root).glob.valid)

    def test_template_validation_and_scope_matching(self):
        base = {"kind": "notation", "key": "_ + _", "arity": 2, "label": "add"}
        for bad in ([0], [0, 0], [0, 1, 2], [True, 1]):
            with self.assertRaises(DictionaryError):
                validate({**base, "slots": bad})
        with tempfile.TemporaryDirectory() as tmp:
            dictionary = Dictionary(Path(tmp) / "rules.json")
            dictionary.replace({**base, "scope": "nat_scope", "slots": [1, 0]})
            dictionary.save()
            restored = Dictionary(dictionary.path)
            self.assertIsNone(restored.match("notation", "_ + _", 2, "type_scope"))
            rule = restored.match("notation", "_ + _", 2, "nat_scope")
            rendered = restored.apply(rule, Token("+", identity="Project.add"), [leaf("a"), leaf("b")])
            self.assertEqual(rendered.plain(), "add(b, a)")
            self.assertEqual(rendered.label.identity, "Project.add")
            restored.remove(rule)
            restored.save()
            self.assertEqual(Dictionary(dictionary.path).rules, [])
            dictionary.path.write_text('{"version":2,"rules":[]}')
            with self.assertRaises(DictionaryError):
                Dictionary(dictionary.path)

    def test_notation_identity_prevents_cross_module_rule_reuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            dictionary = Dictionary(Path(tmp) / "rules.json")
            dictionary.replace({"kind":"notation", "key":"_ ∗ _", "arity":2,
                                "label":"separately", "scope":"bi_scope", "identity":"Iris.sep"})
            self.assertIsNotNone(dictionary.match("notation", "_ ∗ _", 2, "bi_scope", identity="Iris.sep"))
            self.assertIsNone(dictionary.match("notation", "_ ∗ _", 2, "bi_scope", identity="User.multiply"))

    def test_unresolved_short_reference_does_not_guess_a_project_symbol(self):
        source = Source(Path("/tmp/A.v"), Path("/tmp"), "value", "Project.A", Glob())
        adapter = Adapter(source, Dictionary(DEFAULT_DICTIONARY), {"Project.A.value"})
        node = {"v": ["Ser_Qualid", ["DirPath", []], ["Id", "value"]], "loc": {"bp": 0, "ep": 5}}
        self.assertEqual(adapter.ref(node, {}).identity, "value")

    def test_backend_versions_crashes_and_timeouts_are_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "coq-lsp"
            fake.write_text('#!/usr/bin/env python3\nprint("99.0")\n')
            fake.chmod(0o755)
            with self.assertRaisesRegex(BackendError, "unsupported coq-lsp"):
                Backend(root, binary=str(fake))
            fake.write_text('#!/usr/bin/env python3\nimport sys,time\nif "--version" in sys.argv: print("0.2.5")\nelse: time.sleep(10)\n')
            with self.assertRaisesRegex(BackendError, "timed out"):
                Backend(root, timeout=.1, binary=str(fake))
            fake.write_text('#!/usr/bin/env python3\nimport sys\nif "--version" in sys.argv: print("0.2.5")\n')
            with self.assertRaisesRegex(BackendError, "closed its output"):
                Backend(root, timeout=1, binary=str(fake))

    def test_inline_and_multiline_scope(self):
        self.assertEqual(Doc(Token("f"), [leaf("x"), leaf("y")]).plain(), "f(x, y)")
        document = Doc(Token("forall"), [Doc(Token("body"), [leaf("x")], block=True)], block=True)
        self.assertEqual(document.plain(), "forall:\n    body:\n        x")
        self.assertNotIn("(", document.plain())
        long_call = Doc(Token("f"), [leaf("x" * 60), leaf("y" * 60)]).plain()
        self.assertTrue(long_call.startswith("f:\n    "))
        self.assertNotIn("(", long_call)
        self.assertTrue(anchor("A.Σ").isascii())

    def test_html_escapes_source_and_template_labels(self):
        from tools.rocq_readable.layout import render_html
        document = Doc(Token('<script>alert("x")</script>'), [leaf("a < b & c")])
        rendered = render_html(document, Path("/tmp/a.html"), {})
        self.assertNotIn("<script>", rendered)
        self.assertIn("&lt;script&gt;", rendered)
        self.assertIn("&amp;", rendered)

    def test_learning_preview_save_reject_remove_and_cancel(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dictionary = Dictionary(root / "rules.json")
            encounters = {("application", "P.f", 2, None, None): (Token("f", identity="P.f"), [leaf("a"), leaf("b")], "f a b")}
            with patch("builtins.input", side_effect=["1", '{"label":"pair","slots":[0]}', "1", '{"label":"pair","slots":[0,1]}', "n", "1", '{"label":"pair","slots":[1,0]}', "y", "done"]), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "out")
            self.assertTrue((root / "out/rule-preview.html").exists())
            self.assertEqual(Dictionary(dictionary.path).rules[0]["slots"], [1, 0])
            with patch("builtins.input", side_effect=["remove 1", "y", "done"]), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "out")
            self.assertEqual(Dictionary(dictionary.path).rules, [])
            with patch("builtins.input", side_effect=EOFError), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "out")


def backend_available():
    try:
        return bool(executable())
    except BackendError:
        return False


@unittest.skipUnless(backend_available(), "install the pinned coq-lsp backend for integration tests")
class RocqIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name).resolve()
        (cls.root / "_CoqProject").write_text("-Q . readable_test\n")
        (cls.root / "A.v").write_text('''From Coq Require Import List Arith.
Import ListNotations.
Module Inner.
Definition value : nat := 1.
End Inner.
Definition value : nat := 2.
Definition id (x : nat) : nat := x.
Fixpoint count (xs : list nat) : nat := match xs with [] => 0 | x :: rest => S (count rest) end.
Inductive color := Red | Blue.
Record box := Box { item : nat; flag : bool }.
Section Example.
Context {A : Type}.
Definition shadow (value : nat) : nat := value.
Definition lambda_shadow (x : nat) := fun x : nat => x.
Lemma law (x : nat) : forall y : nat, x = y -> id x = y.
Proof. intros y H. exact H. Qed.
End Example.
''')
        (cls.root / "B.v").write_text('''From readable_test Require Import A.
Definition use := A.id A.value.
Definition inner := A.Inner.value.
Definition red := A.Red.
Definition field (b : A.box) := A.item b.
''')
        binary = Path(executable()).with_name("coqc")
        for name in ("A", "B"):
            subprocess.run([str(binary), "-Q", ".", "readable_test", name + ".v"], cwd=cls.root,
                           check=True, capture_output=True, timeout=60)
        with redirect_stderr(io.StringIO()):
            cls.sources, cls.resolutions = prepare([cls.root / "A.v", cls.root / "B.v"], cls.root, 30)
        errors = [e for source in cls.sources for e in source.errors]
        if errors:
            raise AssertionError(errors)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_whole_project_links_shadowing_types_and_no_proofs(self):
        output = self.root / "html"
        dictionary = Dictionary(DEFAULT_DICTIONARY)
        dictionary.replace({"kind": "application", "key": "readable_test.A.id", "arity": 1,
                            "label": "identity", "slots": [0]})
        generate(self.sources, self.resolutions, dictionary, output)
        audit_links(output)
        a, b = (output / "A.html").read_text(), (output / "B.html").read_text()
        self.assertNotIn("Proof.", a)
        self.assertNotIn("intros y", a)
        self.assertNotIn("Qed.", a)
        self.assertIn('A.html#' + anchor("readable_test.A.id"), b)
        self.assertIn('A.html#' + anchor("readable_test.A.Red"), b)
        self.assertIn('A.html#' + anchor("readable_test.A.item"), b)
        self.assertIn('>identity</a>', b)
        self.assertNotIn('href="http', a + b)
        self.assertIn('href="#' + anchor("readable_test.A.shadow") + '-binder-', a)
        first = {str(p.relative_to(output)): p.read_bytes() for p in output.rglob("*") if p.is_file()}
        generate(self.sources, self.resolutions, dictionary, output)
        self.assertEqual(first, {str(p.relative_to(output)): p.read_bytes() for p in output.rglob("*") if p.is_file()})

    def test_selected_statement_does_not_require_proof(self):
        path = self.root / "Unfinished.v"
        path.write_text("(* A leading comment: Σ *)\nDefinition id (x : nat) := x.\nLemma unfinished : id 0 = 0.\nProof. THIS_IS_NOT_A_TACTIC.\n")
        with redirect_stderr(io.StringIO()):
            sources, resolutions = prepare([path], self.root, 30, selected="unfinished")
        self.assertEqual(sources[0].errors, [])
        self.assertEqual(sources[0].declarations[-1].name, "unfinished")
        self.assertNotIn("THIS_IS_NOT_A_TACTIC", sources[0].declarations[-1].source)

    def test_single_cli_strict_unknown_rules_and_ambiguous_names(self):
        rules = self.root / "empty-rules.json"
        rules.write_text('{"version":1,"rules":[]}')
        output = self.root / "standalone"
        output.mkdir(exist_ok=True)
        (output / "index.html").write_text("existing index")
        (output / "style.css").write_text("existing style")
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                status = main(["render", "A.v", "--name", "law", "--output", "standalone/law.html",
                               "--dictionary", str(rules), "--strict"])
                ambiguous = main(["render", "A.v", "--name", "value", "--output", "standalone/ambiguous.html"])
            self.assertEqual(status, 1)
            self.assertEqual(ambiguous, 1)
            self.assertFalse((output / "ambiguous.html").exists())
            self.assertEqual((output / "index.html").read_text(), "existing index")
            self.assertEqual((output / "style.css").read_text(), "existing style")
            page = (output / "law.html").read_text()
            self.assertNotIn("Proof.", page)
            self.assertNotIn('href="index.html"', page)
            self.assertIn("unsupported or unmapped constructs", page)
            self.assertIn("notation &quot;_", page)
            self.assertTrue(json.loads((output / "law.report.json").read_text())["files"][0]["unsupported"])
            audit_links(output)
        finally:
            os.chdir(previous)

    def test_bad_file_does_not_prevent_other_pages_and_returns_failure(self):
        (self.root / "Broken.v").write_text("Definition broken : nat := missing_symbol.\n")
        (self.root / "Malformed.v").write_bytes(b"Definition malformed := \xff.\n")
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                status = main(["build", "--output", "partial-html"])
            self.assertEqual(status, 1)
            self.assertTrue((self.root / "partial-html/A.html").exists())
            report = json.loads((self.root / "partial-html/report.json").read_text())
            self.assertTrue(next(f for f in report["files"] if f["file"] == "Malformed.v")["errors"])
            audit_links(self.root / "partial-html")
        finally:
            os.chdir(previous)
            (self.root / "Broken.v").unlink()
            (self.root / "Malformed.v").unlink()
            (self.root / "Unfinished.v").unlink(missing_ok=True)

    def test_cjr_contracts_and_definition_vocabulary(self):
        dictionary = Dictionary(DEFAULT_DICTIONARY)
        models = []
        for file, selected, expected in [("swap", "swap_wp", "consuming_implies"),
                                          ("list", "is_list", "exists"),
                                          ("array", "array_cells", "separately_for_each_index_and_item"),
                                          ("most_frequent", "most_frequent_spec", "forall")]:
            path = ROOT / f"theories/examples/{file}.v"
            with redirect_stderr(io.StringIO()):
                sources, resolutions = prepare([path], ROOT, 60, selected=selected)
            self.assertEqual(sources[0].errors, [], file)
            models.extend(sources)
            declaration = next(d for d in sources[0].declarations if d.name == selected)
            adapter = Adapter(sources[0], dictionary, {d.identity for d in sources[0].declarations})
            document = adapter.declaration(declaration)
            self.assertIn(expected, document.plain())
            self.assertNotIn("Proof.", declaration.source)
        output = self.root / "cjr-html"
        generate(models, {}, dictionary, output)
        audit_links(output)


if __name__ == "__main__":
    unittest.main()
