import tempfile
import unittest
import csv
import json
from pathlib import Path

from tools.project_tools.benchmark import normalize
from tools.project_tools.docs import HTMLInfo, check_links
from tools.project_tools.docs import hashes
from tools.project_tools.benchmark import load_config, render
from tools.project_tools.examples import PROGRAMS, ROOT, code_path
from tools.rocq_readable.project import configuration, module_name


class ProjectToolTests(unittest.TestCase):
    def test_report_inventory_reads_rendered_declaration_articles(self):
        page = HTMLInfo('<nav aria-label="Project"><a href="index.html">Home</a></nav>'
                        '<article id="symbol-a"><h2>array_cells</h2><p>description</p></article>'
                        '<article id="symbol-b"><h2>array_get</h2></article>')
        self.assertEqual(page.declarations, [("#symbol-a", "array_cells"), ("#symbol-b", "array_get")])

    def test_relocated_examples_preserve_logical_names_and_compile_inputs(self):
        for line in (ROOT / '_CoqProject').read_text().splitlines():
            if not line.endswith('.v'):
                continue
            path = ROOT / line
            self.assertTrue(path.is_file(), line)
            identity = module_name(path, configuration(path, ROOT), ROOT)
            if '/rocq/' in line:
                self.assertEqual(identity, 'cjr.examples.' + path.stem)
            elif line.startswith('example/quadtree/'):
                self.assertEqual(identity, 'cjr.quadtree.' + '.'.join(path.relative_to(ROOT / 'example/quadtree').with_suffix('').parts))
        for program in PROGRAMS:
            self.assertTrue(code_path(program).is_file(), program)
            self.assertTrue((code_path(program).parents[1] / 'test' / (program + '_test.cj')).is_file())
        for config in (ROOT / 'example').glob('*/benchmark/benchmark.config.json'):
            data, root = load_config(config)
            for job in data['jobs']:
                for relative in [*job['sources'], *job.get('harness_sources', [])]:
                    self.assertTrue((root / relative).is_file(), str(config) + ': ' + relative)
                    self.assertTrue((root / relative).resolve().is_relative_to(ROOT))
                command = render(job['compile'], {'root': root, 'cjc': 'cjc', 'binary': '/tmp/test-binary'})
                for arg in command:
                    if arg.endswith('.cj'):
                        self.assertTrue(Path(arg).is_file(), arg)

    def test_benchmark_partitions_retain_all_original_measurements(self):
        historical = ROOT / 'paper/benchmark-history'
        with (historical / 'raw.csv').open() as stream:
            original = list(csv.DictReader(stream))
        records = []
        for name in ('list', 'array', 'array_list', 'hash_map'):
            output = ROOT / 'example' / name / 'benchmark/results'
            with (output / 'raw.csv').open() as stream:
                partition = list(csv.DictReader(stream))
            records.extend(partition)
            data = json.loads((output / 'metadata.json').read_text())
            self.assertTrue(data['historical'])
            self.assertEqual(data['samples'], len(partition))
            original_metadata = json.loads((historical / 'metadata.json').read_text())
            self.assertEqual(data['date_utc'], original_metadata['date_utc'])
            self.assertEqual(data['sources'], original_metadata['sources'])
        key = lambda row: tuple(sorted(row.items()))
        self.assertCountEqual([key(row) for row in records], [key(row) for row in original])

    def test_nested_example_provenance_tracks_shared_and_sibling_sources(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for relative in ('theories/lang.v', 'tools/project_tools/docs.py',
                             'tools/extraction/rocq/cj_print.v', 'example/array/rocq/array.v'):
                path = root / relative; path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('initial')
            project = root / 'example/quadtree'; project.mkdir()
            before = hashes(project)
            shared = root / 'tools/extraction/rocq/cj_print.v'
            shared.write_text('changed')
            after = hashes(project)
            self.assertIn('../array/rocq/array.v', before)
            self.assertNotEqual(before['../../tools/extraction/rocq/cj_print.v'],
                                after['../../tools/extraction/rocq/cj_print.v'])

    def test_benchmark_rows_preserve_dimensions_and_normalize_time(self):
        row = normalize(
            {"name": "range", "dimensions": {"distribution": "uniform"}},
            {"n": "256", "workload": "selective", "implementation": "CJR",
             "trial": "2", "repetitions": "4", "elapsed_ns": "800", "checksum": "11"},
            1,
        )
        self.assertEqual(row["distribution"], "uniform")
        self.assertEqual(row["n"], 256)
        self.assertEqual(row["checksum"], 11)
        self.assertEqual(row["process"], 1)
        self.assertEqual(row["ns_per_operation"], 200)

    def test_link_checker_accepts_local_destination_and_fragment(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "index.html").write_text('<a href="child.html#decl">child</a>')
            (root / "child.html").write_text('<h1 id="decl">declaration</h1>')
            check_links(root)

    def test_link_checker_rejects_links_outside_project(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "index.html").write_text('<a href="../outside.html">outside</a>')
            with self.assertRaisesRegex(RuntimeError, "leaves project"):
                check_links(root)

    def test_link_checker_rejects_missing_fragment(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "index.html").write_text('<a href="child.html#missing">child</a>')
            (root / "child.html").write_text('<h1 id="present">declaration</h1>')
            with self.assertRaisesRegex(RuntimeError, "missing local anchor"):
                check_links(root)


if __name__ == "__main__":
    unittest.main()
