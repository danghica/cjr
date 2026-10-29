"""Compile the two generated libraries together, omitting only demo mains.

The original monomorphic source is read unchanged. Benchmark provenance hashes
both complete extracted files and this transformation, not a hand-maintained
copy of the old implementation.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path


def library(path):
    source = path.read_text()
    matches = list(re.finditer(r"^main\(\)(?:\s*:\s*Unit)?\s*\{", source, re.M))
    if len(matches) != 1:
        raise ValueError(f"expected one final demo main in {path}")
    start = matches[0].start()
    # The emitted main is the final declaration and has no braces in strings.
    depth = 0
    end = None
    for i in range(source.index("{", start), len(source)):
        depth += (source[i] == "{") - (source[i] == "}")
        if depth == 0:
            end = i + 1
            break
    if end is None or source[end:].strip():
        raise ValueError(f"demo main must be the final declaration in {path}")
    return source[:start]


def main():
    compiler, root, binary = sys.argv[1:]
    root = Path(root)
    with tempfile.TemporaryDirectory(prefix="cjr-array-comparison-") as directory:
        files = []
        for example in ("array", "poly_array"):
            source = root / f"example/{example}/extracted/{example}.cj"
            target = Path(directory) / f"{example}.cj"
            target.write_text(library(source))
            files.append(str(target))
        result = subprocess.run([
            compiler, *files,
            str(root / "tools/project_tools/benchmark_common.cj"),
            str(root / "example/poly_array/benchmark/poly_array_bench.cj"),
            "--test", "-O2", "-o", binary,
        ])
        raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
