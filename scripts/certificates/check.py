#!/usr/bin/env python3
"""Regenerate the archived certificate families and compare the checkout byte for byte."""

import filecmp
from hashlib import file_digest
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FACETS = HERE / "facet-vertex"


def run(script, *args):
    subprocess.run([sys.executable, "-I", "-S", "-B", script, *args], cwd=ROOT, check=True)


def check_manifest(manifest):
    for row in manifest.read_text().splitlines():
        expected, name = row.split("  ", 1)
        with (ROOT / name).open("rb") as file:
            if file_digest(file, "sha256").hexdigest() != expected:
                raise ValueError(f"Hash mismatch in {name}")


def compare(source, expected):
    if not filecmp.cmp(source, expected, shallow=False):
        raise ValueError(f"Generated output differs from {expected.relative_to(ROOT)}")


def main():
    check_manifest(HERE / "regional-inputs.sha256")
    check_manifest(HERE / "g1/slabs.sha256")
    run(HERE / "g1/emit_ordinates.py", "--check")
    catalog = json.loads((FACETS / "catalog.json").read_text())
    with TemporaryDirectory(prefix="hlawka-witnesses-") as work:
        temp = Path(work)
        for family, spec in catalog["families"].items():
            out = temp / family
            run(FACETS / "emit.py", family, "--output", out)
            for row in (FACETS / spec["outputs"]).read_text().splitlines():
                _, name = row.split("  ", 1)
                compare(out / name, ROOT / name)
        slabs = temp / "g1"
        slabs.mkdir()
        run(HERE / "g1/emit_slabs.py", slabs, *map(str, range(13)))
        for path in (ROOT / "HlawkaSchatten/BelowExponent/G1CompactSlabs").glob("*.lean"):
            compare(slabs / path.name, path)
    run(HERE / "g3/central_chart.py", "--check", ROOT / "HlawkaSchatten/BelowExponent/G3PCutBands")
    run(HERE / "g3/head_literals.py", "--check", ROOT / "HlawkaSchatten/BelowExponent/G3HeadDataCore.lean")
    print("All retained witness families match the checkout.")


if __name__ == "__main__":
    main()
