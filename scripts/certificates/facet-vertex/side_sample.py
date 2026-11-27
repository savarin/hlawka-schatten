#!/usr/bin/env python3
"""Reproduce the outer side-corner trees at one point and compare the release source."""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import layout  # noqa: E402  (scripts/certificates/layout.py)


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SUPPORT = [
    Path("SideCertificateSupport/RootTable.lean"),
    Path("SideCertificateSupport/WidePrepare.lean"),
]
TARGETS = [
    "HlawkaSchatten.BelowExponent.Vertex.SideCutCorners.PointTable", "HlawkaSchatten.BelowExponent.Vertex.SideOuterWideCheck",
    "HlawkaSchatten.BelowExponent.Vertex.SideOuterTreeSearch", "HlawkaSchatten.BelowExponent.Vertex.SideCornerData.RowTables",
    "HlawkaSchatten.BelowExponent.Vertex.CornerPointData",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("point", nargs="?", type=int, default=0, choices=range(880),
                        metavar="POINT", help="index between 0 and 879 (default 0)")
    args = parser.parse_args()
    subprocess.run(["lake", "build", *TARGETS], cwd=ROOT, check=True)
    prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True)
    lean = Path(prefix.strip()) / "bin/lean"
    paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True)
    with tempfile.TemporaryDirectory(prefix="hlawka-side-witness-") as temp:
        work = Path(temp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(work), paths.strip()]))
        for source in SUPPORT:
            obj = (work / source).with_suffix(".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run([lean, "-R", HERE / "support", "-o", obj, HERE / "support" / source],
                           cwd=ROOT, env=env, check=True)
        driver = HERE / "support/SideSample.lean"
        subprocess.run([lean, "--run", driver, work, str(args.point)],
                       cwd=ROOT, env=env, check=True)
        name = f"Wide{args.point:03}.lean"
        expected = ROOT / "HlawkaSchatten/BelowExponent/Vertex/SideCutCorners" / name
        place = expected.relative_to(ROOT).as_posix()
        data = layout.to_repo(place, (work / name).read_text(encoding="utf-8"), ROOT).encode("utf-8")
        if data != expected.read_bytes():
            raise SystemExit(f"Generated output differs from {expected.relative_to(ROOT)}")
        print(f"{hashlib.sha256(data).hexdigest()}  {expected.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
