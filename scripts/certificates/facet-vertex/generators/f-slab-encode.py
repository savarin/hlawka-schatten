"""Emit the Lean checks for the weighted F knot records."""

import argparse
import json
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "FSlabData"


def render_tree(tree, indent=2):
    prefix = " "*indent
    kind = tree[0]
    if kind == "box":
        return [f"{prefix}(.box {tree[1]} {tree[2]})"]
    if kind in {"cone", "taylor"}:
        return [f"{prefix}(.box {10001 if kind == 'cone' else 10000} 0)"]
    return [f"{prefix}(.{kind}", *render_tree(tree[1], indent+2), *render_tree(tree[2], indent+2), f"{prefix})"]


def emit(record):
    knot = record["knot"]
    weight = int(100*Fraction(record["weight"]))
    assert record["radius"] == "1/64"
    assert [band["e"] for band in record["bands"]] == [["0", "1/4"], ["1/4", "1/2"]]
    name = f"k{knot}w{weight}"
    lines = ["module", "", "public import HlawkaSchatten.BelowExponent.FSlabCheck", "", "@[expose] public section", "",
             "namespace HlawkaSchatten.BelowExponent.FSlabCheck", "", "set_option maxRecDepth 40000", "set_option maxHeartbeats 0", ""]
    for high, band in enumerate(record["bands"]):
        side = "High" if high else "Low"
        flag = "true" if high else "false"
        lines += [f"def {name}{side} : Band := ⟨{knot}, {weight}, {flag}⟩", ""]
        for face, tree in enumerate(band["charts"]):
            label = f"{name}{side}Chart{face}"
            lines += [f"def {label} : FacetNumeric.RowTree :=", *render_tree(tree), "",
                      f"theorem {label}_ok : checkChart {name}{side} {face} {label} = true := by decide +kernel", ""]
    lines += ["end HlawkaSchatten.BelowExponent.FSlabCheck", ""]
    path = PROJECT / f"Knot{knot}Weight{weight}.lean"
    path.write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("knots", type=int, nargs="*")
    args = parser.parse_args()
    PROJECT.mkdir(exist_ok=True)
    for line in args.manifest.read_text().splitlines():
        record = json.loads(line)
        if not args.knots or record["knot"] in args.knots:
            emit(record)


if __name__ == "__main__":
    main()
