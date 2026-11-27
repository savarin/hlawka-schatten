"""Assemble the archived midpoint trees with their verified prism lemmas."""

import argparse
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "FacetArchive"


def qualify(region, index):
    return f"f{region}Archived{index}"


def write_root(region, node):
    imports = []
    statements = []

    def walk(current, v, address):
        name = f"f{region}Rows{address}"
        if isinstance(current, int):
            index = current
            imports.append(f"public import HlawkaSchatten.BelowExponent.FacetArchive.F{region}Prism{index}Real")
            body = f"""  have heq : {v} = {qualify(region, index)}Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [{qualify(region, index)}Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @{qualify(region, index)}_rows"""
        else:
            i, j, lhs, rhs = current
            left = walk(lhs, f"(g2SplitTriangle {v} {i} {j})", address + "0")
            right = walk(rhs, f"(g2SplitTriangle {v} {j} {i})", address + "1")
            body = f"  exact facetArchiveTriangle_of_split (i := {i}) (j := {j}) (by decide) {left} {right}"
        visibility = "" if address == "Root" else "private "
        statements.append(f"{visibility}theorem {name} : FacetArchiveTriangle criticalQ {v} := by\n{body}\n")
        return name

    walk(node, f"(facetArchiveRoot {region})", "Root")
    text = "\n".join(["module", "", *imports, "", "public section", "", "namespace HlawkaSchatten.BelowExponent.FacetNumeric", "",
                      *statements, "end HlawkaSchatten.BelowExponent.FacetNumeric", ""])
    (PROJECT / f"F{region}Root.lean").write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--regions", type=int, nargs="+", default=[0, 1, 2])
    args = parser.parse_args()
    records = json.loads(args.manifest.read_text())
    for region in args.regions:
        write_root(region, records[region]["tree"])


if __name__ == "__main__":
    main()
