"""Join all exact F data proofs to the real balanced-strip theorem."""

import argparse
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "FSlabData"
WEIGHT = runpy.run_path(str(HERE / "f-slab-data.py"))["slab_weight"]


def slab(i):
    mu = int(100*WEIGHT(i))
    body = [f"theorem slab{i}_ok : SlabChecked {i} := by", "  intro cap side", "  cases cap <;> cases side"]
    imports = []
    for n in (i,i+1):
        imports.append(f"public import HlawkaSchatten.BelowExponent.FSlabData.Knot{n}Weight{mu}")
        for side in ("Low", "High"):
            root = f"k{n}w{mu}{side}Chart"
            body.append(f"  · exact checkedOfCharts {root}0_ok {root}1_ok {root}2_ok")
    return imports, body + [""]


def write_range(start, stop):
    imports = []
    proof = []
    for i in range(start, stop):
        deps, body = slab(i)
        imports.extend(deps)
        proof.extend(body)
    lines = ["module", "", "public import HlawkaSchatten.BelowExponent.FSlabSchedule", *dict.fromkeys(imports), "",
             "public section", "", "namespace HlawkaSchatten.BelowExponent.FSlabCheck", "", *proof,
             "end HlawkaSchatten.BelowExponent.FSlabCheck", ""]
    (PROJECT / f"Slabs{start}.lean").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group-size", type=int, default=39)
    args = parser.parse_args()
    groups = range(0, 156, args.group_size)
    for start in groups:
        write_range(start, min(start+args.group_size, 156))
    imports = [f"public import HlawkaSchatten.BelowExponent.FSlabData.Slabs{i}" for i in groups]
    dispatch = [f"  · exact slab{i}_ok" for i in range(156)]
    module_doc = [
        "",
        "/-!",
        "# Balanced certificates for the facet strip",
        "",
        "Each of the 156 slabs has a fixed weight and a checked row bound. The finite case split",
        "combines these certificates into `SlabChecked i` for every index. The schedule places an",
        "ordered profile in this family or in the adjoining balanced-edge region.",
        "-/",
    ]
    result = ["module", "", *imports, *module_doc, "",
              'set_option autoImplicit false', 'set_option relaxedAutoImplicit false', 'set_option linter.mathlibStandardSet true',
              "", "public section", "", "namespace HlawkaSchatten.BelowExponent", "", "open FSlabCheck", "",
              "private theorem allChecked (i : Fin 156) : SlabChecked i := by", "  fin_cases i", *dispatch, "",
              "theorem rowAt_facetStrip_balanced {t : Profile} (ht : OrderedInterior t)",
              "    (hf₀ : 1 / 64 ≤ facetCoord t) (hf₁ : facetCoord t ≤ 1 / 20)",
              "    (hτ : tau t ≤ 3 / 4) (hd : t 3 ≤ 1 / 400) : RowAt criticalQ t :=",
              "  rowAt_facetStrip_of_scheduled_checks allChecked ht hf₀ hf₁ hτ hd", "", "end HlawkaSchatten.BelowExponent", ""]
    (PROJECT / "Complete.lean").write_text("\n".join(result))


if __name__ == "__main__":
    main()
