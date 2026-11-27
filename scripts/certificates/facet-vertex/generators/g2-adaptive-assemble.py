"""Reconstruct the exact midpoint forest and join the prism proofs in Lean."""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
TARGET = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent/FacetG2/Cover.lean"
COMPLETE = TARGET.with_name("Complete.lean")
SHAPE = runpy.run_path(str(HERE / "g2-adaptive-rational.py"))


def read_forest(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    forest = {row["path"]: row for row in rows}
    assert len(rows) == len(forest)
    leaves = sorted((row for row in rows if row["kind"] == "prism"), key=lambda row: row["leaf"])
    assert [row["leaf"] for row in leaves] == list(range(len(leaves)))
    return forest, leaves


def check_geometry(forest):
    visited = set()

    def walk(path, triangle):
        row = forest[path]
        visited.add(path)
        assert [tuple(map(Q, v)) for v in row["triangle"]] == list(triangle)
        if row["kind"] == "prism":
            return
        assert row["kind"] == "split"
        i, j = row["edge"]
        assert 0 <= i < j < 3
        mid = tuple((a+b)/2 for a, b in zip(triangle[i], triangle[j], strict=True))
        left, right = list(triangle), list(triangle)
        left[i], right[j] = mid, mid
        walk(path+"0", left)
        walk(path+"1", right)

    for i, triangle in enumerate(SHAPE["triangles"](Q(1, 20), Q(3, 125))):
        walk(str(i), triangle)
    assert visited == set(forest)


def indexed(name, count, codomain, values):
    lines = [f"def {name} (i : Fin {count}) : {codomain} :=", "  match i.val with"]
    lines.extend(f"  | {ix} => {value}" for ix, value in enumerate(values[:-1]))
    return [*lines, "  | _ => " + values[-1], ""]


def branch(lines, indent):
    return [f"{' '*indent}· {lines[0].lstrip()}", *lines[1:]]


def emit(forest, leaves, tips):
    count = len(leaves) + 2
    modules = ["Tip0", "Tip1"] + [f"Upper{row['leaf']}" for row in leaves]
    names = [f"g2{module}" for module in modules]
    lines = [
        "module", "", "public import HlawkaSchatten.BelowExponent.FacetG2.TriangleSplit",
        *(f"public import HlawkaSchatten.BelowExponent.FacetG2.{module}Real" for module in modules), "",
        "@[expose] public section", "", "namespace HlawkaSchatten.BelowExponent", "", "open FacetNumeric", "",
        "noncomputable section", "", "set_option maxRecDepth 20000",
        "set_option maxHeartbeats 0", "",
    ]
    lines += indexed("g2PrismBase", count, "Fin 3 → Row", [name+"Base" for name in names])
    lines += indexed("g2PrismData", count, "Prism", names)
    lines += indexed("g2PrismRadius", count, "ℝ", [row["rho"] for row in [*tips, *leaves]])
    lines += [
        f"def G2NumericRows (p : Fin {count}) : Prop :=",
        "  ∀ (i : Fin 3) (cap : Bool) (x : Row),",
        "    (cap = true ∨ ¬ FacetRatioCone (g2PrismRadius p) x) →",
        "    WeightedRow criticalQ (realVertex (g2PrismData p) i cap) (realPi (g2PrismData p))",
        "      (realGamma (g2PrismData p) i cap) x", "",
        f"theorem g2PrismRows_of_numeric (h : ∀ p, G2NumericRows p) (p : Fin {count}) :",
        "    G2TriangleRows criticalQ (g2PrismBase p) := by",
        "  fin_cases p",
    ]
    for i, name in enumerate(names):
        lines += [
            "  · apply g2TriangleRows_of_weights",
            "    intro w d hw hs hd₀ hd",
            f"    exact rowAt_{name}_of_numeric_rows (h {i}) hw hs hd₀ hd",
        ]
    lines += [
        "",
        f"theorem g2TriangleRoots_of_prisms (rows : ∀ p : Fin {count}, G2TriangleRows criticalQ (g2PrismBase p)) :",
        "    ∀ upper side, G2TriangleRows criticalQ (g2SliceRoot upper side) := by",
        "  intro upper side",
        "  cases upper <;> cases side",
    ]

    def leaf(index, expr, indent):
        pre = " " * indent
        return [
            pre + f"have geometry : g2PrismBase {index} = {expr} := by",
            pre + "  funext i j",
            pre + "  fin_cases i <;> fin_cases j <;>",
            pre + f"    norm_num [g2PrismBase, {names[index]}Base, g2SliceRoot, g2Root,",
            pre + "      g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,",
            pre + "      Pi.smul_apply, Pi.add_apply, smul_eq_mul]",
            pre + "rw [← geometry]",
            pre + f"exact @rows {index}",
        ]

    def section(path, expr, indent):
        row = forest[path]
        if row["kind"] == "prism":
            return leaf(row["leaf"]+2, expr, indent)
        i, j = row["edge"]
        start = " " * indent
        return [
            start + f"refine g2TriangleRows_of_bisect (i := {i}) (j := {j}) (by decide) ?_ ?_",
            *branch(section(path+"0", f"g2SplitTriangle ({expr}) {i} {j}", indent+2), indent),
            *branch(section(path+"1", f"g2SplitTriangle ({expr}) {j} {i}", indent+2), indent),
        ]

    lines += branch(leaf(0, "g2SliceRoot false false", 4), 2)
    lines += branch(leaf(1, "g2SliceRoot false true", 4), 2)
    lines += branch(section("0", "g2SliceRoot true false", 4), 2)
    lines += branch(section("1", "g2SliceRoot true true", 4), 2)
    lines += [
        "",
        "/-- The entire deep-facet region from the cap and noncone real row estimates. -/",
        "theorem rowAt_deepFacet_of_adaptive_prisms (hnumeric : ∀ p, G2NumericRows p)",
        "    {t : Profile} (ht : OrderedInterior t) (hd : t 3 ≤ 1 / 500)",
        "    (hf : facetCoord t ≤ 1 / 20) (hε : 1 / 8 ≤ vertexDepth t)",
        "    (hσ : 1 / 5 ≤ sigma t) : RowAt criticalQ t := by",
        "  apply rowAt_deepFacet_of_g2Band (t := t) (ht := ht) (hd := hd) (hf := hf) (hε := hε) (hσ := hσ)",
        "  intro b d hb hd₀ hd'",
        "  exact rowAt_g2Band_of_triangleRoots",
        "    (g2TriangleRoots_of_prisms (g2PrismRows_of_numeric hnumeric)) hb hd₀ hd'",
        "", "end", "", "end HlawkaSchatten.BelowExponent", "",
    ]
    assert len(lines) < 10_000
    TARGET.write_text("\n".join(lines))


def emit_complete(leaves):
    modules = ["Tip0", "Tip1"] + [f"Upper{row['leaf']}" for row in leaves]
    lines = """module

public import HlawkaSchatten.BelowExponent.FacetG2.Cover
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic

/-! Discharge the cap and noncone row premises of the adaptive G2 cover. -/

public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

private theorem g2CheckedRows {P : Prism} {b : Fin 3 → Row} {π : Profile} {slope : Row} {ρ : ℝ}
    (hdata : dataOK P = true) (trees : Fin 3 → RowTree)
    (hcharts : ∀ j : Fin 3, checkChart P j.val (Tangent.chartA j).val (Tangent.chartB j).val (trees j) = true)
    (hradius : (P.radiusNum : ℝ) / P.radiusDen = ρ)
    (hcap : ∀ i, (vertexAt P i true).v3 ≠ 0)
    (hvertex : ∀ i cap, realVertex P i cap = facetCap (b i) (if cap then 1 / 500 else 0))
    (hπ : realPi P = π)
    (hγ : ∀ i cap, realGamma P i cap = prismWeight π slope (facetCap (b i) (if cap then 1 / 500 else 0)))
    (hcone : ∀ i x, FacetRatioCone ρ x → WeightedRow criticalQ (facetBase (b i)) π (facetWeight π (b i)) x) :
    ∀ i cap x, WeightedRow criticalQ (realVertex P i cap) (realPi P) (realGamma P i cap) x := by
  apply prismRows_of_numeric hdata trees hcharts facetRowTangent_le (prismCornerSound_of_numeric hdata)
  intro i cap hv x hx
  rw [hradius] at hx
  cases cap
  · have hb : facetCap (b i) 0 = facetBase (b i) := by
      funext s
      fin_cases s <;> simp [facetCap, facetBase]
    have hg : prismWeight π slope (facetCap (b i) 0) = facetWeight π (b i) := by
      funext j
      fin_cases j <;> simp [prismWeight, facetWeight, facetCap, Fin.castSucc]
    rw [hvertex, hπ, hγ]
    change WeightedRow criticalQ (facetCap (b i) 0) π (prismWeight π slope (facetCap (b i) 0)) x
    rw [hg, hb]
    exact hcone i x hx
  · exact (hcap i hv).elim

set_option maxHeartbeats 0 in
theorem g2NumericRows_checked (prism : Fin COUNT) : G2NumericRows prism := by
  fin_cases prism""".replace("COUNT", str(len(modules))).splitlines()
    for i, module in enumerate(modules):
        name = f"g2{module}"
        trees = ", ".join(f"{name}Chart{j}" for j in range(3))
        lines += [
            "  · intro v cap x _",
            f"    refine g2CheckedRows (P := {name}) (b := {name}Base) (π := {name}Pi)",
            f"      (slope := {name}Slope) (ρ := g2PrismRadius {i}) {name}_data_ok ![{trees}] ?_ ?_ ?_",
            f"      {name}_vertices_agree {name}_pi_agrees {name}_gamma_agrees ?_ v cap x",
            "    · intro j",
            "      fin_cases j",
            *(f"      · exact {name}Chart{j}_ok" for j in range(3)),
            f"    · norm_num [{name}, g2PrismRadius]",
            "    · intro j",
            "      fin_cases j <;> decide",
            "    · intro j y hy",
            f"      exact {name}_cone j hy",
        ]
    lines += """

/-- The adaptive deep-facet G2 certificate with every real vertex row discharged. -/
theorem rowAt_deepFacet_adaptive {t : Profile} (ht : OrderedInterior t) (hd : t 3 ≤ 1 / 500)
    (hf : facetCoord t ≤ 1 / 20) (hε : 1 / 8 ≤ vertexDepth t)
    (hσ : 1 / 5 ≤ sigma t) : RowAt criticalQ t :=
  rowAt_deepFacet_of_adaptive_prisms g2NumericRows_checked ht hd hf hε hσ

end HlawkaSchatten.BelowExponent
""".splitlines()
    COMPLETE.write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("forest", type=Path)
    parser.add_argument("tip", type=Path)
    args = parser.parse_args()
    forest, leaves = read_forest(args.forest)
    check_geometry(forest)
    tip = [row for row in json.loads(args.tip.read_text()) if row["cone_exact"] and row["margin"] > 0]
    tip_triangles = [[tuple(map(Q, vertex)) for vertex in row["triangle"]] for row in tip]
    assert tip_triangles == [list(triangle) for triangle in SHAPE["triangles"](Q(3, 125))]
    emit(forest, leaves, tip)
    emit_complete(leaves)
    print(len(leaves)+2, "prisms with a complete exact parent-to-child geometry check")


if __name__ == "__main__":
    main()
