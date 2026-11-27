"""Generate exact cone and assembly proofs for the translated facet prisms."""

import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "FacetArchive"
WEIGHT_DEN = 2**30
WITNESS_DEN = 2**20


def vector(items):
    return "![" + ", ".join(map(str, items)) + "]"


def cone_bounds(base, p, rho):
    gamma = [1 - p[3] - p[j] + (2 * p[3] - 1) * base[j] for j in range(3)]

    def pair(j, k):
        l = 3 - j - k
        a, b = base[j], base[k]
        return 1 + (p[l] - (p[j] + p[l]) * a - (p[k] + p[l]) * b) / (a * b)

    lam = min(pair(j, k) for j, k in combinations(range(3), 2))
    bound = max(g / b for g, b in zip(gamma, base, strict=True))
    upper = Q(8, 3) if rho == Q(1, 4) else 1 / (1 - 2 * rho)**2

    def valid(lower, ceiling):
        return lower >= 0 and rho * (1 + 2 * upper) * (2 - Q(1054, 665)) * ceiling <= 3 * lower

    rounded = (Q((lam * WITNESS_DEN).__floor__(), WITNESS_DEN), Q((bound * WITNESS_DEN).__ceil__(), WITNESS_DEN))
    if valid(*rounded):
        return rounded
    assert valid(lam, bound), (base, lam, bound, rho)
    return lam, bound


def encode(region, index, record):
    name = f"f{region}Archived{index}"
    mod = f"F{region}Prism{index}"
    base = [tuple(map(Q, row)) for row in record["triangle"]]
    pi = [Q(v, WEIGHT_DEN) for v in record["p"]]
    rho = Q(record["rho"])
    intervals = list(zip(*(cone_bounds(v, pi, rho) for v in base), strict=True))
    upper = Q(8, 3) if rho == Q(1, 4) else 1 / (1 - 2 * rho)**2
    upper_proof = ("exact facetCritical_quarter.le" if rho == Q(1, 4) else
                   f"convert facetCritical_inverse_square (R := {2*rho}) (by norm_num) (by norm_num) using 1\n    <;> norm_num")
    replacements = {"@MOD": mod, "@NAME": name, "@BASE": vector(vector(row) for row in base),
                    "@PI": vector(pi), "@SLOPE": vector(Q(x, WEIGHT_DEN) for x in record["slopes"]),
                    "@LAM": vector(intervals[0]), "@GAMMA": vector(intervals[1]), "@RHO": str(rho),
                    "@UPPERPROOF": upper_proof, "@UPPER": str(upper)}
    template = """module

public import HlawkaSchatten.BelowExponent.FacetArchive.@MODData
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def @NAMEBase : Fin 3 → Row := @BASE
private def pi : Profile := @PI
private def slope : Row := @SLOPE
private def lam : Fin 3 → ℝ := @LAM
private def gammaBound : Fin 3 → ℝ := @GAMMA

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (@NAMEBase v) pi (facetWeight pi (@NAMEBase v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [@NAMEBase, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [@NAMEBase]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, @NAMEBase, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, @NAMEBase, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, @NAMEBase, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (@RHO) x) :
    WeightedRow criticalQ (facetBase (@NAMEBase v)) pi (facetWeight pi (@NAMEBase v)) x := by
  apply facetCritical_cone_of_budget (U := @UPPER) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · @UPPERPROOF
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem @NAME_rows : FacetArchiveTriangle criticalQ @NAMEBase := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := @NAME) (slope := slope)
    _ _ _ _ _ _ @NAME_data_ok ![@NAMEChart0, @NAMEChart1, @NAMEChart2] _
    facetRowTangent_le (prismCornerSound_of_numeric @NAME_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, @NAME, Tangent.vertex, @NAMEBase, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, @NAME, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, @NAME, weightDen,
        pi, slope, @NAMEBase, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, @NAMEBase, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, @NAMEBase, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [@NAME] using hx
  · intro j
    fin_cases j
    · exact @NAMEChart0_ok
    · exact @NAMEChart1_ok
    · exact @NAMEChart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
"""
    for key, value in replacements.items():
        template = template.replace(key, value)
    if record.get("mixed", False):
        template = template.replace("rowAt_facetPrism_of_tangents", "rowAt_facetPrism_of_mixed")
        template = template.replace(f"    facetRowTangent_le (prismCornerSound_of_numeric {name}_data_ok)\n", "")
    target = PROJECT / f"{mod}Real.lean"
    if not target.exists() or target.read_text() != template:
        target.write_text(template)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    records = json.loads(parser.parse_args().manifest.read_text())
    for region, item in enumerate(records):
        for index, record in enumerate(item["cells"], start=1):
            if record["boxes"] is not None:
                encode(region, index, record)


if __name__ == "__main__":
    main()
