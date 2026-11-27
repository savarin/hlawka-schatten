"""Write checked cone budgets and the real conditional join for each G2 prism."""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "FacetG2"
RATIONAL = runpy.run_path(str(HERE / "g2-adaptive-rational.py"))
DEN = 2**20


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def witness(record):
    tri = [tuple(map(Q, b)) for b in record["triangle"]]
    rho = Q(record["rho"])
    cone = RATIONAL["exact_budgets"](tri, rho, record["p"], record["slopes"])
    assert cone is not None
    upper = RATIONAL["taylor_upper"](rho)
    pairs = []
    for lam, gamma in cone:
        lo = (lam * DEN).__floor__()
        hi = (gamma * DEN).__ceil__()
        if rho*(1+2*upper)*(2-RATIONAL["Q_LOWER"])*hi <= 3*lo:
            lam, gamma = Q(lo, DEN), Q(hi, DEN)
        pairs.append((lam, gamma))
    return tri, rho, upper, pairs


def render(index, series, record):
    name = f"g2{series}{index}"
    data = f"{series}{index}Data"
    tri, rho, upper, pairs = witness(record)
    pi = vector(Q(k, RATIONAL["WEIGHT_DEN"]) for k in record["p"])
    slope = vector(Q(k, RATIONAL["WEIGHT_DEN"]) for k in record["slopes"])
    base = vector(vector(r) for r in tri)
    lam = vector(l for l, _ in pairs)
    gamma = vector(g for _, g in pairs)
    if rho == Q(1, 4):
        upper_proof = "exact facetCritical_quarter"
    else:
        upper_proof = (
            f"convert facetCritical_inverse_square (R := {2*rho}) (by norm_num) (by norm_num) using 1\n"
            "    <;> norm_num"
        )
    template = """module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.@DATA

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def @NAMEBase : Fin 3 → Row := @BASE
def @NAMEPi : Profile := @PI
def @NAMESlope : Row := @SLOPE

def @NAMEVertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (@NAMEBase v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := @LAM
private def gammaBound : Fin 3 → ℝ := @GAMMA

theorem @NAME_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex @NAME v cap = @NAMEVertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, @NAME, Tangent.vertex, @NAMEVertex, @NAMEBase, facetCap]

theorem @NAME_pi_agrees : realPi @NAME = @NAMEPi := by
  funext s
  fin_cases s <;> norm_num [realPi, @NAME, @NAMEPi, weightDen]

theorem @NAME_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma @NAME v cap = prismWeight @NAMEPi @NAMESlope (@NAMEVertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, @NAME, weightDen, @NAMEPi,
      @NAMESlope, @NAMEVertex, @NAMEBase, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem @NAME_pi : IsSimplex @NAMEPi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [@NAMEPi]
  · norm_num [@NAMEPi, Fin.sum_univ_succ]

theorem @NAME_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight @NAMEPi @NAMESlope (@NAMEVertex v cap) j) ∧
      (∑ j, prismWeight @NAMEPi @NAMESlope (@NAMEVertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, @NAMEVertex, @NAMEPi, @NAMESlope, @NAMEBase,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, @NAMEVertex, @NAMEPi, @NAMESlope, @NAMEBase,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (@NAMEBase v) @NAMEPi (facetWeight @NAMEPi (@NAMEBase v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := @NAME_pi)
  · fin_cases v <;> norm_num [@NAMEBase, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [@NAMEBase]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, @NAMEBase, @NAMEPi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, @NAMEBase, @NAMEPi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, @NAMEBase, @NAMEPi, lam, Fin.castSucc]

theorem @NAME_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (@RHO) x) :
    WeightedRow criticalQ (facetBase (@NAMEBase v)) @NAMEPi (facetWeight @NAMEPi (@NAMEBase v)) x := by
  apply facetCritical_cone_of_budget (U := @UPPER) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · @UPPERPROOF
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_@NAME_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (@RHO) x) →
      WeightedRow criticalQ (realVertex @NAME i cap) (realPi @NAME) (realGamma @NAME i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * @NAMEBase i j) d) :=
  rowAt_g2_prism_of_numeric_rows @NAME_vertices_agree @NAME_pi_agrees @NAME_gamma_agrees @NAME_pi
    (fun i cap => (@NAME_weights i cap).1) (fun i cap => (@NAME_weights i cap).2)
    (fun i _ hx => @NAME_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
"""
    fields = {"DATA": data, "NAME": name, "BASE": base, "PI": pi, "SLOPE": slope,
              "LAM": lam, "GAMMA": gamma, "RHO": rho, "UPPERPROOF": upper_proof, "UPPER": upper}
    for key, value in fields.items():
        template = template.replace("@"+key, str(value))
    return template


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witnesses", type=Path)
    parser.add_argument("--series", choices=("Tip", "Upper"), default="Tip")
    args = parser.parse_args()
    if args.series == "Tip":
        data = json.loads(args.witnesses.read_text())
        chosen = [(i, item) for i, item in enumerate(
            r for r in data if r["margin"] > 0 and r["cone_exact"])]
    else:
        data = [json.loads(line) for line in args.witnesses.read_text().splitlines()]
        chosen = [(r["leaf"], r) for r in data if r["kind"] == "prism"]
    for index, record in chosen:
        path = PROJECT / f"{args.series}{index}Real.lean"
        content = render(index, args.series, record)
        if not path.is_file() or path.read_text() != content:
            path.write_text(content)
        print(path.name)


if __name__ == "__main__":
    main()
