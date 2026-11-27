/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper29Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper29Base : Fin 3 → Row := ![![877/1000, 99/1000, 3/125], ![10321/12000, 1313/12000, 61/2000], ![4169/4800, 127/1200, 41/1600]]
def g2Upper29Pi : Profile := ![37487143/1073741824, 247482035/1073741824, 15889027/67108864, 267274107/536870912]
def g2Upper29Slope : Row := ![507057245/1073741824, -211657919/1073741824, -75011181/268435456]

def g2Upper29Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper29Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![94223/262144, 290539/1048576, 241675/524288]
private def gammaBound : Fin 3 → ℝ := ![5795445/524288, 9119733/1048576, 5427785/524288]

theorem g2Upper29_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper29 v cap = g2Upper29Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper29, Tangent.vertex, g2Upper29Vertex, g2Upper29Base, facetCap]

theorem g2Upper29_pi_agrees : realPi g2Upper29 = g2Upper29Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper29, g2Upper29Pi, weightDen]

theorem g2Upper29_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper29 v cap = prismWeight g2Upper29Pi g2Upper29Slope (g2Upper29Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper29, weightDen, g2Upper29Pi,
      g2Upper29Slope, g2Upper29Vertex, g2Upper29Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper29_pi : IsSimplex g2Upper29Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper29Pi]
  · norm_num [g2Upper29Pi, Fin.sum_univ_succ]

theorem g2Upper29_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper29Pi g2Upper29Slope (g2Upper29Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper29Pi g2Upper29Slope (g2Upper29Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper29Vertex, g2Upper29Pi, g2Upper29Slope, g2Upper29Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper29Vertex, g2Upper29Pi, g2Upper29Slope, g2Upper29Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper29Base v) g2Upper29Pi (facetWeight g2Upper29Pi (g2Upper29Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper29_pi)
  · fin_cases v <;> norm_num [g2Upper29Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper29Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper29Base, g2Upper29Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper29Base, g2Upper29Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper29Base, g2Upper29Pi, lam, Fin.castSucc]

theorem g2Upper29_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper29Base v)) g2Upper29Pi (facetWeight g2Upper29Pi (g2Upper29Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper29_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper29 i cap) (realPi g2Upper29) (realGamma g2Upper29 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper29Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper29_vertices_agree g2Upper29_pi_agrees g2Upper29_gamma_agrees g2Upper29_pi
    (fun i cap => (g2Upper29_weights i cap).1) (fun i cap => (g2Upper29_weights i cap).2)
    (fun i _ hx => g2Upper29_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
