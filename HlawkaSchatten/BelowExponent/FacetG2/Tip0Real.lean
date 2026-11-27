/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Tip0Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Tip0Base : Fin 3 → Row := ![![877/1000, 1/10, 23/1000], ![877/1000, 99/1000, 3/125], ![523/600, 313/3000, 3/125]]
def g2Tip0Pi : Profile := ![4719941/134217728, 128942279/536870912, 7610057/33554432, 267287957/536870912]
def g2Tip0Slope : Row := ![63803323/134217728, -12489037/67108864, -315191991/1073741824]

def g2Tip0Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Tip0Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![211347/524288, 106377/262144, 234493/524288]
private def gammaBound : Fin 3 → ℝ := ![12548341/1048576, 12025307/1048576, 12025307/1048576]

theorem g2Tip0_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Tip0 v cap = g2Tip0Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Tip0, Tangent.vertex, g2Tip0Vertex, g2Tip0Base, facetCap]

theorem g2Tip0_pi_agrees : realPi g2Tip0 = g2Tip0Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Tip0, g2Tip0Pi, weightDen]

theorem g2Tip0_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Tip0 v cap = prismWeight g2Tip0Pi g2Tip0Slope (g2Tip0Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Tip0, weightDen, g2Tip0Pi,
      g2Tip0Slope, g2Tip0Vertex, g2Tip0Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Tip0_pi : IsSimplex g2Tip0Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Tip0Pi]
  · norm_num [g2Tip0Pi, Fin.sum_univ_succ]

theorem g2Tip0_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Tip0Pi g2Tip0Slope (g2Tip0Vertex v cap) j) ∧
      (∑ j, prismWeight g2Tip0Pi g2Tip0Slope (g2Tip0Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Tip0Vertex, g2Tip0Pi, g2Tip0Slope, g2Tip0Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Tip0Vertex, g2Tip0Pi, g2Tip0Slope, g2Tip0Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Tip0Base v) g2Tip0Pi (facetWeight g2Tip0Pi (g2Tip0Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Tip0_pi)
  · fin_cases v <;> norm_num [g2Tip0Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Tip0Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Tip0Base, g2Tip0Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Tip0Base, g2Tip0Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Tip0Base, g2Tip0Pi, lam, Fin.castSucc]

theorem g2Tip0_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Tip0Base v)) g2Tip0Pi (facetWeight g2Tip0Pi (g2Tip0Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Tip0_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Tip0 i cap) (realPi g2Tip0) (realGamma g2Tip0 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Tip0Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Tip0_vertices_agree g2Tip0_pi_agrees g2Tip0_gamma_agrees g2Tip0_pi
    (fun i cap => (g2Tip0_weights i cap).1) (fun i cap => (g2Tip0_weights i cap).2)
    (fun i _ hx => g2Tip0_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
