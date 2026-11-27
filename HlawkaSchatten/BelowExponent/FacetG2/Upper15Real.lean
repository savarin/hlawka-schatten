/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper15Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper15Base : Fin 3 → Row := ![![5059/6000, 379/3000, 61/2000], ![10289/12000, 173/1500, 109/4000], ![10273/12000, 7/60, 109/4000]]
def g2Upper15Pi : Profile := ![44001153/1073741824, 254560375/1073741824, 240904735/1073741824, 534275561/1073741824]
def g2Upper15Slope : Row := ![123158411/268435456, -92604875/536870912, -78153649/268435456]

def g2Upper15Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper15Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![438599/1048576, 424439/1048576, 110033/262144]
private def gammaBound : Fin 3 → ℝ := ![9554407/1048576, 10694527/1048576, 10694527/1048576]

theorem g2Upper15_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper15 v cap = g2Upper15Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper15, Tangent.vertex, g2Upper15Vertex, g2Upper15Base, facetCap]

theorem g2Upper15_pi_agrees : realPi g2Upper15 = g2Upper15Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper15, g2Upper15Pi, weightDen]

theorem g2Upper15_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper15 v cap = prismWeight g2Upper15Pi g2Upper15Slope (g2Upper15Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper15, weightDen, g2Upper15Pi,
      g2Upper15Slope, g2Upper15Vertex, g2Upper15Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper15_pi : IsSimplex g2Upper15Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper15Pi]
  · norm_num [g2Upper15Pi, Fin.sum_univ_succ]

theorem g2Upper15_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper15Pi g2Upper15Slope (g2Upper15Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper15Pi g2Upper15Slope (g2Upper15Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper15Vertex, g2Upper15Pi, g2Upper15Slope, g2Upper15Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper15Vertex, g2Upper15Pi, g2Upper15Slope, g2Upper15Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper15Base v) g2Upper15Pi (facetWeight g2Upper15Pi (g2Upper15Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper15_pi)
  · fin_cases v <;> norm_num [g2Upper15Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper15Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper15Base, g2Upper15Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper15Base, g2Upper15Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper15Base, g2Upper15Pi, lam, Fin.castSucc]

theorem g2Upper15_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper15Base v)) g2Upper15Pi (facetWeight g2Upper15Pi (g2Upper15Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper15_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper15 i cap) (realPi g2Upper15) (realGamma g2Upper15 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper15Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper15_vertices_agree g2Upper15_pi_agrees g2Upper15_gamma_agrees g2Upper15_pi
    (fun i cap => (g2Upper15_weights i cap).1) (fun i cap => (g2Upper15_weights i cap).2)
    (fun i _ hx => g2Upper15_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
