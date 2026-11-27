/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper13Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper13Base : Fin 3 → Row := ![![5059/6000, 379/3000, 61/2000], ![10273/12000, 7/60, 109/4000], ![1681/2000, 129/1000, 61/2000]]
def g2Upper13Pi : Profile := ![44161709/1073741824, 124613519/536870912, 246070383/1073741824, 267141347/536870912]
def g2Upper13Slope : Row := ![30296531/67108864, -92670823/536870912, -38072411/134217728]

def g2Upper13Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper13Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![487353/1048576, 201219/524288, 418751/1048576]
private def gammaBound : Fin 3 → ℝ := ![2347199/262144, 2627291/262144, 2347199/262144]

theorem g2Upper13_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper13 v cap = g2Upper13Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper13, Tangent.vertex, g2Upper13Vertex, g2Upper13Base, facetCap]

theorem g2Upper13_pi_agrees : realPi g2Upper13 = g2Upper13Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper13, g2Upper13Pi, weightDen]

theorem g2Upper13_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper13 v cap = prismWeight g2Upper13Pi g2Upper13Slope (g2Upper13Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper13, weightDen, g2Upper13Pi,
      g2Upper13Slope, g2Upper13Vertex, g2Upper13Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper13_pi : IsSimplex g2Upper13Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper13Pi]
  · norm_num [g2Upper13Pi, Fin.sum_univ_succ]

theorem g2Upper13_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper13Pi g2Upper13Slope (g2Upper13Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper13Pi g2Upper13Slope (g2Upper13Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper13Vertex, g2Upper13Pi, g2Upper13Slope, g2Upper13Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper13Vertex, g2Upper13Pi, g2Upper13Slope, g2Upper13Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper13Base v) g2Upper13Pi (facetWeight g2Upper13Pi (g2Upper13Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper13_pi)
  · fin_cases v <;> norm_num [g2Upper13Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper13Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper13Base, g2Upper13Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper13Base, g2Upper13Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper13Base, g2Upper13Pi, lam, Fin.castSucc]

theorem g2Upper13_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper13Base v)) g2Upper13Pi (facetWeight g2Upper13Pi (g2Upper13Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper13_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper13 i cap) (realPi g2Upper13) (realGamma g2Upper13 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper13Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper13_vertices_agree g2Upper13_pi_agrees g2Upper13_gamma_agrees g2Upper13_pi
    (fun i cap => (g2Upper13_weights i cap).1) (fun i cap => (g2Upper13_weights i cap).2)
    (fun i _ hx => g2Upper13_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
