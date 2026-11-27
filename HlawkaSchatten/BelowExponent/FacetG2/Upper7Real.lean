/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper7Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper7Base : Fin 3 → Row := ![![1681/2000, 129/1000, 61/2000], ![10273/12000, 7/60, 109/4000], ![2053/2400, 44/375, 109/4000]]
def g2Upper7Pi : Profile := ![44216323/1073741824, 250363371/1073741824, 244880143/1073741824, 534281987/1073741824]
def g2Upper7Slope : Row := ![248464337/536870912, -99726095/536870912, -151327167/536870912]

def g2Upper7Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper7Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![402771/1048576, 101847/262144, 103779/262144]
private def gammaBound : Fin 3 → ℝ := ![9426927/1048576, 5275921/524288, 5275921/524288]

theorem g2Upper7_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper7 v cap = g2Upper7Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper7, Tangent.vertex, g2Upper7Vertex, g2Upper7Base, facetCap]

theorem g2Upper7_pi_agrees : realPi g2Upper7 = g2Upper7Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper7, g2Upper7Pi, weightDen]

theorem g2Upper7_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper7 v cap = prismWeight g2Upper7Pi g2Upper7Slope (g2Upper7Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper7, weightDen, g2Upper7Pi,
      g2Upper7Slope, g2Upper7Vertex, g2Upper7Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper7_pi : IsSimplex g2Upper7Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper7Pi]
  · norm_num [g2Upper7Pi, Fin.sum_univ_succ]

theorem g2Upper7_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper7Pi g2Upper7Slope (g2Upper7Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper7Pi g2Upper7Slope (g2Upper7Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper7Vertex, g2Upper7Pi, g2Upper7Slope, g2Upper7Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper7Vertex, g2Upper7Pi, g2Upper7Slope, g2Upper7Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper7Base v) g2Upper7Pi (facetWeight g2Upper7Pi (g2Upper7Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper7_pi)
  · fin_cases v <;> norm_num [g2Upper7Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper7Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper7Base, g2Upper7Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper7Base, g2Upper7Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper7Base, g2Upper7Pi, lam, Fin.castSucc]

theorem g2Upper7_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper7Base v)) g2Upper7Pi (facetWeight g2Upper7Pi (g2Upper7Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper7_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper7 i cap) (realPi g2Upper7) (realGamma g2Upper7 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper7Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper7_vertices_agree g2Upper7_pi_agrees g2Upper7_gamma_agrees g2Upper7_pi
    (fun i cap => (g2Upper7_weights i cap).1) (fun i cap => (g2Upper7_weights i cap).2)
    (fun i _ hx => g2Upper7_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
