/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper3Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper3Base : Fin 3 → Row := ![![607/750, 461/3000, 37/1000], ![79/96, 43/300, 27/800], ![121/150, 469/3000, 37/1000]]
def g2Upper3Pi : Profile := ![54526277/1073741824, 240960921/1073741824, 244438915/1073741824, 533815711/1073741824]
def g2Upper3Slope : Row := ![112233815/268435456, -154408983/1073741824, -300636681/1073741824]

def g2Upper3Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper3Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![482325/1048576, 395177/1048576, 243147/524288]
private def gammaBound : Fin 3 → ℝ := ![7792999/1048576, 4272005/524288, 7792999/1048576]

theorem g2Upper3_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper3 v cap = g2Upper3Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper3, Tangent.vertex, g2Upper3Vertex, g2Upper3Base, facetCap]

theorem g2Upper3_pi_agrees : realPi g2Upper3 = g2Upper3Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper3, g2Upper3Pi, weightDen]

theorem g2Upper3_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper3 v cap = prismWeight g2Upper3Pi g2Upper3Slope (g2Upper3Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper3, weightDen, g2Upper3Pi,
      g2Upper3Slope, g2Upper3Vertex, g2Upper3Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper3_pi : IsSimplex g2Upper3Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper3Pi]
  · norm_num [g2Upper3Pi, Fin.sum_univ_succ]

theorem g2Upper3_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper3Pi g2Upper3Slope (g2Upper3Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper3Pi g2Upper3Slope (g2Upper3Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper3Vertex, g2Upper3Pi, g2Upper3Slope, g2Upper3Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper3Vertex, g2Upper3Pi, g2Upper3Slope, g2Upper3Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper3Base v) g2Upper3Pi (facetWeight g2Upper3Pi (g2Upper3Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper3_pi)
  · fin_cases v <;> norm_num [g2Upper3Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper3Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper3Base, g2Upper3Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper3Base, g2Upper3Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper3Base, g2Upper3Pi, lam, Fin.castSucc]

theorem g2Upper3_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper3Base v)) g2Upper3Pi (facetWeight g2Upper3Pi (g2Upper3Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper3_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper3 i cap) (realPi g2Upper3) (realGamma g2Upper3 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper3Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper3_vertices_agree g2Upper3_pi_agrees g2Upper3_gamma_agrees g2Upper3_pi
    (fun i cap => (g2Upper3_weights i cap).1) (fun i cap => (g2Upper3_weights i cap).2)
    (fun i _ hx => g2Upper3_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
