/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper31Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper31Base : Fin 3 → Row := ![![10321/12000, 247/2400, 37/1000], ![5059/6000, 641/6000, 1/20], ![5059/6000, 719/6000, 37/1000]]
def g2Upper31Pi : Profile := ![44784353/1073741824, 8627353/33554432, 218937335/1073741824, 66743105/134217728]
def g2Upper31Slope : Row := ![30309317/67108864, -167586217/1073741824, -40401875/134217728]

def g2Upper31Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper31Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![199765/524288, 438127/1048576, 294645/1048576]
private def gammaBound : Fin 3 → ℝ := ![8462921/1048576, 1565269/262144, 8462921/1048576]

theorem g2Upper31_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper31 v cap = g2Upper31Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper31, Tangent.vertex, g2Upper31Vertex, g2Upper31Base, facetCap]

theorem g2Upper31_pi_agrees : realPi g2Upper31 = g2Upper31Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper31, g2Upper31Pi, weightDen]

theorem g2Upper31_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper31 v cap = prismWeight g2Upper31Pi g2Upper31Slope (g2Upper31Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper31, weightDen, g2Upper31Pi,
      g2Upper31Slope, g2Upper31Vertex, g2Upper31Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper31_pi : IsSimplex g2Upper31Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper31Pi]
  · norm_num [g2Upper31Pi, Fin.sum_univ_succ]

theorem g2Upper31_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper31Pi g2Upper31Slope (g2Upper31Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper31Pi g2Upper31Slope (g2Upper31Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper31Vertex, g2Upper31Pi, g2Upper31Slope, g2Upper31Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper31Vertex, g2Upper31Pi, g2Upper31Slope, g2Upper31Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper31Base v) g2Upper31Pi (facetWeight g2Upper31Pi (g2Upper31Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper31_pi)
  · fin_cases v <;> norm_num [g2Upper31Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper31Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper31Base, g2Upper31Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper31Base, g2Upper31Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper31Base, g2Upper31Pi, lam, Fin.castSucc]

theorem g2Upper31_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper31Base v)) g2Upper31Pi (facetWeight g2Upper31Pi (g2Upper31Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper31_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper31 i cap) (realPi g2Upper31) (realGamma g2Upper31 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper31Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper31_vertices_agree g2Upper31_pi_agrees g2Upper31_gamma_agrees g2Upper31_pi
    (fun i cap => (g2Upper31_weights i cap).1) (fun i cap => (g2Upper31_weights i cap).2)
    (fun i _ hx => g2Upper31_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
