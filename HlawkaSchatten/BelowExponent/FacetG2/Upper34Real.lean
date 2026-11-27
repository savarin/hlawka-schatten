/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper34Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper34Base : Fin 3 → Row := ![![10321/12000, 247/2400, 37/1000], ![10321/12000, 1079/12000, 1/20], ![5059/6000, 641/6000, 1/20]]
def g2Upper34Pi : Profile := ![5604093/134217728, 278258275/1073741824, 108462379/536870912, 533726047/1073741824]
def g2Upper34Slope : Row := ![247205155/536870912, -180830001/1073741824, -319870041/1073741824]

def g2Upper34Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper34Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![395771/1048576, 191339/524288, 217033/524288]
private def gammaBound : Fin 3 → ℝ := ![8521387/1048576, 3152115/524288, 3152115/524288]

theorem g2Upper34_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper34 v cap = g2Upper34Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper34, Tangent.vertex, g2Upper34Vertex, g2Upper34Base, facetCap]

theorem g2Upper34_pi_agrees : realPi g2Upper34 = g2Upper34Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper34, g2Upper34Pi, weightDen]

theorem g2Upper34_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper34 v cap = prismWeight g2Upper34Pi g2Upper34Slope (g2Upper34Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper34, weightDen, g2Upper34Pi,
      g2Upper34Slope, g2Upper34Vertex, g2Upper34Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper34_pi : IsSimplex g2Upper34Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper34Pi]
  · norm_num [g2Upper34Pi, Fin.sum_univ_succ]

theorem g2Upper34_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper34Pi g2Upper34Slope (g2Upper34Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper34Pi g2Upper34Slope (g2Upper34Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper34Vertex, g2Upper34Pi, g2Upper34Slope, g2Upper34Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper34Vertex, g2Upper34Pi, g2Upper34Slope, g2Upper34Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper34Base v) g2Upper34Pi (facetWeight g2Upper34Pi (g2Upper34Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper34_pi)
  · fin_cases v <;> norm_num [g2Upper34Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper34Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper34Base, g2Upper34Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper34Base, g2Upper34Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper34Base, g2Upper34Pi, lam, Fin.castSucc]

theorem g2Upper34_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper34Base v)) g2Upper34Pi (facetWeight g2Upper34Pi (g2Upper34Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper34_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper34 i cap) (realPi g2Upper34) (realGamma g2Upper34 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper34Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper34_vertices_agree g2Upper34_pi_agrees g2Upper34_gamma_agrees g2Upper34_pi
    (fun i cap => (g2Upper34_weights i cap).1) (fun i cap => (g2Upper34_weights i cap).2)
    (fun i _ hx => g2Upper34_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
