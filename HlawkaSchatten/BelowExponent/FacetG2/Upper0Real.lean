/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper0Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper0Base : Fin 3 → Row := ![![1551/2000, 181/1000, 87/2000], ![929/1200, 547/3000, 87/2000], ![89/120, 5/24, 1/20]]
def g2Upper0Pi : Profile := ![17286935/268435456, 223550485/1073741824, 123941695/536870912, 533160209/1073741824]
def g2Upper0Slope : Row := ![401452455/1073741824, -127663821/1073741824, -281210041/1073741824]

def g2Upper0Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper0Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![355417/1048576, 365541/1048576, 164165/524288]
private def gammaBound : Fin 3 → ℝ := ![205117/32768, 205117/32768, 5709515/1048576]

theorem g2Upper0_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper0 v cap = g2Upper0Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper0, Tangent.vertex, g2Upper0Vertex, g2Upper0Base, facetCap]

theorem g2Upper0_pi_agrees : realPi g2Upper0 = g2Upper0Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper0, g2Upper0Pi, weightDen]

theorem g2Upper0_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper0 v cap = prismWeight g2Upper0Pi g2Upper0Slope (g2Upper0Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper0, weightDen, g2Upper0Pi,
      g2Upper0Slope, g2Upper0Vertex, g2Upper0Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper0_pi : IsSimplex g2Upper0Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper0Pi]
  · norm_num [g2Upper0Pi, Fin.sum_univ_succ]

theorem g2Upper0_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper0Pi g2Upper0Slope (g2Upper0Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper0Pi g2Upper0Slope (g2Upper0Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper0Vertex, g2Upper0Pi, g2Upper0Slope, g2Upper0Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper0Vertex, g2Upper0Pi, g2Upper0Slope, g2Upper0Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper0Base v) g2Upper0Pi (facetWeight g2Upper0Pi (g2Upper0Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper0_pi)
  · fin_cases v <;> norm_num [g2Upper0Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper0Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper0Base, g2Upper0Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper0Base, g2Upper0Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper0Base, g2Upper0Pi, lam, Fin.castSucc]

theorem g2Upper0_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper0Base v)) g2Upper0Pi (facetWeight g2Upper0Pi (g2Upper0Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper0_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper0 i cap) (realPi g2Upper0) (realGamma g2Upper0 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper0Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper0_vertices_agree g2Upper0_pi_agrees g2Upper0_gamma_agrees g2Upper0_pi
    (fun i cap => (g2Upper0_weights i cap).1) (fun i cap => (g2Upper0_weights i cap).2)
    (fun i _ hx => g2Upper0_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
