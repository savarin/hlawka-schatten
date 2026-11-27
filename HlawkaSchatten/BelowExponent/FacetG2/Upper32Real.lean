/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper32Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper32Base : Fin 3 → Row := ![![10321/12000, 1313/12000, 61/2000], ![10321/12000, 247/2400, 37/1000], ![5059/6000, 719/6000, 37/1000]]
def g2Upper32Pi : Profile := ![44173389/1073741824, 271268519/1073741824, 56052947/268435456, 8345127/16777216]
def g2Upper32Slope : Row := ![487935215/1073741824, -21192749/134217728, -161979397/536870912]

def g2Upper32Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper32Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![208639/524288, 206469/524288, 66267/262144]
private def gammaBound : Fin 3 → ℝ := ![2523631/262144, 8320207/1048576, 8320207/1048576]

theorem g2Upper32_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper32 v cap = g2Upper32Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper32, Tangent.vertex, g2Upper32Vertex, g2Upper32Base, facetCap]

theorem g2Upper32_pi_agrees : realPi g2Upper32 = g2Upper32Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper32, g2Upper32Pi, weightDen]

theorem g2Upper32_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper32 v cap = prismWeight g2Upper32Pi g2Upper32Slope (g2Upper32Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper32, weightDen, g2Upper32Pi,
      g2Upper32Slope, g2Upper32Vertex, g2Upper32Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper32_pi : IsSimplex g2Upper32Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper32Pi]
  · norm_num [g2Upper32Pi, Fin.sum_univ_succ]

theorem g2Upper32_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper32Pi g2Upper32Slope (g2Upper32Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper32Pi g2Upper32Slope (g2Upper32Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper32Vertex, g2Upper32Pi, g2Upper32Slope, g2Upper32Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper32Vertex, g2Upper32Pi, g2Upper32Slope, g2Upper32Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper32Base v) g2Upper32Pi (facetWeight g2Upper32Pi (g2Upper32Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper32_pi)
  · fin_cases v <;> norm_num [g2Upper32Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper32Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper32Base, g2Upper32Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper32Base, g2Upper32Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper32Base, g2Upper32Pi, lam, Fin.castSucc]

theorem g2Upper32_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper32Base v)) g2Upper32Pi (facetWeight g2Upper32Pi (g2Upper32Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper32_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper32 i cap) (realPi g2Upper32) (realGamma g2Upper32 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper32Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper32_vertices_agree g2Upper32_pi_agrees g2Upper32_gamma_agrees g2Upper32_pi
    (fun i cap => (g2Upper32_weights i cap).1) (fun i cap => (g2Upper32_weights i cap).2)
    (fun i _ hx => g2Upper32_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
