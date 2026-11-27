/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper22Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper22Base : Fin 3 → Row := ![![607/750, 461/3000, 37/1000], ![607/750, 211/1500, 1/20], ![1551/2000, 349/2000, 1/20]]
def g2Upper22Pi : Profile := ![7333003/134217728, 117117073/536870912, 247240021/1073741824, 533603633/1073741824]
def g2Upper22Slope : Row := ![222141951/536870912, -41202251/268435456, -286009457/1073741824]

def g2Upper22Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper22Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![187857/524288, 49951/131072, 182047/1048576]
private def gammaBound : Fin 3 → ℝ := ![7724251/1048576, 2857143/524288, 2857143/524288]

theorem g2Upper22_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper22 v cap = g2Upper22Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper22, Tangent.vertex, g2Upper22Vertex, g2Upper22Base, facetCap]

theorem g2Upper22_pi_agrees : realPi g2Upper22 = g2Upper22Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper22, g2Upper22Pi, weightDen]

theorem g2Upper22_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper22 v cap = prismWeight g2Upper22Pi g2Upper22Slope (g2Upper22Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper22, weightDen, g2Upper22Pi,
      g2Upper22Slope, g2Upper22Vertex, g2Upper22Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper22_pi : IsSimplex g2Upper22Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper22Pi]
  · norm_num [g2Upper22Pi, Fin.sum_univ_succ]

theorem g2Upper22_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper22Pi g2Upper22Slope (g2Upper22Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper22Pi g2Upper22Slope (g2Upper22Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper22Vertex, g2Upper22Pi, g2Upper22Slope, g2Upper22Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper22Vertex, g2Upper22Pi, g2Upper22Slope, g2Upper22Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper22Base v) g2Upper22Pi (facetWeight g2Upper22Pi (g2Upper22Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper22_pi)
  · fin_cases v <;> norm_num [g2Upper22Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper22Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper22Base, g2Upper22Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper22Base, g2Upper22Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper22Base, g2Upper22Pi, lam, Fin.castSucc]

theorem g2Upper22_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper22Base v)) g2Upper22Pi (facetWeight g2Upper22Pi (g2Upper22Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper22_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper22 i cap) (realPi g2Upper22) (realGamma g2Upper22 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper22Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper22_vertices_agree g2Upper22_pi_agrees g2Upper22_gamma_agrees g2Upper22_pi
    (fun i cap => (g2Upper22_weights i cap).1) (fun i cap => (g2Upper22_weights i cap).2)
    (fun i _ hx => g2Upper22_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
