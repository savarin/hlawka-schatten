/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper9Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper9Base : Fin 3 → Row := ![![607/750, 461/3000, 37/1000], ![9899/12000, 53/375, 27/800], ![1007/1200, 391/3000, 61/2000]]
def g2Upper9Pi : Profile := ![47693979/1073741824, 54036109/268435456, 68921567/268435456, 534217141/1073741824]
def g2Upper9Slope : Row := ![230888123/536870912, -49576773/268435456, -33597087/134217728]

def g2Upper9Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper9Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![221685/1048576, 413707/1048576, 68881/262144]
private def gammaBound : Fin 3 → ℝ := ![3479229/524288, 7629031/1048576, 8442513/1048576]

theorem g2Upper9_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper9 v cap = g2Upper9Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper9, Tangent.vertex, g2Upper9Vertex, g2Upper9Base, facetCap]

theorem g2Upper9_pi_agrees : realPi g2Upper9 = g2Upper9Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper9, g2Upper9Pi, weightDen]

theorem g2Upper9_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper9 v cap = prismWeight g2Upper9Pi g2Upper9Slope (g2Upper9Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper9, weightDen, g2Upper9Pi,
      g2Upper9Slope, g2Upper9Vertex, g2Upper9Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper9_pi : IsSimplex g2Upper9Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper9Pi]
  · norm_num [g2Upper9Pi, Fin.sum_univ_succ]

theorem g2Upper9_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper9Pi g2Upper9Slope (g2Upper9Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper9Pi g2Upper9Slope (g2Upper9Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper9Vertex, g2Upper9Pi, g2Upper9Slope, g2Upper9Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper9Vertex, g2Upper9Pi, g2Upper9Slope, g2Upper9Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper9Base v) g2Upper9Pi (facetWeight g2Upper9Pi (g2Upper9Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper9_pi)
  · fin_cases v <;> norm_num [g2Upper9Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper9Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper9Base, g2Upper9Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper9Base, g2Upper9Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper9Base, g2Upper9Pi, lam, Fin.castSucc]

theorem g2Upper9_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper9Base v)) g2Upper9Pi (facetWeight g2Upper9Pi (g2Upper9Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper9_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper9 i cap) (realPi g2Upper9) (realGamma g2Upper9 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper9Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper9_vertices_agree g2Upper9_pi_agrees g2Upper9_gamma_agrees g2Upper9_pi
    (fun i cap => (g2Upper9_weights i cap).1) (fun i cap => (g2Upper9_weights i cap).2)
    (fun i _ hx => g2Upper9_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
