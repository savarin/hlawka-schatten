/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper33Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper33Base : Fin 3 → Row := ![![877/1000, 99/1000, 3/125], ![10321/12000, 247/2400, 37/1000], ![10321/12000, 1313/12000, 61/2000]]
def g2Upper33Pi : Profile := ![37487011/1073741824, 247479359/1073741824, 254230681/1073741824, 534544773/1073741824]
def g2Upper33Slope : Row := ![126036951/268435456, -216061053/1073741824, -292739031/1073741824]

def g2Upper33Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper33Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![188439/524288, 186493/524288, 36317/131072]
private def gammaBound : Fin 3 → ℝ := ![11590769/1048576, 1879185/262144, 9119637/1048576]

theorem g2Upper33_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper33 v cap = g2Upper33Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper33, Tangent.vertex, g2Upper33Vertex, g2Upper33Base, facetCap]

theorem g2Upper33_pi_agrees : realPi g2Upper33 = g2Upper33Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper33, g2Upper33Pi, weightDen]

theorem g2Upper33_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper33 v cap = prismWeight g2Upper33Pi g2Upper33Slope (g2Upper33Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper33, weightDen, g2Upper33Pi,
      g2Upper33Slope, g2Upper33Vertex, g2Upper33Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper33_pi : IsSimplex g2Upper33Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper33Pi]
  · norm_num [g2Upper33Pi, Fin.sum_univ_succ]

theorem g2Upper33_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper33Pi g2Upper33Slope (g2Upper33Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper33Pi g2Upper33Slope (g2Upper33Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper33Vertex, g2Upper33Pi, g2Upper33Slope, g2Upper33Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper33Vertex, g2Upper33Pi, g2Upper33Slope, g2Upper33Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper33Base v) g2Upper33Pi (facetWeight g2Upper33Pi (g2Upper33Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper33_pi)
  · fin_cases v <;> norm_num [g2Upper33Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper33Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper33Base, g2Upper33Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper33Base, g2Upper33Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper33Base, g2Upper33Pi, lam, Fin.castSucc]

theorem g2Upper33_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper33Base v)) g2Upper33Pi (facetWeight g2Upper33Pi (g2Upper33Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper33_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper33 i cap) (realPi g2Upper33) (realGamma g2Upper33 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper33Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper33_vertices_agree g2Upper33_pi_agrees g2Upper33_gamma_agrees g2Upper33_pi
    (fun i cap => (g2Upper33_weights i cap).1) (fun i cap => (g2Upper33_weights i cap).2)
    (fun i _ hx => g2Upper33_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
