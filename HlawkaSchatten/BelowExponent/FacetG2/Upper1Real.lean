/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper1Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper1Base : Fin 3 → Row := ![![1551/2000, 181/1000, 87/2000], ![121/150, 469/3000, 37/1000], ![929/1200, 547/3000, 87/2000]]
def g2Upper1Pi : Profile := ![29522359/536870912, 113933659/536870912, 253196263/1073741824, 533633525/1073741824]
def g2Upper1Slope : Row := ![431784263/1073741824, -157443413/1073741824, -140407813/536870912]

def g2Upper1Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper1Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![246235/1048576, 349219/1048576, 205001/1048576]
private def gammaBound : Fin 3 → ℝ := ![3217385/524288, 3783157/524288, 3217385/524288]

theorem g2Upper1_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper1 v cap = g2Upper1Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper1, Tangent.vertex, g2Upper1Vertex, g2Upper1Base, facetCap]

theorem g2Upper1_pi_agrees : realPi g2Upper1 = g2Upper1Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper1, g2Upper1Pi, weightDen]

theorem g2Upper1_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper1 v cap = prismWeight g2Upper1Pi g2Upper1Slope (g2Upper1Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper1, weightDen, g2Upper1Pi,
      g2Upper1Slope, g2Upper1Vertex, g2Upper1Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper1_pi : IsSimplex g2Upper1Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper1Pi]
  · norm_num [g2Upper1Pi, Fin.sum_univ_succ]

theorem g2Upper1_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper1Pi g2Upper1Slope (g2Upper1Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper1Pi g2Upper1Slope (g2Upper1Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper1Vertex, g2Upper1Pi, g2Upper1Slope, g2Upper1Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper1Vertex, g2Upper1Pi, g2Upper1Slope, g2Upper1Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper1Base v) g2Upper1Pi (facetWeight g2Upper1Pi (g2Upper1Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper1_pi)
  · fin_cases v <;> norm_num [g2Upper1Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper1Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper1Base, g2Upper1Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper1Base, g2Upper1Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper1Base, g2Upper1Pi, lam, Fin.castSucc]

theorem g2Upper1_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper1Base v)) g2Upper1Pi (facetWeight g2Upper1Pi (g2Upper1Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper1_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper1 i cap) (realPi g2Upper1) (realGamma g2Upper1 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper1Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper1_vertices_agree g2Upper1_pi_agrees g2Upper1_gamma_agrees g2Upper1_pi
    (fun i cap => (g2Upper1_weights i cap).1) (fun i cap => (g2Upper1_weights i cap).2)
    (fun i _ hx => g2Upper1_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
