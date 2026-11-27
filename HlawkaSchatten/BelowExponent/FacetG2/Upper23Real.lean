/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper23Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper23Base : Fin 3 → Row := ![![661/800, 7/50, 27/800], ![607/750, 211/1500, 1/20], ![607/750, 461/3000, 37/1000]]
def g2Upper23Pi : Profile := ![13432827/268435456, 122250203/536870912, 241677853/1073741824, 533832257/1073741824]
def g2Upper23Slope : Row := ![228118127/536870912, -83430251/536870912, -295453063/1073741824]

def g2Upper23Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper23Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![406939/1048576, 242093/524288, 471/1024]
private def gammaBound : Fin 3 → ℝ := ![8623455/1048576, 727363/131072, 7865469/1048576]

theorem g2Upper23_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper23 v cap = g2Upper23Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper23, Tangent.vertex, g2Upper23Vertex, g2Upper23Base, facetCap]

theorem g2Upper23_pi_agrees : realPi g2Upper23 = g2Upper23Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper23, g2Upper23Pi, weightDen]

theorem g2Upper23_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper23 v cap = prismWeight g2Upper23Pi g2Upper23Slope (g2Upper23Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper23, weightDen, g2Upper23Pi,
      g2Upper23Slope, g2Upper23Vertex, g2Upper23Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper23_pi : IsSimplex g2Upper23Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper23Pi]
  · norm_num [g2Upper23Pi, Fin.sum_univ_succ]

theorem g2Upper23_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper23Pi g2Upper23Slope (g2Upper23Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper23Pi g2Upper23Slope (g2Upper23Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper23Vertex, g2Upper23Pi, g2Upper23Slope, g2Upper23Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper23Vertex, g2Upper23Pi, g2Upper23Slope, g2Upper23Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper23Base v) g2Upper23Pi (facetWeight g2Upper23Pi (g2Upper23Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper23_pi)
  · fin_cases v <;> norm_num [g2Upper23Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper23Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper23Base, g2Upper23Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper23Base, g2Upper23Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper23Base, g2Upper23Pi, lam, Fin.castSucc]

theorem g2Upper23_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper23Base v)) g2Upper23Pi (facetWeight g2Upper23Pi (g2Upper23Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper23_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper23 i cap) (realPi g2Upper23) (realGamma g2Upper23 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper23Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper23_vertices_agree g2Upper23_pi_agrees g2Upper23_gamma_agrees g2Upper23_pi
    (fun i cap => (g2Upper23_weights i cap).1) (fun i cap => (g2Upper23_weights i cap).2)
    (fun i _ hx => g2Upper23_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
