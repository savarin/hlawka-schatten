/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper28Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper28Base : Fin 3 → Row := ![![4169/4800, 127/1200, 41/1600], ![10321/12000, 1313/12000, 61/2000], ![10321/12000, 169/1500, 109/4000]]
def g2Upper28Pi : Profile := ![40330985/1073741824, 251072453/1073741824, 247929321/1073741824, 534409065/1073741824]
def g2Upper28Slope : Row := ![493297827/1073741824, -194293943/1073741824, -151963789/536870912]

def g2Upper28Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper28Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![398723/1048576, 241005/524288, 241005/524288]
private def gammaBound : Fin 3 → ℝ := ![5550253/524288, 2331369/262144, 10438263/1048576]

theorem g2Upper28_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper28 v cap = g2Upper28Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper28, Tangent.vertex, g2Upper28Vertex, g2Upper28Base, facetCap]

theorem g2Upper28_pi_agrees : realPi g2Upper28 = g2Upper28Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper28, g2Upper28Pi, weightDen]

theorem g2Upper28_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper28 v cap = prismWeight g2Upper28Pi g2Upper28Slope (g2Upper28Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper28, weightDen, g2Upper28Pi,
      g2Upper28Slope, g2Upper28Vertex, g2Upper28Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper28_pi : IsSimplex g2Upper28Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper28Pi]
  · norm_num [g2Upper28Pi, Fin.sum_univ_succ]

theorem g2Upper28_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper28Pi g2Upper28Slope (g2Upper28Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper28Pi g2Upper28Slope (g2Upper28Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper28Vertex, g2Upper28Pi, g2Upper28Slope, g2Upper28Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper28Vertex, g2Upper28Pi, g2Upper28Slope, g2Upper28Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper28Base v) g2Upper28Pi (facetWeight g2Upper28Pi (g2Upper28Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper28_pi)
  · fin_cases v <;> norm_num [g2Upper28Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper28Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper28Base, g2Upper28Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper28Base, g2Upper28Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper28Base, g2Upper28Pi, lam, Fin.castSucc]

theorem g2Upper28_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper28Base v)) g2Upper28Pi (facetWeight g2Upper28Pi (g2Upper28Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper28_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper28 i cap) (realPi g2Upper28) (realGamma g2Upper28 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper28Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper28_vertices_agree g2Upper28_pi_agrees g2Upper28_gamma_agrees g2Upper28_pi
    (fun i cap => (g2Upper28_weights i cap).1) (fun i cap => (g2Upper28_weights i cap).2)
    (fun i _ hx => g2Upper28_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
