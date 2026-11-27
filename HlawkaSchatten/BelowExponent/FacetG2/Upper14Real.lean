/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper14Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper14Base : Fin 3 → Row := ![![10289/12000, 173/1500, 109/4000], ![523/600, 313/3000, 3/125], ![10273/12000, 7/60, 109/4000]]
def g2Upper14Pi : Profile := ![19526297/536870912, 123865123/536870912, 63106177/268435456, 133633569/268435456]
def g2Upper14Slope : Row := ![498994853/1073741824, -202573543/1073741824, -301094585/1073741824]

def g2Upper14Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper14Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![218877/524288, 383257/1048576, 163639/524288]
private def gammaBound : Fin 3 → ℝ := ![5136459/524288, 2916165/262144, 5136459/524288]

theorem g2Upper14_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper14 v cap = g2Upper14Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper14, Tangent.vertex, g2Upper14Vertex, g2Upper14Base, facetCap]

theorem g2Upper14_pi_agrees : realPi g2Upper14 = g2Upper14Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper14, g2Upper14Pi, weightDen]

theorem g2Upper14_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper14 v cap = prismWeight g2Upper14Pi g2Upper14Slope (g2Upper14Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper14, weightDen, g2Upper14Pi,
      g2Upper14Slope, g2Upper14Vertex, g2Upper14Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper14_pi : IsSimplex g2Upper14Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper14Pi]
  · norm_num [g2Upper14Pi, Fin.sum_univ_succ]

theorem g2Upper14_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper14Pi g2Upper14Slope (g2Upper14Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper14Pi g2Upper14Slope (g2Upper14Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper14Vertex, g2Upper14Pi, g2Upper14Slope, g2Upper14Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper14Vertex, g2Upper14Pi, g2Upper14Slope, g2Upper14Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper14Base v) g2Upper14Pi (facetWeight g2Upper14Pi (g2Upper14Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper14_pi)
  · fin_cases v <;> norm_num [g2Upper14Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper14Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper14Base, g2Upper14Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper14Base, g2Upper14Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper14Base, g2Upper14Pi, lam, Fin.castSucc]

theorem g2Upper14_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper14Base v)) g2Upper14Pi (facetWeight g2Upper14Pi (g2Upper14Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper14_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper14 i cap) (realPi g2Upper14) (realGamma g2Upper14 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper14Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper14_vertices_agree g2Upper14_pi_agrees g2Upper14_gamma_agrees g2Upper14_pi
    (fun i cap => (g2Upper14_weights i cap).1) (fun i cap => (g2Upper14_weights i cap).2)
    (fun i _ hx => g2Upper14_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
