/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper12Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper12Base : Fin 3 → Row := ![![5059/6000, 379/3000, 61/2000], ![1681/2000, 129/1000, 61/2000], ![661/800, 7/50, 27/800]]
def g2Upper12Pi : Profile := ![12067723/268435456, 245781177/1073741824, 61403935/268435456, 534074015/1073741824]
def g2Upper12Slope : Row := ![475625727/1073741824, -90345737/536870912, -300528049/1073741824]

def g2Upper12Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper12Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![198825/524288, 26591/65536, 466757/1048576]
private def gammaBound : Fin 3 → ℝ := ![9409627/1048576, 9409627/1048576, 8502989/1048576]

theorem g2Upper12_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper12 v cap = g2Upper12Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper12, Tangent.vertex, g2Upper12Vertex, g2Upper12Base, facetCap]

theorem g2Upper12_pi_agrees : realPi g2Upper12 = g2Upper12Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper12, g2Upper12Pi, weightDen]

theorem g2Upper12_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper12 v cap = prismWeight g2Upper12Pi g2Upper12Slope (g2Upper12Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper12, weightDen, g2Upper12Pi,
      g2Upper12Slope, g2Upper12Vertex, g2Upper12Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper12_pi : IsSimplex g2Upper12Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper12Pi]
  · norm_num [g2Upper12Pi, Fin.sum_univ_succ]

theorem g2Upper12_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper12Pi g2Upper12Slope (g2Upper12Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper12Pi g2Upper12Slope (g2Upper12Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper12Vertex, g2Upper12Pi, g2Upper12Slope, g2Upper12Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper12Vertex, g2Upper12Pi, g2Upper12Slope, g2Upper12Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper12Base v) g2Upper12Pi (facetWeight g2Upper12Pi (g2Upper12Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper12_pi)
  · fin_cases v <;> norm_num [g2Upper12Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper12Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper12Base, g2Upper12Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper12Base, g2Upper12Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper12Base, g2Upper12Pi, lam, Fin.castSucc]

theorem g2Upper12_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper12Base v)) g2Upper12Pi (facetWeight g2Upper12Pi (g2Upper12Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper12_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper12 i cap) (realPi g2Upper12) (realGamma g2Upper12 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper12Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper12_vertices_agree g2Upper12_pi_agrees g2Upper12_gamma_agrees g2Upper12_pi
    (fun i cap => (g2Upper12_weights i cap).1) (fun i cap => (g2Upper12_weights i cap).2)
    (fun i _ hx => g2Upper12_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
