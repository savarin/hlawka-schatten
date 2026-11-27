/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper25Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper25Base : Fin 3 → Row := ![![5059/6000, 719/6000, 37/1000], ![607/750, 211/1500, 1/20], ![5059/6000, 379/3000, 61/2000]]
def g2Upper25Pi : Profile := ![92651/2097152, 114990195/536870912, 32576425/134217728, 267856361/536870912]
def g2Upper25Slope : Row := ![473776355/1073741824, -6343431/33554432, -273102945/1073741824]

def g2Upper25Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper25Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![89345/262144, 78231/1048576, 331169/1048576]
private def gammaBound : Fin 3 → ℝ := ![7319785/1048576, 5416053/1048576, 8880221/1048576]

theorem g2Upper25_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper25 v cap = g2Upper25Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper25, Tangent.vertex, g2Upper25Vertex, g2Upper25Base, facetCap]

theorem g2Upper25_pi_agrees : realPi g2Upper25 = g2Upper25Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper25, g2Upper25Pi, weightDen]

theorem g2Upper25_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper25 v cap = prismWeight g2Upper25Pi g2Upper25Slope (g2Upper25Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper25, weightDen, g2Upper25Pi,
      g2Upper25Slope, g2Upper25Vertex, g2Upper25Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper25_pi : IsSimplex g2Upper25Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper25Pi]
  · norm_num [g2Upper25Pi, Fin.sum_univ_succ]

theorem g2Upper25_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper25Pi g2Upper25Slope (g2Upper25Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper25Pi g2Upper25Slope (g2Upper25Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper25Vertex, g2Upper25Pi, g2Upper25Slope, g2Upper25Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper25Vertex, g2Upper25Pi, g2Upper25Slope, g2Upper25Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper25Base v) g2Upper25Pi (facetWeight g2Upper25Pi (g2Upper25Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper25_pi)
  · fin_cases v <;> norm_num [g2Upper25Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper25Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper25Base, g2Upper25Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper25Base, g2Upper25Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper25Base, g2Upper25Pi, lam, Fin.castSucc]

theorem g2Upper25_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/32) x) :
    WeightedRow criticalQ (facetBase (g2Upper25Base v)) g2Upper25Pi (facetWeight g2Upper25Pi (g2Upper25Base v)) x := by
  apply facetCritical_cone_of_budget (U := 256/225) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/16) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper25_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/32) x) →
      WeightedRow criticalQ (realVertex g2Upper25 i cap) (realPi g2Upper25) (realGamma g2Upper25 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper25Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper25_vertices_agree g2Upper25_pi_agrees g2Upper25_gamma_agrees g2Upper25_pi
    (fun i cap => (g2Upper25_weights i cap).1) (fun i cap => (g2Upper25_weights i cap).2)
    (fun i _ hx => g2Upper25_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
