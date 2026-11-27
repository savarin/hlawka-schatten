/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper24Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper24Base : Fin 3 → Row := ![![5059/6000, 379/3000, 61/2000], ![607/750, 211/1500, 1/20], ![661/800, 7/50, 27/800]]
def g2Upper24Pi : Profile := ![2964831/67108864, 114990075/536870912, 32576479/134217728, 267856273/536870912]
def g2Upper24Slope : Row := ![230170439/536870912, -189192563/1073741824, -136732525/536870912]

def g2Upper24Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper24Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![10349/32768, 78231/1048576, 495489/1048576]
private def gammaBound : Fin 3 → ℝ := ![8880213/1048576, 338503/65536, 8024863/1048576]

theorem g2Upper24_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper24 v cap = g2Upper24Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper24, Tangent.vertex, g2Upper24Vertex, g2Upper24Base, facetCap]

theorem g2Upper24_pi_agrees : realPi g2Upper24 = g2Upper24Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper24, g2Upper24Pi, weightDen]

theorem g2Upper24_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper24 v cap = prismWeight g2Upper24Pi g2Upper24Slope (g2Upper24Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper24, weightDen, g2Upper24Pi,
      g2Upper24Slope, g2Upper24Vertex, g2Upper24Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper24_pi : IsSimplex g2Upper24Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper24Pi]
  · norm_num [g2Upper24Pi, Fin.sum_univ_succ]

theorem g2Upper24_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper24Pi g2Upper24Slope (g2Upper24Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper24Pi g2Upper24Slope (g2Upper24Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper24Vertex, g2Upper24Pi, g2Upper24Slope, g2Upper24Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper24Vertex, g2Upper24Pi, g2Upper24Slope, g2Upper24Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper24Base v) g2Upper24Pi (facetWeight g2Upper24Pi (g2Upper24Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper24_pi)
  · fin_cases v <;> norm_num [g2Upper24Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper24Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper24Base, g2Upper24Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper24Base, g2Upper24Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper24Base, g2Upper24Pi, lam, Fin.castSucc]

theorem g2Upper24_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/32) x) :
    WeightedRow criticalQ (facetBase (g2Upper24Base v)) g2Upper24Pi (facetWeight g2Upper24Pi (g2Upper24Base v)) x := by
  apply facetCritical_cone_of_budget (U := 256/225) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/16) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper24_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/32) x) →
      WeightedRow criticalQ (realVertex g2Upper24 i cap) (realPi g2Upper24) (realGamma g2Upper24 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper24Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper24_vertices_agree g2Upper24_pi_agrees g2Upper24_gamma_agrees g2Upper24_pi
    (fun i cap => (g2Upper24_weights i cap).1) (fun i cap => (g2Upper24_weights i cap).2)
    (fun i _ hx => g2Upper24_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
