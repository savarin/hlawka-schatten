/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper16Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper16Base : Fin 3 → Row := ![![10321/12000, 169/1500, 109/4000], ![10289/12000, 173/1500, 109/4000], ![5059/6000, 379/3000, 61/2000]]
def g2Upper16Pi : Profile := ![42959051/1073741824, 248925293/1073741824, 247543329/1073741824, 534314151/1073741824]
def g2Upper16Slope : Row := ![250463423/536870912, -203252861/1073741824, -302787509/1073741824]

def g2Upper16Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper16Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![396555/1048576, 106765/262144, 43127/131072]
private def gammaBound : Fin 3 → ℝ := ![653457/65536, 653457/65536, 9340689/1048576]

theorem g2Upper16_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper16 v cap = g2Upper16Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper16, Tangent.vertex, g2Upper16Vertex, g2Upper16Base, facetCap]

theorem g2Upper16_pi_agrees : realPi g2Upper16 = g2Upper16Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper16, g2Upper16Pi, weightDen]

theorem g2Upper16_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper16 v cap = prismWeight g2Upper16Pi g2Upper16Slope (g2Upper16Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper16, weightDen, g2Upper16Pi,
      g2Upper16Slope, g2Upper16Vertex, g2Upper16Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper16_pi : IsSimplex g2Upper16Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper16Pi]
  · norm_num [g2Upper16Pi, Fin.sum_univ_succ]

theorem g2Upper16_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper16Pi g2Upper16Slope (g2Upper16Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper16Pi g2Upper16Slope (g2Upper16Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper16Vertex, g2Upper16Pi, g2Upper16Slope, g2Upper16Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper16Vertex, g2Upper16Pi, g2Upper16Slope, g2Upper16Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper16Base v) g2Upper16Pi (facetWeight g2Upper16Pi (g2Upper16Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper16_pi)
  · fin_cases v <;> norm_num [g2Upper16Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper16Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper16Base, g2Upper16Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper16Base, g2Upper16Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper16Base, g2Upper16Pi, lam, Fin.castSucc]

theorem g2Upper16_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper16Base v)) g2Upper16Pi (facetWeight g2Upper16Pi (g2Upper16Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper16_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper16 i cap) (realPi g2Upper16) (realGamma g2Upper16 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper16Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper16_vertices_agree g2Upper16_pi_agrees g2Upper16_gamma_agrees g2Upper16_pi
    (fun i cap => (g2Upper16_weights i cap).1) (fun i cap => (g2Upper16_weights i cap).2)
    (fun i _ hx => g2Upper16_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
