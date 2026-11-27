/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper30Data

/-! Exact cone checks and conditional real interpolation for one G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

def g2Upper30Base : Fin 3 → Row := ![![5059/6000, 719/6000, 37/1000], ![5059/6000, 641/6000, 1/20], ![607/750, 211/1500, 1/20]]
def g2Upper30Pi : Profile := ![48250143/1073741824, 229123961/1073741824, 262613977/1073741824, 533753743/1073741824]
def g2Upper30Slope : Row := ![468276337/1073741824, -102957069/536870912, -268596539/1073741824]

def g2Upper30Vertex (v : Fin 3) (cap : Bool) : Profile :=
  facetCap (g2Upper30Base v) (if cap then 1 / 500 else 0)

private def lam : Fin 3 → ℝ := ![165197/524288, 184521/524288, 172397/1048576]
private def gammaBound : Fin 3 → ℝ := ![914351/131072, 5411375/1048576, 5411375/1048576]

theorem g2Upper30_vertices_agree (v : Fin 3) (cap : Bool) :
    realVertex g2Upper30 v cap = g2Upper30Vertex v cap := by
  funext s
  fin_cases v <;> cases cap <;> fin_cases s <;>
    norm_num [realVertex, vertexAt, g2Upper30, Tangent.vertex, g2Upper30Vertex, g2Upper30Base, facetCap]

theorem g2Upper30_pi_agrees : realPi g2Upper30 = g2Upper30Pi := by
  funext s
  fin_cases s <;> norm_num [realPi, g2Upper30, g2Upper30Pi, weightDen]

theorem g2Upper30_gamma_agrees (v : Fin 3) (cap : Bool) :
    realGamma g2Upper30 v cap = prismWeight g2Upper30Pi g2Upper30Slope (g2Upper30Vertex v cap) := by
  funext j
  fin_cases v <;> cases cap <;> fin_cases j <;>
    norm_num [realGamma, realInput, vertexAt, inputNumerator, g2Upper30, weightDen, g2Upper30Pi,
      g2Upper30Slope, g2Upper30Vertex, g2Upper30Base, prismWeight, facetWeight, facetCap, Fin.castSucc]

theorem g2Upper30_pi : IsSimplex g2Upper30Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [g2Upper30Pi]
  · norm_num [g2Upper30Pi, Fin.sum_univ_succ]

theorem g2Upper30_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight g2Upper30Pi g2Upper30Slope (g2Upper30Vertex v cap) j) ∧
      (∑ j, prismWeight g2Upper30Pi g2Upper30Slope (g2Upper30Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, g2Upper30Vertex, g2Upper30Pi, g2Upper30Slope, g2Upper30Base,
        facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, g2Upper30Vertex, g2Upper30Pi, g2Upper30Slope, g2Upper30Base,
        facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (g2Upper30Base v) g2Upper30Pi (facetWeight g2Upper30Pi (g2Upper30Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := g2Upper30_pi)
  · fin_cases v <;> norm_num [g2Upper30Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [g2Upper30Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, g2Upper30Base, g2Upper30Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, g2Upper30Base, g2Upper30Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, g2Upper30Base, g2Upper30Pi, lam, Fin.castSucc]

theorem g2Upper30_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/16) x) :
    WeightedRow criticalQ (facetBase (g2Upper30Base v)) g2Upper30Pi (facetWeight g2Upper30Pi (g2Upper30Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64/49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem rowAt_g2Upper30_of_numeric_rows {w : Row} {d : ℝ}
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone (1/16) x) →
      WeightedRow criticalQ (realVertex g2Upper30 i cap) (realPi g2Upper30) (realGamma g2Upper30 i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * g2Upper30Base i j) d) :=
  rowAt_g2_prism_of_numeric_rows g2Upper30_vertices_agree g2Upper30_pi_agrees g2Upper30_gamma_agrees g2Upper30_pi
    (fun i cap => (g2Upper30_weights i cap).1) (fun i cap => (g2Upper30_weights i cap).2)
    (fun i _ hx => g2Upper30_cone i hx) hnumeric hw hsum hd₀ hd

end

end HlawkaSchatten.BelowExponent
