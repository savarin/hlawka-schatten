/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetPrism

/-! The three base cone proofs and the six weight budgets for F0 prism 10.
The exact vertices, weights and radius come from the one-based preorder
leaf in the archived facet_big.txt certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def f0Prism10Base : Fin 3 → Row :=
  ![![1/3,1/3,1/3], ![17/30,13/60,13/60], ![61/120,1/3,19/120]]

def f0Prism10Pi : Profile :=
  ![143667942/1073741824, 193335422/1073741824, 218970954/1073741824, 517767506/1073741824]

def f0Prism10Slope : Row :=
  ![105607723/1073741824, -72854106/1073741824, -70960433/1073741824]

def f0Prism10Vertex (v : Fin 3) (cap : Bool) : Profile :=
  if cap then facetCap (f0Prism10Base v) (1 / 400) else facetBase (f0Prism10Base v)

private def lam : Fin 3 → ℝ := ![31179/125000,340323/1000000,6796/15625]

private def gammaBound : Fin 3 → ℝ := ![279097/250000,1523189/1000000,486671/250000]

theorem f0Prism10_pi : IsSimplex f0Prism10Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [f0Prism10Pi]
  · norm_num [f0Prism10Pi, Fin.sum_univ_succ]

theorem f0Prism10_vertex_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight f0Prism10Pi f0Prism10Slope (f0Prism10Vertex v cap) j) ∧
      (∑ j, prismWeight f0Prism10Pi f0Prism10Slope (f0Prism10Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, f0Prism10Vertex, f0Prism10Pi, f0Prism10Slope,
        f0Prism10Base, facetBase, facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, f0Prism10Vertex, f0Prism10Pi, f0Prism10Slope,
        f0Prism10Base, facetBase, facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f0Prism10Base v) f0Prism10Pi
      (facetWeight f0Prism10Pi (f0Prism10Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := f0Prism10_pi)
  · fin_cases v <;> norm_num [f0Prism10Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f0Prism10Base]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, f0Prism10Base, f0Prism10Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, f0Prism10Base, f0Prism10Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, f0Prism10Base, f0Prism10Pi, lam, Fin.castSucc]

theorem f0Prism10_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1 / 4) x) :
    WeightedRow criticalQ (facetBase (f0Prism10Base v)) f0Prism10Pi
      (facetWeight f0Prism10Pi (f0Prism10Base v)) x := by
  apply facetCritical_cone_of_budget (U := 8 / 3) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · exact facetCritical_quarter.le
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

end

end HlawkaSchatten.BelowExponent
