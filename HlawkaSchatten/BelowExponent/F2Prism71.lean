/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetPrism

/-! The three base cone proofs and the six weight budgets for F2 prism 71.
The exact vertices, weights and radius come from the one-based preorder
leaf in the archived facet_s2.txt certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def f2Prism71Base : Fin 3 → Row :=
  ![![317/640,289/640,17/320], ![19/40,19/40,1/20], ![125/256,591/1280,1/20]]

def f2Prism71Pi : Profile :=
  ![158118463/1073741824, 163628656/1073741824, 218672122/1073741824, 533322583/1073741824]

def f2Prism71Slope : Row :=
  ![234749993/1073741824, 86177653/1073741824, -328024308/1073741824]

def f2Prism71Vertex (v : Fin 3) (cap : Bool) : Profile :=
  if cap then facetCap (f2Prism71Base v) (1 / 400) else facetBase (f2Prism71Base v)

private def lam : Fin 3 → ℝ := ![82919/200000,25893/62500,103533/250000]

private def gammaBound : Fin 3 → ℝ := ![1408467/250000,2993199/500000,2993199/500000]

theorem f2Prism71_pi : IsSimplex f2Prism71Pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [f2Prism71Pi]
  · norm_num [f2Prism71Pi, Fin.sum_univ_succ]

theorem f2Prism71_vertex_weights (v : Fin 3) (cap : Bool) :
    (∀ j, 0 ≤ prismWeight f2Prism71Pi f2Prism71Slope (f2Prism71Vertex v cap) j) ∧
      (∑ j, prismWeight f2Prism71Pi f2Prism71Slope (f2Prism71Vertex v cap) j) ≤ 1 := by
  constructor
  · intro j
    fin_cases v <;> cases cap <;> fin_cases j <;>
      norm_num [prismWeight, facetWeight, f2Prism71Vertex, f2Prism71Pi, f2Prism71Slope,
        f2Prism71Base, facetBase, facetCap, Fin.castSucc]
  · fin_cases v <;> cases cap <;>
      norm_num [prismWeight, facetWeight, f2Prism71Vertex, f2Prism71Pi, f2Prism71Slope,
        f2Prism71Base, facetBase, facetCap, Fin.castSucc, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f2Prism71Base v) f2Prism71Pi
      (facetWeight f2Prism71Pi (f2Prism71Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := f2Prism71_pi)
  · fin_cases v <;> norm_num [f2Prism71Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f2Prism71Base]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, f2Prism71Base, f2Prism71Pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;>
      norm_num [facetWeight, f2Prism71Base, f2Prism71Pi, gammaBound, Fin.castSucc]
  all_goals
    fin_cases v <;> norm_num [facetPairWeight, f2Prism71Base, f2Prism71Pi, lam, Fin.castSucc]

theorem f2Prism71_cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1 / 16) x) :
    WeightedRow criticalQ (facetBase (f2Prism71Base v)) f2Prism71Pi
      (facetWeight f2Prism71Pi (f2Prism71Base v)) x := by
  apply facetCritical_cone_of_budget (U := 64 / 49) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1 / 8) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

end

end HlawkaSchatten.BelowExponent
