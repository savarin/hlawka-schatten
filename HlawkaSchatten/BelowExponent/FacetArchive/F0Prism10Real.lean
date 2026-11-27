/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism10Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F0Prism10Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f0Archived10Base : Fin 3 → Row := ![![1/3, 1/3, 1/3], ![17/30, 13/60, 13/60], ![61/120, 1/3, 19/120]]
private def pi : Profile := ![71833971/536870912, 96667711/536870912, 109485477/536870912, 258883753/536870912]
private def slope : Row := ![105607723/1073741824, -36427053/536870912, -70960433/1073741824]
private def lam : Fin 3 → ℝ := ![261549/1048576, 356855/1048576, 57009/131072]
private def gammaBound : Fin 3 → ℝ := ![585309/524288, 1597179/1048576, 1020623/524288]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f0Archived10Base v) pi (facetWeight pi (f0Archived10Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f0Archived10Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f0Archived10Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f0Archived10Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f0Archived10Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f0Archived10Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/4) x) :
    WeightedRow criticalQ (facetBase (f0Archived10Base v)) pi (facetWeight pi (f0Archived10Base v)) x := by
  apply facetCritical_cone_of_budget (U := 8/3) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · exact facetCritical_quarter.le
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f0Archived10_rows : FacetArchiveTriangle criticalQ f0Archived10Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f0Archived10) (slope := slope)
    _ _ _ _ _ _ f0Archived10_data_ok ![f0Archived10Chart0, f0Archived10Chart1, f0Archived10Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f0Archived10_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f0Archived10, Tangent.vertex, f0Archived10Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f0Archived10, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f0Archived10, weightDen,
        pi, slope, f0Archived10Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f0Archived10Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f0Archived10Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f0Archived10] using hx
  · intro j
    fin_cases j
    · exact f0Archived10Chart0_ok
    · exact f0Archived10Chart1_ok
    · exact f0Archived10Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
