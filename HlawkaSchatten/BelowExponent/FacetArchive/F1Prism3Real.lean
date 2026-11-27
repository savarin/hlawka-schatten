/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism3Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F1Prism3Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f1Archived3Base : Fin 3 → Row := ![![317/640, 289/640, 17/320], ![617/1280, 589/1280, 37/640], ![621/1280, 593/1280, 33/640]]
private def pi : Profile := ![18812883/134217728, 157715261/1073741824, 239113133/1073741824, 263205183/536870912]
private def slope : Row := ![73350675/536870912, 115360233/1073741824, -141491341/536870912]
private def lam : Fin 3 → ℝ := ![113409/262144, 470513/1048576, 467433/1048576]
private def gammaBound : Fin 3 → ℝ := ![1411337/262144, 648245/131072, 2908519/524288]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f1Archived3Base v) pi (facetWeight pi (f1Archived3Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f1Archived3Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f1Archived3Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f1Archived3Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f1Archived3Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f1Archived3Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f1Archived3Base v)) pi (facetWeight pi (f1Archived3Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f1Archived3_rows : FacetArchiveTriangle criticalQ f1Archived3Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f1Archived3) (slope := slope)
    _ _ _ _ _ _ f1Archived3_data_ok ![f1Archived3Chart0, f1Archived3Chart1, f1Archived3Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f1Archived3_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f1Archived3, Tangent.vertex, f1Archived3Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f1Archived3, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f1Archived3, weightDen,
        pi, slope, f1Archived3Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f1Archived3Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f1Archived3Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f1Archived3] using hx
  · intro j
    fin_cases j
    · exact f1Archived3Chart0_ok
    · exact f1Archived3Chart1_ok
    · exact f1Archived3Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
