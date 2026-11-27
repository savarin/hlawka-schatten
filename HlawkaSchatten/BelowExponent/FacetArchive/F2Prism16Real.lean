/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F2Prism16Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F2Prism16Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f2Archived16Base : Fin 3 → Row := ![![263/320, 37/320, 1/16], ![1067/1280, 149/1280, 1/20], ![267/320, 7/64, 9/160]]
private def pi : Profile := ![49634993/1073741824, 248118511/1073741824, 247424551/1073741824, 528563769/1073741824]
private def slope : Row := ![456505735/1073741824, -200288875/1073741824, -136415575/536870912]
private def lam : Fin 3 → ℝ := ![493459/1048576, 466005/1048576, 461937/1048576]
private def gammaBound : Fin 3 → ℝ := ![2318087/524288, 2899637/524288, 5153107/1048576]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f2Archived16Base v) pi (facetWeight pi (f2Archived16Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f2Archived16Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f2Archived16Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived16Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived16Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f2Archived16Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f2Archived16Base v)) pi (facetWeight pi (f2Archived16Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f2Archived16_rows : FacetArchiveTriangle criticalQ f2Archived16Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f2Archived16) (slope := slope)
    _ _ _ _ _ _ f2Archived16_data_ok ![f2Archived16Chart0, f2Archived16Chart1, f2Archived16Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f2Archived16_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f2Archived16, Tangent.vertex, f2Archived16Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f2Archived16, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f2Archived16, weightDen,
        pi, slope, f2Archived16Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f2Archived16Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f2Archived16Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f2Archived16] using hx
  · intro j
    fin_cases j
    · exact f2Archived16Chart0_ok
    · exact f2Archived16Chart1_ok
    · exact f2Archived16Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
