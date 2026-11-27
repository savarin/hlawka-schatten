/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F2Prism37Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F2Prism37Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f2Archived37Base : Fin 3 → Row := ![![967/1280, 233/1280, 1/16], ![483/640, 121/640, 9/160], ![491/640, 117/640, 1/20]]
private def pi : Profile := ![17220219/268435456, 231956827/1073741824, 61291945/268435456, 527736341/1073741824]
private def slope : Row := ![391444667/1073741824, -16987663/134217728, -8556641/33554432]
private def lam : Fin 3 → ℝ := ![488015/1048576, 243511/524288, 117679/262144]
private def gammaBound : Fin 3 → ℝ := ![4682749/1048576, 1301259/262144, 732237/131072]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f2Archived37Base v) pi (facetWeight pi (f2Archived37Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f2Archived37Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f2Archived37Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived37Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived37Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f2Archived37Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f2Archived37Base v)) pi (facetWeight pi (f2Archived37Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f2Archived37_rows : FacetArchiveTriangle criticalQ f2Archived37Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f2Archived37) (slope := slope)
    _ _ _ _ _ _ f2Archived37_data_ok ![f2Archived37Chart0, f2Archived37Chart1, f2Archived37Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f2Archived37_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f2Archived37, Tangent.vertex, f2Archived37Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f2Archived37, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f2Archived37, weightDen,
        pi, slope, f2Archived37Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f2Archived37Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f2Archived37Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f2Archived37] using hx
  · intro j
    fin_cases j
    · exact f2Archived37Chart0_ok
    · exact f2Archived37Chart1_ok
    · exact f2Archived37Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
