/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism18Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F1Prism18Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f1Archived18Base : Fin 3 → Row := ![![5/8, 11/40, 1/10], ![43/80, 29/80, 1/10], ![87/160, 59/160, 7/80]]
private def pi : Profile := ![60257045/536870912, 185167965/1073741824, 244991609/1073741824, 2043235/4194304]
private def slope : Row := ![57295923/268435456, -16062493/1073741824, -240726707/1073741824]
private def lam : Fin 3 → ℝ := ![71131/262144, 325347/1048576, 19781/65536]
private def gammaBound : Fin 3 → ℝ := ![1479109/524288, 1479109/524288, 105771/32768]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f1Archived18Base v) pi (facetWeight pi (f1Archived18Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f1Archived18Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f1Archived18Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f1Archived18Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f1Archived18Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f1Archived18Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f1Archived18Base v)) pi (facetWeight pi (f1Archived18Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f1Archived18_rows : FacetArchiveTriangle criticalQ f1Archived18Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f1Archived18) (slope := slope)
    _ _ _ _ _ _ f1Archived18_data_ok ![f1Archived18Chart0, f1Archived18Chart1, f1Archived18Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f1Archived18_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f1Archived18, Tangent.vertex, f1Archived18Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f1Archived18, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f1Archived18, weightDen,
        pi, slope, f1Archived18Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f1Archived18Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f1Archived18Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f1Archived18] using hx
  · intro j
    fin_cases j
    · exact f1Archived18Chart0_ok
    · exact f1Archived18Chart1_ok
    · exact f1Archived18Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
