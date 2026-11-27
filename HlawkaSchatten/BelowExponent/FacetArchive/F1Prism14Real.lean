/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism14Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F1Prism14Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f1Archived14Base : Fin 3 → Row := ![![51/80, 23/80, 3/40], ![189/320, 21/64, 13/160], ![191/320, 107/320, 11/160]]
private def pi : Profile := ![115568205/1073741824, 200675363/1073741824, 58227025/268435456, 131147539/268435456]
private def slope : Row := ![259798419/1073741824, -5576121/536870912, -136603847/536870912]
private def lam : Fin 3 → ℝ := ![22837/65536, 443707/1048576, 448173/1048576]
private def gammaBound : Fin 3 → ℝ := ![4093769/1048576, 3777019/1048576, 4468111/1048576]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f1Archived14Base v) pi (facetWeight pi (f1Archived14Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f1Archived14Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f1Archived14Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f1Archived14Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f1Archived14Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f1Archived14Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f1Archived14Base v)) pi (facetWeight pi (f1Archived14Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f1Archived14_rows : FacetArchiveTriangle criticalQ f1Archived14Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f1Archived14) (slope := slope)
    _ _ _ _ _ _ f1Archived14_data_ok ![f1Archived14Chart0, f1Archived14Chart1, f1Archived14Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f1Archived14_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f1Archived14, Tangent.vertex, f1Archived14Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f1Archived14, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f1Archived14, weightDen,
        pi, slope, f1Archived14Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f1Archived14Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f1Archived14Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f1Archived14] using hx
  · intro j
    fin_cases j
    · exact f1Archived14Chart0_ok
    · exact f1Archived14Chart1_ok
    · exact f1Archived14Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
