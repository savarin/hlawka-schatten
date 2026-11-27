/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F2Prism62Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F2Prism62Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f2Archived62Base : Fin 3 → Row := ![![51/80, 23/80, 3/40], ![39/64, 21/64, 1/16], ![203/320, 101/320, 1/20]]
private def pi : Profile := ![6720311/67108864, 195602079/1073741824, 243635847/1073741824, 263489461/536870912]
private def slope : Row := ![269254505/1073741824, -9840673/536870912, -134678571/536870912]
private def lam : Fin 3 → ℝ := ![423897/1048576, 387331/1048576, 237095/524288]
private def gammaBound : Fin 3 → ℝ := ![3927647/1048576, 294815/65536, 2950565/524288]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f2Archived62Base v) pi (facetWeight pi (f2Archived62Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f2Archived62Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f2Archived62Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived62Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived62Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f2Archived62Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f2Archived62Base v)) pi (facetWeight pi (f2Archived62Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f2Archived62_rows : FacetArchiveTriangle criticalQ f2Archived62Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f2Archived62) (slope := slope)
    _ _ _ _ _ _ f2Archived62_data_ok ![f2Archived62Chart0, f2Archived62Chart1, f2Archived62Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f2Archived62_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f2Archived62, Tangent.vertex, f2Archived62Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f2Archived62, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f2Archived62, weightDen,
        pi, slope, f2Archived62Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f2Archived62Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f2Archived62Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f2Archived62] using hx
  · intro j
    fin_cases j
    · exact f2Archived62Chart0_ok
    · exact f2Archived62Chart1_ok
    · exact f2Archived62Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
