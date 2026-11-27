/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism7Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F0Prism7Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f0Archived7Base : Fin 3 → Row := ![![41/60, 19/120, 19/120], ![89/120, 31/240, 31/240], ![57/80, 3/16, 1/10]]
private def pi : Profile := ![42563099/536870912, 113851905/536870912, 59621639/268435456, 130606315/268435456]
private def slope : Row := ![170700583/536870912, -20944583/134217728, -101367905/536870912]
private def lam : Fin 3 → ℝ := ![219589/524288, 195391/524288, 58431/131072]
private def gammaBound : Fin 3 → ℝ := ![1967753/1048576, 2418455/1048576, 3026767/1048576]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f0Archived7Base v) pi (facetWeight pi (f0Archived7Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f0Archived7Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f0Archived7Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f0Archived7Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f0Archived7Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f0Archived7Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f0Archived7Base v)) pi (facetWeight pi (f0Archived7Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f0Archived7_rows : FacetArchiveTriangle criticalQ f0Archived7Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f0Archived7) (slope := slope)
    _ _ _ _ _ _ f0Archived7_data_ok ![f0Archived7Chart0, f0Archived7Chart1, f0Archived7Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f0Archived7_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f0Archived7, Tangent.vertex, f0Archived7Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f0Archived7, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f0Archived7, weightDen,
        pi, slope, f0Archived7Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f0Archived7Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f0Archived7Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f0Archived7] using hx
  · intro j
    fin_cases j
    · exact f0Archived7Chart0_ok
    · exact f0Archived7Chart1_ok
    · exact f0Archived7Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
