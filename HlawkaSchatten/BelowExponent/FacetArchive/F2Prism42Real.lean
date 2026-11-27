/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F2Prism42Data
public import HlawkaSchatten.BelowExponent.FacetArchive.Geometry
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
public import HlawkaSchatten.BelowExponent.FacetTangentPrism

/-! Archived facet prism certificate data: `F2Prism42Real`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def f2Archived42Base : Fin 3 → Row := ![![449/640, 31/128, 9/160], ![897/1280, 319/1280, 1/20], ![457/640, 151/640, 1/20]]
private def pi : Profile := ![84330579/1073741824, 217672375/1073741824, 243987511/1073741824, 527751359/1073741824]
private def slope : Row := ![169136399/536870912, -76552837/1073741824, -8748721/33554432]
private def lam : Fin 3 → ℝ := ![242209/524288, 472547/1048576, 472547/1048576]
private def gammaBound : Fin 3 → ℝ := ![326581/65536, 1470171/262144, 1470171/262144]

private theorem probabilities : IsSimplex pi := by
  constructor
  · intro s
    fin_cases s <;> norm_num [pi]
  · norm_num [pi, Fin.sum_univ_succ]

private theorem moments (v : Fin 3) :
    FacetConeMoments (f2Archived42Base v) pi (facetWeight pi (f2Archived42Base v)) (lam v) (gammaBound v) := by
  apply facetConeMoments_of_pairWeights (hπ := probabilities)
  · fin_cases v <;> norm_num [f2Archived42Base, Fin.sum_univ_succ]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [f2Archived42Base]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived42Base, pi, Fin.castSucc]
  · intro j
    fin_cases v <;> fin_cases j <;> norm_num [facetWeight, f2Archived42Base, pi, gammaBound, Fin.castSucc]
  all_goals fin_cases v <;> norm_num [facetPairWeight, f2Archived42Base, pi, lam, Fin.castSucc]

private theorem cone (v : Fin 3) {x : Row} (hx : FacetRatioCone (1/8) x) :
    WeightedRow criticalQ (facetBase (f2Archived42Base v)) pi (facetWeight pi (f2Archived42Base v)) x := by
  apply facetCritical_cone_of_budget (U := 16/9) (hm := moments v) (hx := hx)
  · norm_num
  · norm_num
  · convert facetCritical_inverse_square (R := 1/4) (by norm_num) (by norm_num) using 1
    <;> norm_num
  · fin_cases v <;> norm_num [lam]
  · fin_cases v <;> norm_num [gammaBound]
  · fin_cases v <;> norm_num [lam, gammaBound]

theorem f2Archived42_rows : FacetArchiveTriangle criticalQ f2Archived42Base := by
  apply facetArchiveTriangle_of_weights
  intro w d hw hsum hd₀ hd₁
  apply rowAt_facetPrism_of_tangents hw hsum hd₀ hd₁ probabilities (P := f2Archived42) (slope := slope)
    _ _ _ _ _ _ f2Archived42_data_ok ![f2Archived42Chart0, f2Archived42Chart1, f2Archived42Chart2] _
    facetRowTangent_le (prismCornerSound_of_numeric f2Archived42_data_ok)
  · intro i cap
    funext s
    fin_cases i <;> cases cap <;> fin_cases s <;>
      norm_num [realVertex, vertexAt, f2Archived42, Tangent.vertex, f2Archived42Base, facetCap]
  · funext s
    fin_cases s <;> norm_num [realPi, f2Archived42, pi, weightDen]
  · intro i cap
    funext j
    fin_cases i <;> cases cap <;> fin_cases j <;>
      norm_num [realGamma, realInput, vertexAt, inputNumerator, f2Archived42, weightDen,
        pi, slope, f2Archived42Base, prismWeight, facetWeight, facetCap, Fin.castSucc]
  · intro i cap
    constructor
    · intro j
      fin_cases i <;> cases cap <;> fin_cases j <;>
        norm_num [prismWeight, facetWeight, f2Archived42Base, pi, slope, facetCap, Fin.castSucc]
    · fin_cases i <;> cases cap <;>
        norm_num [prismWeight, facetWeight, f2Archived42Base, pi, slope, facetCap, Fin.castSucc, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> decide
  · intro i x hx
    apply cone i
    simpa [f2Archived42] using hx
  · intro j
    fin_cases j
    · exact f2Archived42Chart0_ok
    · exact f2Archived42Chart1_ok
    · exact f2Archived42Chart2_ok

end

end HlawkaSchatten.BelowExponent.FacetNumeric
