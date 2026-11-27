/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideCurvatureJoin
public import HlawkaSchatten.BelowExponent.Vertex.SideConeJoin
public import HlawkaSchatten.BelowExponent.VertexRegion

/-! Assemble a checked curvature grid and near cone in physical profile coordinates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem rowAt_vertexSide_of_checked_grid {certs : List CurvatureCellCertificate}
    (hgrid : certs.map CurvatureCellCertificate.cell = scParameterGrid)
    (hcorners : ∀ cert ∈ certs, ∀ z,
      ¬ InSideNearCone z → CellCornerMargins cert.cell cert.margins z)
    (hnear : ∀ c ∈ scParameterGrid, ∀ ij ∈ sideRowGrid,
      SideConeOn c (sideURange ij.1) (sideVRange ij.2))
    {t : Profile} (ht : OrderedInterior t) (hmin : minDirection t ≤ 1/40)
    (hmax : maxDirection t ≤ 4/5) (hdepth : vertexDepth t ≤ 1/8) : RowAt criticalQ t := by
  classical
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  have hsmall : vertexDepth t < 1/2 := by linarith only [hdepth]
  have hden : 0 < 1-2*vertexDepth t := by linarith only [hdepth]
  have hη : 0 ≤ vertexDepth t/(1-2*vertexDepth t) := div_nonneg ht.depth_pos.le hden.le
  have hη' : vertexDepth t/(1-2*vertexDepth t) ≤ 1/6 :=
    (div_le_iff₀ hden).2 (by linarith only [hdepth])
  have ha : 0 ≤ directions t 0 := (directions_mem_unit ht 0).1
  have h₁ : directions t 1 ≤ directions t 2 := div_le_div_of_nonneg_right ht.second_ge ht.depth_pos.le
  have hs : directions t 0+directions t 1+directions t 2 = 1 := by
    simpa only [Fin.sum_univ_three] using directions_sum ht
  change directions t 0 ≤ 1/40 at hmin
  change directions t 2 ≤ 4/5 at hmax
  have hb : directions t 1 ≤ 1-directions t 0-directions t 1 := by linarith only [h₁, hs]
  have hab : 1/5 ≤ directions t 0+directions t 1 := by linarith only [hmax, hs]
  apply rowAt_of_parameter_rows hq ht hsmall
  obtain ⟨hweight, houter⟩ := side_curvature_rows_of_grid hgrid hcorners ha hmin hb hab hη hη'
  refine ⟨hweight, fun z => ?_⟩
  by_cases hz : InSideNearCone z
  · exact scNearGap_of_parameterGrid hnear ha hmin hb hab hη hη' hz
  · exact houter z hz

end HlawkaSchatten.BelowExponent.Vertex
