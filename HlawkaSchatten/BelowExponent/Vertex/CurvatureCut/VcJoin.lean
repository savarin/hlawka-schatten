/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.Addresses
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddle
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBand
public import HlawkaSchatten.BelowExponent.Vertex.SideCornerLinks
public import HlawkaSchatten.BelowExponent.Vertex.VcCurvatureJoin
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.PointTable

/-! The revised shared VC budgets supply both original physical vertex regions. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 30000

set_option maxHeartbeats 0 in
theorem vcCutMiddleLinks_checked : sideCornerGridLookupOK (sideCornerBlockLookup vcCutPointBlocks)
    vcCutMiddleCertificates vcCutMiddleLinks = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem vcCutBandLinks_checked : sideCornerGridLookupOK (sideCornerBlockLookup vcCutPointBlocks)
    vcCutBandCertificates vcCutBandLinks = true := by decide +kernel

private theorem vcCutPointLookup_valid
    (hpoints : SideCornerEntriesOK (fun _ => True) vcCutPoints.toList)
    (n : ℕ) (p : SideCornerEntry) (hp : sideCornerBlockLookup vcCutPointBlocks n = some p) :
    p.ValidFor (fun _ => True) := by
  have hm := sideCornerBlockLookup_mem hp
  rw [vcCutPoints_toList] at hm
  exact sideCornerEntriesOK_mem (xs := vcCutPoints.toList) hpoints hm

private theorem vcCut_direction_bounds {t : Profile} (ht : OrderedInterior t)
    (hmax : maxDirection t ≤ 4/5) :
    directions t 0 ≤ directions t 1 ∧ directions t 1 ≤ 1-directions t 0-directions t 1 ∧
      1/5 ≤ directions t 0+directions t 1 := by
  have h₁ : directions t 1 ≤ directions t 2 := div_le_div_of_nonneg_right ht.second_ge ht.depth_pos.le
  have hs : directions t 0+directions t 1+directions t 2 = 1 := by
    simpa only [Fin.sum_univ_three] using directions_sum ht
  change directions t 2 ≤ 4/5 at hmax
  exact ⟨div_le_div_of_nonneg_right ht.third_ge ht.depth_pos.le,
    by linarith only [h₁, hs], by linarith only [hmax, hs]⟩

theorem rowAt_vertexMiddle_cut (hpoints : SideCornerEntriesOK (fun _ => True) vcCutPoints.toList)
    {t : Profile} (ht : OrderedInterior t) (hmin : 1/20 ≤ minDirection t)
    (hmax : maxDirection t ≤ 4/5) (hdepth : vertexDepth t ≤ 1/20) : RowAt criticalQ t := by
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  have hsmall : vertexDepth t < 1/2 := by linarith only [hdepth]
  have hden : 0 < 1-2*vertexDepth t := by linarith only [hdepth]
  have hη : 0 ≤ vertexDepth t/(1-2*vertexDepth t) := div_nonneg ht.depth_pos.le hden.le
  have hη' : vertexDepth t/(1-2*vertexDepth t) ≤ 1/18 :=
    (div_le_iff₀ hden).2 (by linarith only [hdepth])
  obtain ⟨hab, hb, hs⟩ := vcCut_direction_bounds ht hmax
  apply rowAt_of_parameter_rows hq ht hsmall
  apply vc_middle_curvature_rows_of_grid vcCutMiddleCertificates_cells _ hmin hab hb hs hη hη'
  intro c hcell z
  exact sideCornerGridLookup_sound (applies := fun _ => True) vcCutMiddleLinks_checked
    (vcCutPointLookup_valid hpoints) c hcell z True.intro

theorem rowAt_vertexBand_cut (hpoints : SideCornerEntriesOK (fun _ => True) vcCutPoints.toList)
    {t : Profile} (ht : OrderedInterior t) (hmin₀ : 1/40 ≤ minDirection t)
    (hmin₁ : minDirection t ≤ 1/20) (hmax : maxDirection t ≤ 4/5)
    (hdepth : vertexDepth t ≤ 1/12) : RowAt criticalQ t := by
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  have hsmall : vertexDepth t < 1/2 := by linarith only [hdepth]
  have hden : 0 < 1-2*vertexDepth t := by linarith only [hdepth]
  have hη : 0 ≤ vertexDepth t/(1-2*vertexDepth t) := div_nonneg ht.depth_pos.le hden.le
  have hη' : vertexDepth t/(1-2*vertexDepth t) ≤ 1/10 :=
    (div_le_iff₀ hden).2 (by linarith only [hdepth])
  obtain ⟨_, hb, hs⟩ := vcCut_direction_bounds ht hmax
  apply rowAt_of_parameter_rows hq ht hsmall
  apply vc_band_curvature_rows_of_grid vcCutBandCertificates_cells _ hmin₀ hmin₁ hb hs hη hη'
  intro c hcell z
  exact sideCornerGridLookup_sound (applies := fun _ => True) vcCutBandLinks_checked
    (vcCutPointLookup_valid hpoints) c hcell z True.intro

end HlawkaSchatten.BelowExponent.Vertex
