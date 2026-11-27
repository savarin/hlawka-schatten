/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideCutCorners.PointTable
public import HlawkaSchatten.BelowExponent.Vertex.SideCornerLinks
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.Addresses
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.Side
public import HlawkaSchatten.BelowExponent.Vertex.SidePhysicalGrid

/-! Join the revised shared SC corner budgets to their checked curvature cells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem scCutOuterLinks_checked :
    sideCornerGridLookupOK (sideCornerBlockLookup scCutOuterPointBlocks)
      scCutCurvatureCertificates scCutLinks = true := by
  decide +kernel

theorem rowAt_vertexSide_of_cut_corners
    (hpoints : SideCornerEntriesOK (fun z => ¬ InSideNearCone z) scCutOuterPoints.toList)
    (hnear : ∀ c ∈ scParameterGrid, ∀ ij ∈ sideRowGrid,
      SideConeOn c (sideURange ij.1) (sideVRange ij.2))
    {t : Profile} (ht : OrderedInterior t) (hmin : minDirection t ≤ 1/40)
    (hmax : maxDirection t ≤ 4/5) (hdepth : vertexDepth t ≤ 1/8) : RowAt criticalQ t := by
  apply rowAt_vertexSide_of_checked_grid scCutCurvatureCertificates_cells _
    hnear ht hmin hmax hdepth
  apply sideCornerGridLookup_sound (applies := fun z => ¬ InSideNearCone z) scCutOuterLinks_checked
  intro n p hp
  have hm : p ∈ scCutOuterPointBlocks.flatMap Array.toList := sideCornerBlockLookup_mem hp
  rw [scCutOuterPoints_toList] at hm
  exact sideCornerEntriesOK_mem hpoints hm

end HlawkaSchatten.BelowExponent.Vertex
