/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.VcParameterGrid

/-! The vertex middle and band curvature checks on the exact parameter covers. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem vc_middle_curvature_rows_of_grid {certs : List CurvatureCellCertificate}
    (hgrid : certs.map CurvatureCellCertificate.cell = vcMiddleRefinedGrid)
    (hcorners : ∀ cert ∈ certs, ∀ z, CellCornerMargins cert.cell cert.margins z)
    {a b η : ℝ} (ha : 1/20 ≤ a) (hab : a ≤ b) (hb : b ≤ 1-a-b) (hs : 1/5 ≤ a+b)
    (hη : 0 ≤ η) (hη' : η ≤ 1/18) :
    (∀ j, 0 ≤ parameterWeight a b η j) ∧ (∀ z, 0 ≤ parameterGap criticalQ z a b η) := by
  have h := curvatureRows_of_cell_cover (applies := fun _ => True) hgrid
    (vcMiddleRefinedGrid_cover ha hab hb hs hη hη') (fun cert hm z _ => hcorners cert hm z)
  exact ⟨h.1, fun z => h.2 z True.intro⟩

theorem vc_band_curvature_rows_of_grid {certs : List CurvatureCellCertificate}
    (hgrid : certs.map CurvatureCellCertificate.cell = vcBandParameterGrid)
    (hcorners : ∀ cert ∈ certs, ∀ z, CellCornerMargins cert.cell cert.margins z)
    {a b η : ℝ} (ha : 1/40 ≤ a) (ha' : a ≤ 1/20) (hb : b ≤ 1-a-b) (hs : 1/5 ≤ a+b)
    (hη : 0 ≤ η) (hη' : η ≤ 1/10) :
    (∀ j, 0 ≤ parameterWeight a b η j) ∧ (∀ z, 0 ≤ parameterGap criticalQ z a b η) := by
  have h := curvatureRows_of_cell_cover (applies := fun _ => True) hgrid
    (vcBandParameterGrid_cover ha ha' hb hs hη hη') (fun cert hm z _ => hcorners cert hm z)
  exact ⟨h.1, fun z => h.2 z True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
