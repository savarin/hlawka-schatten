/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.SideConeParameterGrid

/-! Curvature and corner checks on the same parameter cover as the side near cone. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem side_curvature_rows_of_grid {certs : List CurvatureCellCertificate} {applies : Row → Prop}
    (hgrid : certs.map CurvatureCellCertificate.cell = scParameterGrid)
    (hcorners : ∀ cert ∈ certs, ∀ z, applies z → CellCornerMargins cert.cell cert.margins z)
    {a b η : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1/40) (hb : b ≤ 1-a-b)
    (hab : 1/5 ≤ a+b) (hη : 0 ≤ η) (hη₁ : η ≤ 1/6) :
    (∀ j, 0 ≤ parameterWeight a b η j) ∧ (∀ z, applies z → 0 ≤ parameterGap criticalQ z a b η) := by
  have hb₁ : b ≤ 1/2 := by linarith only [ha, hb]
  exact curvatureRows_of_cell_cover hgrid (scParameterGrid_cover ha ha₁ hb₁ hab hη hη₁) hcorners

end HlawkaSchatten.BelowExponent.Vertex
