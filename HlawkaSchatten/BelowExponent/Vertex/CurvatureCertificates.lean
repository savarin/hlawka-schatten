/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureSound

/-! Curvature and weight certificates used by the parameter covers. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def CornerMarginAt (margins : Fin 3 → ℚ) (z : Row) (a b η : ℝ) : Prop :=
  (∑ m, (margins m : ℝ) * |z m| ^ criticalQ) ≤ parameterGap criticalQ z a b η

/-- The required inequality at each of a cell's eight closed corners. -/
def CellCornerMargins (c : ParameterCell) (margins : Fin 3 → ℚ) (z : Row) : Prop :=
  ∀ i j k : Bool, CornerMarginAt margins z (chooseCorner i (c.lower 0) (c.upper 0))
      (chooseCorner j (c.lower 1) (c.upper 1)) (chooseCorner k (c.lower 2) (c.upper 2))

theorem CornerMarginAt.mono {small large : Fin 3 → ℚ} {z : Row} {a b η : ℝ}
    (hbudget : ∀ m, small m ≤ large m) (h : CornerMarginAt large z a b η) :
    CornerMarginAt small z a b η :=
  (Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right
    (show (small m : ℝ) ≤ large m by exact_mod_cast hbudget m)
    (Real.rpow_nonneg (abs_nonneg _) _)).trans h

theorem CellCornerMargins.of_shared {c : ParameterCell} {margins : Fin 3 → ℚ} {z : Row}
    {stored : Bool → Bool → Bool → Fin 3 → ℚ}
    (hbudget : ∀ i j k m, margins m ≤ stored i j k m)
    (hrecord : ∀ i j k : Bool, CornerMarginAt (stored i j k) z
      (chooseCorner i (c.lower 0) (c.upper 0)) (chooseCorner j (c.lower 1) (c.upper 1))
      (chooseCorner k (c.lower 2) (c.upper 2))) : CellCornerMargins c margins z :=
  fun i j k => (hrecord i j k).mono (hbudget i j k)

structure CurvatureCellCertificate where
  cell : ParameterCell
  margins : Fin 3 → ℚ
  weightFloor : ℚ
  weightFloor_nonneg : 0 ≤ weightFloor
  weight_bound : ∀ {a b η : ℝ}, cell.Contains a b η →
    ∀ j, (weightFloor : ℝ) ≤ parameterWeight a b η j
  gap_of_corners : ∀ {a b η : ℝ} {z : Row}, cell.Contains a b η → CellCornerMargins cell margins z →
    0 ≤ parameterGap criticalQ z a b η

namespace CurvatureCellCertificate

def of_layer_checks {c : ParameterCell} {roots : Fin 3 → RatBounds} {na nb nη : ℕ}
    {caps : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ} {margins : Fin 3 → ℚ}
    (hroot : c.rootsOK roots = true)
    (hlayers : ∀ i, gridLayerCurvatureOK c roots na nb nη caps weightFloor i = true)
    (hdom : c.jetDomainOK = true) (hcaps : ∀ k i, 0 ≤ caps k i)
    (hmargin : ∀ i, curvatureLoss c caps i ≤ margins i)
    (hcounts : 0 < na ∧ 0 < nb ∧ 0 < nη) (hfloor : 0 ≤ weightFloor) : CurvatureCellCertificate := by
  have hg := gridCurvatureOK_of_layers hlayers
  refine ⟨c, margins, weightFloor, hfloor, ?_, ?_⟩
  · intro a b η ht
    exact (gridCurvatureOK_sound ht hcounts.1 hcounts.2.1 hcounts.2.2 hroot hg).1
  · intro a b η z ht hcorner
    exact ParameterCell.parameterGap_of_curvature_grid ht hcounts.1 hcounts.2.1 hcounts.2.2
      hroot hg hdom hcaps hmargin hcorner

theorem weight_nonneg (cert : CurvatureCellCertificate) {a b η : ℝ}
    (ht : cert.cell.Contains a b η) (j : Fin 3) : 0 ≤ parameterWeight a b η j :=
  (show (0 : ℝ) ≤ cert.weightFloor by exact_mod_cast cert.weightFloor_nonneg).trans (cert.weight_bound ht j)

end CurvatureCellCertificate

/-- Apply the certificate of the cell supplied by a parameter cover. -/
theorem curvatureRows_of_cover {certs : List CurvatureCellCertificate} {a b η : ℝ} {applies : Row → Prop}
    (hcover : ∃ cert ∈ certs, cert.cell.Contains a b η)
    (hcorners : ∀ cert ∈ certs, ∀ z, applies z → CellCornerMargins cert.cell cert.margins z) :
    (∀ j, 0 ≤ parameterWeight a b η j) ∧ (∀ z, applies z → 0 ≤ parameterGap criticalQ z a b η) := by
  obtain ⟨cert, hm, ht⟩ := hcover
  exact ⟨cert.weight_nonneg ht, fun z hz => cert.gap_of_corners ht (hcorners cert hm z hz)⟩

theorem curvatureRows_of_cell_cover {certs : List CurvatureCellCertificate} {grid : List ParameterCell}
    {a b η : ℝ} {applies : Row → Prop}
    (hgrid : certs.map CurvatureCellCertificate.cell = grid)
    (hcover : ∃ c ∈ grid, c.Contains a b η)
    (hcorners : ∀ cert ∈ certs, ∀ z, applies z → CellCornerMargins cert.cell cert.margins z) :
    (∀ j, 0 ≤ parameterWeight a b η j) ∧ (∀ z, applies z → 0 ≤ parameterGap criticalQ z a b η) := by
  obtain ⟨c, hc, ht⟩ := hcover
  rw [← hgrid] at hc
  obtain ⟨cert, hm, rfl⟩ := List.mem_map.mp hc
  exact curvatureRows_of_cover ⟨cert, hm, ht⟩ hcorners

end HlawkaSchatten.BelowExponent.Vertex
