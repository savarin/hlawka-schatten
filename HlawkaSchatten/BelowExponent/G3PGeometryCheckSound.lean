/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData
public import HlawkaSchatten.BelowExponent.G3PGeometrySound

/-! The native geometry checker preserves the accepted ratio coverage and row predicates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

open Vertex (RatK RatBounds RatBoundsK)

private theorem lo_val (A : RatBoundsK) : A.lo.val = A.val.lo := rfl
private theorem hi_val (A : RatBoundsK) : A.hi.val = A.val.hi := rfl

theorem PowerCache.geometryRowCheck_eq {c : PowerCache} (hc : c.valid = true)
    (B : Box) (b : Bool) (w : RowWitness) : c.geometryRowCheck B b w = c.rowCheck B b w := by
  simp only [geometryRowCheck, rowCheck, Geometry.ratOfK_eq, Geometry.unit_val, Geometry.domainOK_eq,
    Geometry.jensenOK_eq,
    Geometry.farWitnessOK_eq hc, farCheck_eq hc, Geometry.rowQuad_eq]

theorem CertTree.geometryOK_eq {c : PowerCache} (hc : c.valid = true)
    (t : CertTree) (B : Box) (b : Bool) : t.geometryOK c B b = t.sharedOK c B b := by
  induction t generalizing B with
  | cone | empty => rfl
  | row w => exact PowerCache.geometryRowCheck_eq hc B b w
  | cut j m l r hl hr =>
    simp only [geometryOK, sharedOK, Box.lowerChildK_eq, Box.upperChildK_eq, hl, hr]

theorem CertTree.commonOK_of_geometryOK {c : PowerCache} (hc : c.valid = true)
    {t : CertTree} {B : Box} {b : Bool} (h : t.geometryOK c B b = true) :
    t.commonOK B b = true :=
  (t.sharedOK_eq hc B b).symm.trans ((t.geometryOK_eq hc B b).symm.trans h)

theorem TiledRow.geometryOKOnRatio_eq (w : TiledRow) (c : PowerCache)
    (B : Box) (b : Bool) (A : RatBounds) :
    w.geometryOKOnRatio c B b A = w.sharedOKOnRatio c B b A := by
  apply Bool.eq_iff_iff.mpr
  simp only [geometryOKOnRatio, sharedOKOnRatio, Geometry.ratOfK_eq, Geometry.unit_val,
    Geometry.domainOK_eq,
    Geometry.jensenOK_eq, Geometry.farTilesOK_eq, Geometry.tiledQuad_eq,
    RatK.le_eq, RatK.val_zero, RatK.val_ofRat, Bool.and_eq_true, decide_eq_true_eq]

theorem geometryChartGuard_eq (B : Box) :
    geometryChartGuard B = decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [geometryChartGuard, RatK.le_eq, RatK.lt_eq, Bool.and_eq_true, decide_eq_true_eq]
  simp only [RatK.val_ofRat, RatK.val_one, hi_val, Geometry.lBounds_val]

theorem geometryCoveredGuard_eq (B : Box) (cap : ℚ) :
    geometryCoveredGuard B cap = decide (0 < B.lo 2 ∧ B.hi 1 ≤ 1/5 ∧ (lBounds B).hi ≤ 1 ∧
      (absBounds (center B)).hi ≤ cap * B.lo 2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [geometryCoveredGuard, RatK.le_eq, RatK.lt_eq, Bool.and_eq_true, decide_eq_true_eq]
  simp only [RatK.val_ofRat, RatK.val_one, RatK.val_zero, RatK.val_mul, hi_val,
    Geometry.lBounds_val, Geometry.absolute_val, Geometry.center_val, and_assoc]

theorem RatioChart.geometryOK_eq {c : PowerCache} (hc : c.valid = true)
    (t : RatioChart) (B : Box) (b : Bool) : t.geometryOK c B b = t.ok B b := by
  have h : t.geometryOK c B b = t.sharedOK c B b := by
    induction t generalizing B with
    | original t =>
      simp only [geometryOK, sharedOK, geometryChartGuard_eq, Geometry.physicalBox_eq,
        CertTree.geometryOK_eq hc]
    | row w =>
      simp only [geometryOK, sharedOK, geometryChartGuard_eq, Geometry.physicalBox_eq,
        TiledRow.geometryOKOnRatio_eq]
    | cut j m l r hl hr =>
      simp only [geometryOK, sharedOK, Box.lowerChildK_eq, Box.upperChildK_eq, hl, hr]
  exact h.trans (t.sharedOK_eq hc B b)

theorem RatioRemainder.geometryOK_eq {c : PowerCache} (hc : c.valid = true)
    (t : RatioRemainder) (B : Box) (b : Bool) (cap : ℚ) :
    t.geometryOK c B b cap = t.ok B b cap := by
  have h : t.geometryOK c B b cap = t.sharedOK c B b cap := by
    induction t generalizing B with
    | original t => exact CertTree.geometryOK_eq hc t B b
    | covered => exact geometryCoveredGuard_eq B cap
    | cut j m l r hl hr =>
      simp only [geometryOK, sharedOK, Box.lowerChildK_eq, Box.upperChildK_eq, hl, hr]
  exact h.trans (t.sharedOK_eq hc B b cap)

theorem RatioChart.ok_of_geometryOK {c : PowerCache} (hc : c.valid = true)
    {t : RatioChart} {B : Box} {b : Bool} (h : t.geometryOK c B b = true) :
    t.ok B b = true := (t.geometryOK_eq hc B b).symm.trans h

theorem RatioRemainder.ok_of_geometryOK {c : PowerCache} (hc : c.valid = true)
    {t : RatioRemainder} {B : Box} {b : Bool} {cap : ℚ}
    (h : t.geometryOK c B b cap = true) : t.ok B b cap = true :=
  (t.geometryOK_eq hc B b cap).symm.trans h

end

end HlawkaSchatten.BelowExponent.G3P
