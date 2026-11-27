/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertSound
public import HlawkaSchatten.BelowExponent.G3PCommonDenSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1Pos
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1Neg

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid0H1_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (hLow : 9/68 ≤ h) (hHigh : h ≤ 9/34) (sLow : 1/20 ≤ σ)
    (sHigh : σ ≤ 7/100) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  exact box_pair (CertTree.ok_of_commonOK CutMid0H1Pos_checked) (CertTree.ok_of_commonOK CutMid0H1Neg_checked) hh hσ hσ₁ hCap hs hz
      (by simpa using hLow) (by simpa using hHigh) (by simpa using sLow) (by simpa using sHigh)

end HlawkaSchatten.BelowExponent.G3P
