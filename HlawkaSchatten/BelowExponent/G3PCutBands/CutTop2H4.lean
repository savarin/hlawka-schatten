/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertSound
public import HlawkaSchatten.BelowExponent.G3PCommonDenSound
public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4Pos
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4Neg

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop2H4_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (hLow : 9/34 ≤ h) (hHigh : h ≤ 45/136) (sLow : 17/100 ≤ σ)
    (sHigh : σ ≤ 9/50) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  exact signed_box_pair CutTop2H4Pos_gap CutTop2H4Neg_gap hh hσ hσ₁ hCap hs hz
      (by simpa using hLow) (by simpa using hHigh) (by simpa using sLow) (by simpa using sHigh)

end HlawkaSchatten.BelowExponent.G3P
