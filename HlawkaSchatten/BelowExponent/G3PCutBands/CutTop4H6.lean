/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertSound
public import HlawkaSchatten.BelowExponent.G3PCommonDenSound
public import HlawkaSchatten.BelowExponent.G3PGeometryCheckSound
public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6Pos
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6Neg

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop4H6_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (hLow : 27/68 ≤ h) (hHigh : h ≤ 63/136) (sLow : 19/100 ≤ σ)
    (sHigh : σ ≤ 1/5) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  exact signed_box_pair CutTop4H6Pos_gap CutTop4H6Neg_gap hh hσ hσ₁ hCap hs hz
      (by simpa using hLow) (by simpa using hHigh) (by simpa using sLow) (by simpa using sHigh)

end HlawkaSchatten.BelowExponent.G3P
