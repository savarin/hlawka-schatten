/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4Band

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMidComplete`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem cut_mid_chart {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (sLower : 1/20 ≤ σ) (sUpper : σ ≤ 3/20) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  rcases le_total σ (7/100) with sHi | s1
  · exact CutMid0_gap hh hσ hσ₁ hCap sLower sHi hs hz
  rcases le_total σ (9/100) with sHi | s2
  · exact CutMid1_gap hh hσ hσ₁ hCap s1 sHi hs hz
  rcases le_total σ (11/100) with sHi | s3
  · exact CutMid2_gap hh hσ hσ₁ hCap s2 sHi hs hz
  rcases le_total σ (13/100) with sHi | s4
  · exact CutMid3_gap hh hσ hσ₁ hCap s3 sHi hs hz
  exact CutMid4_gap hh hσ hσ₁ hCap s4 sUpper hs hz

end HlawkaSchatten.BelowExponent.G3P
