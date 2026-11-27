/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3Band
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4Band

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTopComplete`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem cut_top_chart {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (sLower : 3/20 ≤ σ) (sUpper : σ ≤ 1/5) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  rcases le_total σ (4/25) with sHi | s1
  · exact CutTop0_gap hh hσ hσ₁ hCap sLower sHi hs hz
  rcases le_total σ (17/100) with sHi | s2
  · exact CutTop1_gap hh hσ hσ₁ hCap s1 sHi hs hz
  rcases le_total σ (9/50) with sHi | s3
  · exact CutTop2_gap hh hσ hσ₁ hCap s2 sHi hs hz
  rcases le_total σ (19/100) with sHi | s4
  · exact CutTop3_gap hh hσ hσ₁ hCap s3 sHi hs hz
  exact CutTop4_gap hh hσ hσ₁ hCap s4 sUpper hs hz

end HlawkaSchatten.BelowExponent.G3P
