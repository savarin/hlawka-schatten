/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3Band`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop3_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (sLower : 9/50 ≤ σ) (sUpper : σ ≤ 19/100) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  have h0 : (0 : ℝ) ≤ h := hh.le
  rcases le_total h (9/136) with hHi | h1
  · exact CutTop3H0_gap hh hσ hσ₁ hCap h0 hHi sLower sUpper hs hz
  rcases le_total h (9/68) with hHi | h2
  · exact CutTop3H1_gap hh hσ hσ₁ hCap h1 hHi sLower sUpper hs hz
  rcases le_total h (27/136) with hHi | h3
  · exact CutTop3H2_gap hh hσ hσ₁ hCap h2 hHi sLower sUpper hs hz
  rcases le_total h (9/34) with hHi | h4
  · exact CutTop3H3_gap hh hσ hσ₁ hCap h3 hHi sLower sUpper hs hz
  rcases le_total h (45/136) with hHi | h5
  · exact CutTop3H4_gap hh hσ hσ₁ hCap h4 hHi sLower sUpper hs hz
  rcases le_total h (27/68) with hHi | h6
  · exact CutTop3H5_gap hh hσ hσ₁ hCap h5 hHi sLower sUpper hs hz
  rcases le_total h (63/136) with hHi | h7
  · exact CutTop3H6_gap hh hσ hσ₁ hCap h6 hHi sLower sUpper hs hz
  have hHi := g3_h_max hσ₁ hCap
  exact CutTop3H7_gap hh hσ hσ₁ hCap h7 hHi sLower sUpper hs hz

end HlawkaSchatten.BelowExponent.G3P
