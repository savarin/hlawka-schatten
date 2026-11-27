/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1Band`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop1_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (sLower : 4/25 ≤ σ) (sUpper : σ ≤ 17/100) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  have h0 : (0 : ℝ) ≤ h := hh.le
  rcases le_total h (9/136) with hHi | h1
  · exact CutTop1H0_gap hh hσ hσ₁ hCap h0 hHi sLower sUpper hs hz
  rcases le_total h (9/68) with hHi | h2
  · exact CutTop1H1_gap hh hσ hσ₁ hCap h1 hHi sLower sUpper hs hz
  rcases le_total h (27/136) with hHi | h3
  · exact CutTop1H2_gap hh hσ hσ₁ hCap h2 hHi sLower sUpper hs hz
  rcases le_total h (9/34) with hHi | h4
  · exact CutTop1H3_gap hh hσ hσ₁ hCap h3 hHi sLower sUpper hs hz
  rcases le_total h (45/136) with hHi | h5
  · exact CutTop1H4_gap hh hσ hσ₁ hCap h4 hHi sLower sUpper hs hz
  rcases le_total h (27/68) with hHi | h6
  · exact CutTop1H5_gap hh hσ hσ₁ hCap h5 hHi sLower sUpper hs hz
  rcases le_total h (63/136) with hHi | h7
  · exact CutTop1H6_gap hh hσ hσ₁ hCap h6 hHi sLower sUpper hs hz
  have hHi := g3_h_max hσ₁ hCap
  exact CutTop1H7_gap hh hσ hσ₁ hCap h7 hHi sLower sUpper hs hz

end HlawkaSchatten.BelowExponent.G3P
