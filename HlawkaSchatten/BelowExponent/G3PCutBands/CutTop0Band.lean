/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0Band`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop0_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (sLower : 3/20 ≤ σ) (sUpper : σ ≤ 4/25) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  have h0 : (0 : ℝ) ≤ h := hh.le
  rcases le_total h (9/136) with hHi | h1
  · exact CutTop0H0_gap hh hσ hσ₁ hCap h0 hHi sLower sUpper hs hz
  rcases le_total h (9/68) with hHi | h2
  · exact CutTop0H1_gap hh hσ hσ₁ hCap h1 hHi sLower sUpper hs hz
  rcases le_total h (27/136) with hHi | h3
  · exact CutTop0H2_gap hh hσ hσ₁ hCap h2 hHi sLower sUpper hs hz
  rcases le_total h (9/34) with hHi | h4
  · exact CutTop0H3_gap hh hσ hσ₁ hCap h3 hHi sLower sUpper hs hz
  rcases le_total h (45/136) with hHi | h5
  · exact CutTop0H4_gap hh hσ hσ₁ hCap h4 hHi sLower sUpper hs hz
  rcases le_total h (27/68) with hHi | h6
  · exact CutTop0H5_gap hh hσ hσ₁ hCap h5 hHi sLower sUpper hs hz
  rcases le_total h (63/136) with hHi | h7
  · exact CutTop0H6_gap hh hσ hσ₁ hCap h6 hHi sLower sUpper hs hz
  have hHi := g3_h_max hσ₁ hCap
  exact CutTop0H7_gap hh hσ hσ₁ hCap h7 hHi sLower sUpper hs hz

end HlawkaSchatten.BelowExponent.G3P
