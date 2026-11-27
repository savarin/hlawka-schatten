/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertSound
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0Pos
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0Neg

/-! Closed height slabs in one central G3 ratio band. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem Low0_gap {h σ s z : ℝ} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (hS₀ : 7/10000 ≤ σ) (hS₁ : σ ≤ 1/20) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  have hHeight := g3_h_max hσ₁ hCap
  have hLow0 : (0 : ℝ) ≤ h := hh.le
  have hHigh := hHeight
  exact box_pair Low0H0Pos_ok Low0H0Neg_ok hh hσ hσ₁ hCap hs hz
      (by simpa using hLow0) (by simpa using hHigh) (by simpa using hS₀) (by simpa using hS₁)

end HlawkaSchatten.BelowExponent.G3P
