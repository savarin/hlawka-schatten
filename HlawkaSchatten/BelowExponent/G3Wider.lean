/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3HeadCertificate
public import HlawkaSchatten.BelowExponent.G3PCertBands.LowComplete
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMidComplete
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTopComplete
public import HlawkaSchatten.BelowExponent.G3SBands.Complete

/-! Assemble the full ordered G3 corner on its wider ratio interval. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

theorem g3_central_wider_chart {h σ s z : ℝ} (hh : 0 < h) (hσ₀ : 7 / 10000 ≤ σ)
    (hσ₁ : σ ≤ 1 / 5) (hh₁ : h ≤ 1 / (2 - σ / (2 - σ)))
    (hs : |s| ≤ 1) (hz : |z| ≤ 8) : 0 ≤ g3FacetGap h σ 1 s z := by
  have hp : 0 < σ := (by norm_num : (0 : ℝ) < 7 / 10000).trans_le hσ₀
  rcases le_total σ (1 / 20) with h | h
  · exact G3P.low_chart hh hp hσ₁ hh₁ hσ₀ h hs hz
  rcases le_total σ (3 / 20) with h' | h'
  · exact G3P.cut_mid_chart hh hp hσ₁ hh₁ h h' hs hz
  exact G3P.cut_top_chart hh hp hσ₁ hh₁ h' hσ₁ hs hz

theorem rowAt_vertexCorner_balanced {t : Profile} (ht : OrderedInterior t)
    (hσ₀ : 7 / 10000 ≤ sigma t) (hσ₁ : sigma t ≤ 1 / 5)
    (hh₀ : 0 < cornerH t) (hh₁ : cornerH t ≤ 1 / (2 - cornerK t)) :
    RowAt criticalQ t := by
  have hp : 0 < sigma t := (by norm_num : (0 : ℝ) < 7 / 10000).trans_le hσ₀
  apply rowAt_g3_of_charts ht hσ₀ hσ₁ hh₀ hh₁
  · intro p s hp₁ hs
    exact g3_head_chart_gap hh₀ hp hσ₁ hh₁ hp₁ hs
  · intro s z hs hz
    exact g3_central_wider_chart hh₀ hσ₀ hσ₁ hh₁ hs hz
  · intro p z hp₁ hz
    exact G3S.wider_chart hh₀ hσ₀ hσ₁ hh₁ hp₁ hz

end HlawkaSchatten.BelowExponent
