/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3SSound
public import HlawkaSchatten.BelowExponent.G3SBands.Band0
public import HlawkaSchatten.BelowExponent.G3SBands.Band1
public import HlawkaSchatten.BelowExponent.G3SBands.Band2
public import HlawkaSchatten.BelowExponent.G3SBands.Band3
public import HlawkaSchatten.BelowExponent.G3SBands.Band4

/-! Complete cover of the wider transverse G3 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3S

private theorem mem_band {lo hi : ℚ} {h σ p z : ℝ}
    (hh : 0 ≤ h) (hh₁ : h ≤ 9 / 17) (hlo : (lo : ℝ) ≤ σ) (hhi : σ ≤ (hi : ℝ))
    (hp : |p| ≤ 1) (hz : |z| ≤ 8) :
    (⟨![0, lo, -1, -8], ![9 / 17, hi, 1, 8]⟩ : Box).Mem ![h, σ, p, z] := by
  intro i
  fin_cases i
  · simpa using And.intro hh hh₁
  · exact ⟨hlo, hhi⟩
  · simpa using abs_le.mp hp
  · simpa using abs_le.mp hz

/-- The transverse chart holds on the full wider G3 corner with the common weight. -/
theorem wider_chart {h σ p z : ℝ} (hh : 0 < h) (hσ₀ : 7 / 10000 ≤ σ)
    (hσ₁ : σ ≤ 1 / 5) (hh₁ : h ≤ 1 / (2 - σ / (2 - σ)))
    (hp : |p| ≤ 1) (hz : |z| ≤ 8) : 0 ≤ g3FacetGap h σ p 1 z := by
  have hh' := g3_h_max hσ₁ hh₁
  have hheight : h ≤ 1 := hh'.trans (by norm_num)
  have hσpos : 0 < σ := (by norm_num : (0 : ℝ) < 7 / 10000).trans_le hσ₀
  have close {lo hi : ℚ} {t : Tree} (ht : t.ok ⟨![0, lo, -1, -8], ![9 / 17, hi, 1, 8]⟩ = true)
      (hlo : (lo : ℝ) ≤ σ) (hhi : σ ≤ (hi : ℝ)) : 0 ≤ g3FacetGap h σ p 1 z :=
    tree_sound ht (mem_band hh.le hh' hlo hhi hp hz) hheight hσpos hp hz
  rcases le_total σ (1 / 50) with h | h
  · exact close Band0_ok (by simpa using hσ₀) (by simpa using h)
  rcases le_total σ (1 / 20) with h' | h'
  · exact close Band1_ok (by simpa using h) (by simpa using h')
  rcases le_total σ (1 / 10) with h | h
  · exact close Band2_ok (by simpa using h') (by simpa using h)
  rcases le_total σ (3 / 20) with h' | h'
  · exact close Band3_ok (by simpa using h) (by simpa using h')
  exact close Band4_ok (by simpa using h') (by simpa using hσ₁)

end HlawkaSchatten.BelowExponent.G3S
