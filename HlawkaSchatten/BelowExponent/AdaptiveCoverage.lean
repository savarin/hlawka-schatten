/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Center
public import HlawkaSchatten.BelowExponent.Coverage

/-! Joins from the adaptive certificates to the existing ordered region statements. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- The part omitted by the radius-1/500 tangent cover is inside the
radius-1/100 Euclidean neighbourhood used by the centre certificate. -/
theorem e2_cube_subset_center_ball {t : Profile}
    (h : ∀ i, |t i - 1 / 4| ≤ 1 / 500) :
    ∑ i, (t i - centerProfile i) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _ : Fin 4, (1 / 500 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [centerProfile, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ ≤ _ := by norm_num

/-- E2 includes the cube interface. The centre certificate supplies its complement. -/
theorem rowAt_bulk_of_e2_and_center {q : ℝ}
    (hE2 : ∀ t : Profile, OrderedInterior t → 1 / 500 ≤ t 3 →
      (∃ i, 1 / 500 ≤ |t i - 1 / 4|) → RowAt q t)
    (hCenter : ∀ t : Profile, OrderedInterior t →
      (∑ i, (t i - centerProfile i) ^ 2 ≤ (1 / 100 : ℝ) ^ 2) → RowAt q t)
    {t : Profile} (ht : OrderedInterior t) (hd : 1 / 500 ≤ t 3) : RowAt q t := by
  by_cases h : ∃ i, 1 / 500 ≤ |t i - 1 / 4|
  · exact hE2 t ht hd h
  · apply hCenter t ht
    apply e2_cube_subset_center_ball
    exact fun i => (lt_of_not_ge fun hi => h ⟨i, hi⟩).le

/-- The F0–F2 depth cap includes the facet-interior constructor and the join at 1/500. -/
theorem rowAt_facetInterior_of_F0F2 {q : ℝ}
    (hF : ∀ t : Profile, OrderedInterior t → t 3 ≤ 1 / 400 →
      1 / 20 ≤ facetCoord t → RowAt q t)
    {t : Profile} (ht : OrderedInterior t) (hd : t 3 ≤ 1 / 500)
    (hf : 1 / 20 ≤ facetCoord t) : RowAt q t :=
  hF t ht (hd.trans (by norm_num)) hf

end HlawkaSchatten.BelowExponent
