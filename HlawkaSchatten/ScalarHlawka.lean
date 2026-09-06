/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.GapComparison

/-!
# The scalar Hlawka inequality

The absolute value on the real line satisfies Hlawka with constant one.
This scalar fact is not on the final proof path but records the pointwise
inequality underlying the Hilbert-space Hlawka theorem.
-/

namespace HlawkaSchatten

/-- The real scalar absolute-value form of Hlawka's inequality. -/
theorem abs_pair_sums_le (a b c : ℝ) :
    |a + b| + |a + c| + |b + c| ≤
      |a| + |b| + |c| + |a + b + c| := by
  rcases le_total 0 a with ha | ha <;>
  rcases le_total 0 b with hb | hb <;>
  rcases le_total 0 c with hc | hc <;>
  rcases le_total 0 (a + b) with hab | hab <;>
  rcases le_total 0 (a + c) with hac | hac <;>
  rcases le_total 0 (b + c) with hbc | hbc <;>
  rcases le_total 0 (a + b + c) with habc | habc <;>
  simp_all only [abs_of_nonneg, abs_of_nonpos] <;>
  linarith

/-- The gap form of the real scalar Hlawka inequality. -/
theorem abs_hasHlawkaConstant : HasHlawkaConstant (abs : ℝ → ℝ) 1 := by
  intro a b c
  dsimp only [tripleGap, pairGapSum, pairGap]
  have h := abs_pair_sums_le a b c
  simp only [one_mul]
  linarith

end HlawkaSchatten
