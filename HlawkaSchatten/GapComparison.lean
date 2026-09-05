/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.Basic

/-!
# Transferring Hlawka inequalities through gap comparisons

This file isolates the last, purely ordered-algebraic step in the
Bregman--Mazur proof of the dimension-independent Schatten Hlawka bound.
If the three-body gap for one size functional is bounded above by the gap
for a model functional, while every two-body gap is bounded below by the
corresponding model gap, then a Hlawka inequality for the model transfers.
-/

namespace HlawkaSchatten

variable {E : Type*} [Add E]

/-- The triangle-inequality deficit of a size functional at two vectors. -/
def pairGap (size : E → ℝ) (x y : E) : ℝ :=
  size x + size y - size (x + y)

/-- The triangle-inequality deficit of a size functional at three vectors. -/
def tripleGap (size : E → ℝ) (x y z : E) : ℝ :=
  size x + size y + size z - size (x + y + z)

/-- The sum of all three pair deficits associated to a triple. -/
def pairGapSum (size : E → ℝ) (x y z : E) : ℝ :=
  pairGap size x y + pairGap size x z + pairGap size y z

/-- A size functional satisfies the three-vector Hlawka inequality with constant `C`. -/
def HasHlawkaConstant (size : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap size x y z ≤ C * pairGapSum size x y z

/--
The final comparison step in the Bregman--Mazur route to a Hlawka bound.

In the Schatten application, `size` is the Schatten `p`-norm, `model` is
the Hilbert--Schmidt norm after the Mazur map, and the comparison constants
are `2 * m` and `2 * M`. The hypotheses before `hModel` are supplied by the
spectral-lift, rectangular-dilation, and variational layers. The conclusion
is the desired factor `M / m`, with no loss from the factors of two.
-/
theorem tripleGap_le_ratio_mul_pairGapSum
    (size model : E → ℝ) (m M : ℝ) (x y z : E)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hTriple : tripleGap size x y z ≤ 2 * M * tripleGap model x y z)
    (hPairXY : 2 * m * pairGap model x y ≤ pairGap size x y)
    (hPairXZ : 2 * m * pairGap model x z ≤ pairGap size x z)
    (hPairYZ : 2 * m * pairGap model y z ≤ pairGap size y z)
    (hModel : tripleGap model x y z ≤ pairGapSum model x y z) :
    tripleGap size x y z ≤ (M / m) * pairGapSum size x y z := by
  have hPair : 2 * m * pairGapSum model x y z ≤ pairGapSum size x y z := by
    dsimp only [pairGapSum]
    nlinarith
  have hRatio : 0 ≤ M / m := div_nonneg hM hm.le
  have hScaled := mul_le_mul_of_nonneg_left hPair hRatio
  have hCancel :
      (M / m) * (2 * m * pairGapSum model x y z) =
        2 * M * pairGapSum model x y z := by
    field_simp [ne_of_gt hm]
  rw [hCancel] at hScaled
  calc
    tripleGap size x y z ≤ 2 * M * tripleGap model x y z := hTriple
    _ ≤ 2 * M * pairGapSum model x y z :=
      mul_le_mul_of_nonneg_left hModel (mul_nonneg (by positivity) hM)
    _ ≤ (M / m) * pairGapSum size x y z := hScaled

/--
A global form of `tripleGap_le_ratio_mul_pairGapSum`. This is the exact
logical interface between the analytic comparison layers and the final
Hlawka conclusion.
-/
theorem hasHlawkaConstant_of_gapComparison
    (size model : E → ℝ) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hTriple : ∀ x y z,
      tripleGap size x y z ≤ 2 * M * tripleGap model x y z)
    (hPair : ∀ x y, 2 * m * pairGap model x y ≤ pairGap size x y)
    (hModel : HasHlawkaConstant model 1) :
    HasHlawkaConstant size (M / m) := by
  intro x y z
  apply tripleGap_le_ratio_mul_pairGapSum size model m M x y z hm hM
  · exact hTriple x y z
  · exact hPair x y
  · exact hPair x z
  · exact hPair y z
  · simpa only [one_mul] using hModel x y z

/-- A positive three-body gap with vanishing pair-gap sum rules out every constant. -/
theorem no_hlawkaConstant_of_pairGapSum_eq_zero
    (size : E → ℝ) (x y z : E)
    (hTriple : 0 < tripleGap size x y z)
    (hPairs : pairGapSum size x y z = 0) :
    ∀ C : ℝ, ¬HasHlawkaConstant size C := by
  intro C hC
  have h := hC x y z
  rw [hPairs, mul_zero] at h
  exact (not_le_of_gt hTriple) h

end HlawkaSchatten
