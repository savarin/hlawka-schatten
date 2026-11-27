/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Bulk

/-! The completed-square and parameter-endpoint tests for a side-cone quadratic. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

def sideQuadratic (A B C V G K e x y : ℝ) : ℝ :=
  e * (V + G * x + K * y) + A * x ^ 2 + 2 * B * x * y + C * y ^ 2

def adjugateCost (A B C G K : ℝ) : ℝ := C * G ^ 2 - 2 * B * G * K + A * K ^ 2

theorem adjugateCost_nonneg {A B C G K : ℝ}
    (hA : 0 < A) (hD : 0 ≤ A * C - B ^ 2) :
    0 ≤ adjugateCost A B C G K := by
  have h := add_nonneg (sq_nonneg (A * K - B * G)) (mul_nonneg hD (sq_nonneg G))
  have heq : A * adjugateCost A B C G K =
      (A * K - B * G) ^ 2 + (A * C - B ^ 2) * G ^ 2 := by
    unfold adjugateCost
    ring
  exact nonneg_of_mul_nonneg_right (heq ▸ h) hA

/-- The exact global minimum comparison used by the positive determinant branch. -/
theorem sideQuadratic_det_nonneg {A B C V G K e eMax x y : ℝ}
    (hA : 0 < A) (hD : 0 < A * C - B ^ 2) (he : 0 ≤ e) (hcap : e ≤ eMax)
    (hmargin : eMax * adjugateCost A B C G K ≤ 4 * (A * C - B ^ 2) * V) :
    0 ≤ sideQuadratic A B C V G K e x y := by
  let D := A * C - B ^ 2
  let X := adjugateCost A B C G K
  have hX : 0 ≤ X := adjugateCost_nonneg hA hD.le
  have hm : 0 ≤ 4 * D * V - e * X :=
    sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hcap hX).trans hmargin)
  have hsum := add_nonneg
    (add_nonneg (mul_nonneg hD.le (sq_nonneg (2 * A * x + 2 * B * y + e * G)))
      (sq_nonneg (2 * D * y + e * (A * K - B * G))))
    (mul_nonneg (mul_nonneg hA.le he) hm)
  have heq : 4 * A * D * sideQuadratic A B C V G K e x y =
      D * (2 * A * x + 2 * B * y + e * G) ^ 2 +
        (2 * D * y + e * (A * K - B * G)) ^ 2 + A * e * (4 * D * V - e * X) := by
    unfold D X sideQuadratic adjugateCost
    ring
  rw [← heq] at hsum
  exact nonneg_of_mul_nonneg_right hsum (mul_pos (mul_pos (by norm_num) hA) hD)

/-- The other branch checks the two closed first-direction endpoints. -/
theorem sideQuadratic_of_endpoints {A B C V G K e lo hi x y : ℝ}
    (hlo : lo ≤ e) (hhi : e ≤ hi)
    (hl : 0 ≤ sideQuadratic A B C V G K lo x y)
    (hr : 0 ≤ sideQuadratic A B C V G K hi x y) :
    0 ≤ sideQuadratic A B C V G K e x y := by
  rcases le_total 0 (V + G * x + K * y) with h | h
  · unfold sideQuadratic at *
    linarith only [hl, mul_le_mul_of_nonneg_right hlo h]
  · unfold sideQuadratic at *
    linarith only [hr, mul_le_mul_of_nonpos_right hhi h]

end

end HlawkaSchatten.BelowExponent.Vertex
