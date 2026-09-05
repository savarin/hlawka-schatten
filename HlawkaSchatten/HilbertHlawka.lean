/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import HlawkaSchatten.GapComparison

/-!
# Hlawka's inequality in inner-product spaces

This proof uses the quadrilateral square identity. It avoids the Gaussian
integration route from the paper while proving the same Hilbert-space layer.
-/

namespace HlawkaSchatten

/-- The numerical core of the quadrilateral proof of Hlawka's inequality. -/
private theorem seven_lengths_hlawka
    {a b c d α β γ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hγab : γ ≤ a + b) (hγcd : γ ≤ c + d)
    (hβac : β ≤ a + c) (hβbd : β ≤ b + d)
    (hαbc : α ≤ b + c) (hαad : α ≤ a + d)
    (hsq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = α ^ 2 + β ^ 2 + γ ^ 2) :
    α + β + γ ≤ a + b + c + d := by
  have hproducts : 0 ≤
      (a + b - γ) * (c + d - γ) +
      (a + c - β) * (b + d - β) +
      (b + c - α) * (a + d - α) := by
    positivity
  have hidentity :
      (a + b + c + d - (α + β + γ)) * (a + b + c + d) =
        (a + b - γ) * (c + d - γ) +
        (a + c - β) * (b + d - β) +
        (b + c - α) * (a + d - α) := by
    nlinarith [hsq]
  have hmul : 0 ≤
      (a + b + c + d - (α + β + γ)) * (a + b + c + d) := by
    rw [hidentity]
    exact hproducts
  by_cases hzero : a + b + c + d = 0
  · have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hc0 : c = 0 := by nlinarith
    have hd0 : d = 0 := by nlinarith
    nlinarith
  · have hpos : 0 < a + b + c + d := lt_of_le_of_ne (by positivity) (Ne.symm hzero)
    nlinarith

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

include 𝕜

/-- The seven norms in Hlawka's inequality satisfy the quadrilateral square identity. -/
theorem norm_hlawka_square_identity (x y z : E) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖x + y + z‖ ^ 2 =
      ‖y + z‖ ^ 2 + ‖x + z‖ ^ 2 + ‖x + y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜) x y, norm_add_sq (𝕜 := 𝕜) x z,
    norm_add_sq (𝕜 := 𝕜) y z, norm_add_sq (𝕜 := 𝕜) (x + y) z,
    norm_add_sq (𝕜 := 𝕜) x y]
  simp only [inner_add_left, map_add]
  ring

/-- Hlawka's inequality for the norm of any real or complex inner-product space. -/
theorem norm_pair_sums_le (x y z : E) :
    ‖x + y‖ + ‖x + z‖ + ‖y + z‖ ≤
      ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ := by
  rw [show ‖x + y‖ + ‖x + z‖ + ‖y + z‖ =
      ‖y + z‖ + ‖x + z‖ + ‖x + y‖ by ring]
  apply seven_lengths_hlawka
      (a := ‖x‖) (b := ‖y‖) (c := ‖z‖) (d := ‖x + y + z‖)
      (α := ‖y + z‖) (β := ‖x + z‖) (γ := ‖x + y‖)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  · exact norm_add_le x y
  · calc
      ‖x + y‖ = ‖(x + y + z) + -z‖ := by congr 1; abel
      _ ≤ ‖x + y + z‖ + ‖-z‖ := norm_add_le _ _
      _ = ‖z‖ + ‖x + y + z‖ := by rw [norm_neg]; ring
  · exact norm_add_le x z
  · calc
      ‖x + z‖ = ‖(x + y + z) + -y‖ := by congr 1; abel
      _ ≤ ‖x + y + z‖ + ‖-y‖ := norm_add_le _ _
      _ = ‖y‖ + ‖x + y + z‖ := by rw [norm_neg]; ring
  · exact norm_add_le y z
  · calc
      ‖y + z‖ = ‖(x + y + z) + -x‖ := by congr 1; abel
      _ ≤ ‖x + y + z‖ + ‖-x‖ := norm_add_le _ _
      _ = ‖x‖ + ‖x + y + z‖ := by rw [norm_neg]; ring
  · exact norm_hlawka_square_identity (𝕜 := 𝕜) x y z

/-- Every inner-product norm has Hlawka constant one. -/
theorem norm_hasHlawkaConstant : HasHlawkaConstant (norm : E → ℝ) 1 := by
  intro x y z
  dsimp only [tripleGap, pairGapSum, pairGap]
  have h := norm_pair_sums_le (𝕜 := 𝕜) x y z
  simp only [one_mul]
  linarith

/--
The completed final layer of the Bregman--Mazur route: two-sided comparison
with an inner-product norm yields Hlawka constant `M / m`.
-/
theorem hasHlawkaConstant_of_innerProductComparison
    (size : E → ℝ) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hTriple : ∀ x y z,
      tripleGap size x y z ≤ 2 * M * tripleGap (norm : E → ℝ) x y z)
    (hPair : ∀ x y,
      2 * m * pairGap (norm : E → ℝ) x y ≤ pairGap size x y) :
    HasHlawkaConstant size (M / m) :=
  hasHlawkaConstant_of_gapComparison size (norm : E → ℝ) m M hm hM hTriple hPair
    (norm_hasHlawkaConstant (𝕜 := 𝕜))

end HlawkaSchatten
