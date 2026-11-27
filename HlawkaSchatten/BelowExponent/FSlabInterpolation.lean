/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCone

/-! Three output comparisons suffice when the profile and its weights vary with the imbalance. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def weightedOutput (q : ℝ) (t π : Profile) (x : Row) : ℝ :=
  ∑ j, π j * |rowEval t j x| ^ q

/-- Two diagonal bounds and the averaged mixed bound control the entire interpolation. -/
theorem weightedOutput_profile_weight_lerp {q u C : ℝ} {t₀ t₁ π₀ π₁ : Profile} {x : Row}
    (hq : 1 ≤ q) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (hπ₀ : ∀ j, 0 ≤ π₀ j) (hπ₁ : ∀ j, 0 ≤ π₁ j)
    (h₀₀ : weightedOutput q t₀ π₀ x ≤ C)
    (h₁₁ : weightedOutput q t₁ π₁ x ≤ C)
    (h₀₁ : weightedOutput q t₀ π₁ x + weightedOutput q t₁ π₀ x ≤ 2 * C) :
    weightedOutput q (profileLerp u t₀ t₁) (profileLerp u π₀ π₁) x ≤ C := by
  let a := 1 - u
  have ha : 0 ≤ a := sub_nonneg.mpr hu₁
  calc
    _ ≤ ∑ j, (a * π₀ j + u * π₁ j) *
        (a * |rowEval t₀ j x| ^ q + u * |rowEval t₁ j x| ^ q) := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (abs_rowEval_rpow_profileLerp_le hq hu₀ hu₁ t₀ t₁ j x)
          (add_nonneg (mul_nonneg ha (hπ₀ j)) (mul_nonneg hu₀ (hπ₁ j)))
    _ = ∑ j, (a ^ 2 * (π₀ j * |rowEval t₀ j x| ^ q) +
        (a * u * (π₁ j * |rowEval t₀ j x| ^ q) +
          a * u * (π₀ j * |rowEval t₁ j x| ^ q)) +
        u ^ 2 * (π₁ j * |rowEval t₁ j x| ^ q)) := by
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = a ^ 2 * weightedOutput q t₀ π₀ x +
        a * u * (weightedOutput q t₀ π₁ x + weightedOutput q t₁ π₀ x) +
        u ^ 2 * weightedOutput q t₁ π₁ x := by
      simp only [weightedOutput, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ a ^ 2 * C + a * u * (2 * C) + u ^ 2 * C := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₀₀ (sq_nonneg a))
        (mul_le_mul_of_nonneg_left h₀₁ (mul_nonneg ha hu₀)))
        (mul_le_mul_of_nonneg_left h₁₁ (sq_nonneg u))
    _ = C := by dsimp [a]; ring

theorem balancedOutput_of_imbalance_interval {μ l e₀ e₁ u C : ℝ} {x : Row}
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (he₀ : 0 ≤ e₀) (he₁ : e₁ ≤ 1/2) (he : e₀ ≤ e₁) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (h₀₀ : weightedOutput criticalQ (balancedProfile l e₀ l) (balancedPi μ e₀) x ≤ C)
    (h₁₁ : weightedOutput criticalQ (balancedProfile l e₁ l) (balancedPi μ e₁) x ≤ C)
    (hmix : weightedOutput criticalQ (balancedProfile l e₀ l) (balancedPi μ e₁) x +
      weightedOutput criticalQ (balancedProfile l e₁ l) (balancedPi μ e₀) x ≤ 2 * C) :
    weightedOutput criticalQ (balancedProfile l ((1-u)*e₀+u*e₁) l)
      (balancedPi μ ((1-u)*e₀+u*e₁)) x ≤ C := by
  have h0 : |e₀| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  have h1 : |e₁| ≤ 1 := by rw [abs_of_nonneg (he₀.trans he)]; linarith
  have ht : profileLerp u (balancedProfile l e₀ l) (balancedProfile l e₁ l) =
      balancedProfile l ((1-u)*e₀+u*e₁) l := by
    funext j
    fin_cases j <;> simp [profileLerp, balancedProfile, splitProfile] <;> ring
  have hπ : profileLerp u (balancedPi μ e₀) (balancedPi μ e₁) =
      balancedPi μ ((1-u)*e₀+u*e₁) := by
    funext j
    fin_cases j <;> simp [profileLerp, balancedPi] <;> ring
  rw [← ht, ← hπ]
  exact weightedOutput_profile_weight_lerp facetCritical_one_lt.le hu₀ hu₁
    (isSimplex_balancedPi hμ₀ hμ₁ h0).1 (isSimplex_balancedPi hμ₀ hμ₁ h1).1 h₀₀ h₁₁ hmix

end

end HlawkaSchatten.BelowExponent
