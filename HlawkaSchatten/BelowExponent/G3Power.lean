/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Bulk

/-! Integer cross-power witnesses for rational G3 endpoint evaluations. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3Power

def crossLE (x y : ℚ) (m n : ℕ) : Bool :=
  decide (x.num.natAbs ^ m * y.den ^ n ≤ y.num.natAbs ^ n * x.den ^ m)

def lower (x y : ℚ) : Bool :=
  if |x| ≤ 1 then crossLE y x 200 317 else crossLE y x 53 84

def upper (x y : ℚ) : Bool :=
  if |x| ≤ 1 then crossLE x y 84 53 else crossLE x y 317 200

private theorem abs_cast_fraction (x : ℚ) :
    |(x : ℝ)| = (x.num.natAbs : ℝ) / x.den := by
  rw [Rat.cast_def, abs_div, ← Int.cast_abs, ← Int.natCast_natAbs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  simp

theorem crossLE_upper {x y : ℚ} {m n : ℕ} (hn : 0 < n)
    (h : crossLE x y m n = true) :
    |(x : ℝ)| ^ ((m : ℝ) / n) ≤ |(y : ℝ)| := by
  rw [abs_cast_fraction, abs_cast_fraction]
  exact (natRat_rpow_le_iff x.den_pos y.den_pos hn).mpr (of_decide_eq_true h)

theorem crossLE_lower {x y : ℚ} {m n : ℕ} (hn : 0 < n)
    (h : crossLE y x n m = true) :
    |(y : ℝ)| ≤ |(x : ℝ)| ^ ((m : ℝ) / n) := by
  rw [abs_cast_fraction, abs_cast_fraction]
  have hx : y.num.natAbs ^ n * x.den ^ m ≤ x.num.natAbs ^ m * y.den ^ n :=
    of_decide_eq_true h
  exact (le_natRat_rpow_iff x.den_pos y.den_pos hn).mpr hx

private theorem q_bracket : (84 / 53 : ℝ) ≤ criticalQ ∧ criticalQ ≤ 317 / 200 :=
  ⟨(by norm_num : (84 / 53 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le,
    criticalQ_bracket.2.le.trans (by norm_num)⟩

theorem lower_sound {x y : ℚ} (h : lower x y = true) :
    (y : ℝ) ≤ |(x : ℝ)| ^ criticalQ := by
  have hb := rpow_exponent_bounds (abs_nonneg (x : ℝ)) (by norm_num)
    q_bracket.1 q_bracket.2
  unfold lower at h
  split at h
  · rename_i hx
    have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
    simp only [ite_eq_left hx'] at hb
    exact (le_abs_self _).trans ((crossLE_lower (by decide) h).trans hb.1)
  · rename_i hx
    have hx' : ¬ |(x : ℝ)| ≤ 1 := fun h => hx (by exact_mod_cast h)
    simp only [ite_eq_right hx'] at hb
    exact (le_abs_self _).trans ((crossLE_lower (by decide) h).trans hb.1)

theorem upper_sound {x y : ℚ} (hy : 0 ≤ y) (h : upper x y = true) :
    |(x : ℝ)| ^ criticalQ ≤ (y : ℝ) := by
  have hy' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  rw [← abs_of_nonneg hy']
  have hb := rpow_exponent_bounds (abs_nonneg (x : ℝ)) (by norm_num)
    q_bracket.1 q_bracket.2
  unfold upper at h
  split at h
  · rename_i hx
    have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
    simp only [ite_eq_left hx'] at hb
    exact hb.2.trans (crossLE_upper (by decide) h)
  · rename_i hx
    have hx' : ¬ |(x : ℝ)| ≤ 1 := fun h => hx (by exact_mod_cast h)
    simp only [ite_eq_right hx'] at hb
    exact hb.2.trans (crossLE_upper (by decide) h)

def tightLower (x y : ℚ) : Bool :=
  if |x| ≤ 1 then crossLE y x 306 485 else crossLE y x 665 1054

def tightUpper (x y : ℚ) : Bool :=
  if |x| ≤ 1 then crossLE x y 1054 665 else crossLE x y 485 306

theorem tightLower_sound {x y : ℚ} (h : tightLower x y = true) :
    (y : ℝ) ≤ |(x : ℝ)| ^ criticalQ := by
  have hb := rpow_exponent_bounds (abs_nonneg (x : ℝ))
    (by norm_num) criticalQ_bracket.1.le criticalQ_bracket.2.le
  unfold tightLower at h
  split at h
  · rename_i hx
    have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
    simp only [ite_eq_left hx'] at hb
    exact (le_abs_self _).trans ((crossLE_lower (by decide) h).trans hb.1)
  · rename_i hx
    have hx' : ¬ |(x : ℝ)| ≤ 1 := fun h => hx (by exact_mod_cast h)
    simp only [ite_eq_right hx'] at hb
    exact (le_abs_self _).trans ((crossLE_lower (by decide) h).trans hb.1)

theorem tightUpper_sound {x y : ℚ} (hy : 0 ≤ y) (h : tightUpper x y = true) :
    |(x : ℝ)| ^ criticalQ ≤ (y : ℝ) := by
  have hy' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  rw [← abs_of_nonneg hy']
  have hb := rpow_exponent_bounds (abs_nonneg (x : ℝ))
    (by norm_num) criticalQ_bracket.1.le criticalQ_bracket.2.le
  unfold tightUpper at h
  split at h
  · rename_i hx
    have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
    simp only [ite_eq_left hx'] at hb
    exact hb.2.trans (crossLE_upper (by decide) h)
  · rename_i hx
    have hx' : ¬ |(x : ℝ)| ≤ 1 := fun h => hx (by exact_mod_cast h)
    simp only [ite_eq_right hx'] at hb
    exact hb.2.trans (crossLE_upper (by decide) h)

def tightCurve (x y : ℚ) : Bool :=
  if x ≤ 1 then crossLE (1 / x) y 276 665 else crossLE (1 / x) y 127 306

theorem tightCurve_sound {x y : ℚ} (hx : 0 < x) (hy : 0 ≤ y) (h : tightCurve x y = true) :
    (x : ℝ) ^ (criticalQ - 2) ≤ (y : ℝ) := by
  have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
  have hy' : 0 ≤ (y : ℝ) := by exact_mod_cast hy
  have heq : |((1 / x : ℚ) : ℝ)| = (x : ℝ)⁻¹ := by
    push_cast
    rw [one_div, abs_of_nonneg (inv_nonneg.mpr hx'.le)]
  rw [show criticalQ - 2 = -(2 - criticalQ) by ring, Real.rpow_neg hx'.le,
    ← Real.inv_rpow hx'.le, ← heq, ← abs_of_nonneg hy']
  have hb := rpow_exponent_bounds (abs_nonneg (((1 / x : ℚ) : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 127 / 306)
    (show (127 / 306 : ℝ) ≤ 2 - criticalQ by linarith only [criticalQ_bracket.2])
    (show 2 - criticalQ ≤ (276 / 665 : ℝ) by linarith only [criticalQ_bracket.1])
  unfold tightCurve at h
  rcases le_or_gt x 1 with hx₁ | hx₁
  · simp only [ite_eq_left hx₁] at h
    have hx₁' : (x : ℝ) ≤ 1 := by exact_mod_cast hx₁
    have hinv : 1 ≤ |((1 / x : ℚ) : ℝ)| := by
      rw [heq, ← one_div, le_div_iff₀ hx', one_mul]
      exact hx₁'
    have hupper := crossLE_upper (by decide) h
    rcases hinv.eq_or_lt with h1 | h1
    · simpa only [← h1, Real.one_rpow] using hupper
    · simp only [ite_eq_right (not_le.mpr h1)] at hb
      exact hb.2.trans hupper
  · simp only [ite_eq_right (not_le.mpr hx₁)] at h
    have hx₁' : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx₁
    have hinv : |((1 / x : ℚ) : ℝ)| ≤ 1 := by
      rw [heq, ← one_div, div_le_iff₀ hx', one_mul]
      exact hx₁'.le
    simp only [ite_eq_left hinv] at hb
    exact hb.2.trans (crossLE_upper (by decide) h)

end HlawkaSchatten.BelowExponent.G3Power
