/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.HessianBounds

/-! # Uniform scalar comparison of the Hessian coefficients -/

namespace HlawkaSchatten.DiagonalConstruction

/-- The ratio `d_p / b_p` equals `(157/27) (2983/3483)^(p-2)`. -/
theorem hessianCoefficient_ratio (p : ℝ) :
    upperHessianCoefficient p = lowerHessianCoefficient p * (157 / 27) *
      (2983 / 3483 : ℝ) ^ (p - 2) := by
  have hM : (157 / 100 : ℝ) ^ (p - 1) = (157 / 100 : ℝ) ^ (p - 2) * (157 / 100) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (81 / 50 : ℝ) ^ (p - 1) = (81 / 50 : ℝ) ^ (p - 2) * (81 / 50) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (2983 / 3483 : ℝ) ^ (p - 2) =
      ((19 / 50 : ℝ) ^ (p - 2) * (157 / 100 : ℝ) ^ (p - 2)) /
        ((81 / 50 : ℝ) ^ (p - 2) * (43 / 100 : ℝ) ^ (p - 2)) := by
    rw [show (2983 / 3483 : ℝ) = ((19 / 50) * (157 / 100)) / ((81 / 50) * (43 / 100)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperHessianCoefficient, lowerHessianCoefficient, hM, hL, hbase]
  field_simp
  ring

/-- The upper coefficient is strictly less than `8 b_p (6/7)^(p-2)`. -/
theorem upperHessianCoefficient_lt {p : ℝ} (hp : 2 < p) :
    upperHessianCoefficient p < 8 * lowerHessianCoefficient p * (6 / 7 : ℝ) ^ (p - 2) := by
  have hb := lowerHessianCoefficient_pos (show 1 < p by linarith)
  have hr := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6 / 7) (p - 2)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2983 / 3483)
    (by norm_num : (2983 / 3483 : ℝ) ≤ 6 / 7) (show 0 ≤ p - 2 by linarith)
  have hm := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ lowerHessianCoefficient p * (157 / 27) by positivity)
  rw [hessianCoefficient_ratio]
  nlinarith [mul_pos hb hr]

/-- The geometric decay `9600 p (6/7)^(p-2) < 1` for `p ≥ 256`. -/
theorem exponential_curvature_margin {p : ℝ} (hp : 256 ≤ p) :
    9600 * p * (6 / 7 : ℝ) ^ (p - 2) < 1 := by
  have hp0 : 0 < p := by linarith
  have hbase : (9600 * 256 : ℝ) < (7 / 6 : ℝ) ^ (254 : ℕ) := by norm_num
  have hlog : (1 / 7 : ℝ) ≤ Real.log (7 / 6) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 7 / 6 by norm_num)
    norm_num at h
    exact h
  have hgrowth : p / 256 ≤ (7 / 6 : ℝ) ^ (p - 256) := by
    have h := Real.add_one_le_exp (Real.log (7 / 6) * (p - 256))
    have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p - 256 by linarith)
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have hr : 0 < (7 / 6 : ℝ) ^ (p - 256) := by positivity
  have hprod := mul_lt_mul_of_pos_right hbase hr
  have he : (7 / 6 : ℝ) ^ (254 : ℕ) * (7 / 6 : ℝ) ^ (p - 256) =
      (7 / 6 : ℝ) ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    norm_num
    ring
  rw [he] at hprod
  have hlarge : 9600 * p < (7 / 6 : ℝ) ^ (p - 2) := by linarith
  have hinv : (6 / 7 : ℝ) ^ (p - 2) = ((7 / 6 : ℝ) ^ (p - 2))⁻¹ := by
    rw [show (6 / 7 : ℝ) = (7 / 6 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
  rw [hinv, ← div_eq_mul_inv, div_lt_one (by positivity)]
  exact hlarge

/-- The curvature margin `1200 p d_p < b_p` for `p ≥ 256`. -/
theorem hessian_curvature_margin {p : ℝ} (hp : 256 ≤ p) :
    1200 * p * upperHessianCoefficient p < lowerHessianCoefficient p := by
  have hb := lowerHessianCoefficient_pos (show 1 < p by linarith)
  have hU := upperHessianCoefficient_lt (show 2 < p by linarith)
  have hsmall := exponential_curvature_margin hp
  have hm := mul_lt_mul_of_pos_left hU (show 0 < 1200 * p by linarith)
  have hbsmall := mul_lt_mul_of_pos_left hsmall hb
  nlinarith

end HlawkaSchatten.DiagonalConstruction
