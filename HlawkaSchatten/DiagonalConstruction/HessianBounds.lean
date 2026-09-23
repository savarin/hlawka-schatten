/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.NormHessian
import HlawkaSchatten.DiagonalConstruction.BoxGeometry

/-! # Uniform lower and upper bounds for the norm Hessian -/

namespace HlawkaSchatten.DiagonalConstruction

/-- The lower Hessian coefficient `(p-1)(43/100)^(p-2) / (3(157/100)^(p-1))`. -/
noncomputable def lowerHessianCoefficient (p : ℝ) : ℝ :=
  (p - 1) * (43 / 100 : ℝ) ^ (p - 2) / (3 * (157 / 100 : ℝ) ^ (p - 1))

/-- The upper Hessian coefficient `2(p-1)(38/100)^(p-2) / (162/100)^(p-1)`. -/
noncomputable def upperHessianCoefficient (p : ℝ) : ℝ :=
  2 * (p - 1) * (19 / 50 : ℝ) ^ (p - 2) / (81 / 50 : ℝ) ^ (p - 1)

/-- The lower Hessian coefficient is strictly positive. -/
theorem lowerHessianCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < lowerHessianCoefficient p := by
  unfold lowerHessianCoefficient
  positivity

/-- The upper Hessian coefficient is strictly positive. -/
theorem upperHessianCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < upperHessianCoefficient p := by
  unfold upperHessianCoefficient
  positivity

/-- A `(p-1)`-power bound using the `p`-norm. -/
theorem lpNorm_pred_le_three_mul {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ M) :
    lpNorm p v ^ (p - 1) ≤ 3 * M ^ (p - 1) := by
  have hp0 := zero_lt_one.trans hp
  have hN := lpNorm_le_card_root_mul hp0 hM v hv
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hN
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg p v) hN (by linarith : 0 ≤ p - 1)
  rw [Real.mul_rpow (by positivity) hM, ← Real.rpow_mul (by norm_num)] at hpower
  have he : 1 / p * (p - 1) = 1 - 1 / p := by field_simp
  rw [he] at hpower
  have hthree : (3 : ℝ) ^ (1 - 1 / p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show 1 - 1 / p ≤ 1 by have := one_div_nonneg.mpr hp0.le; linarith)
    simpa only [Real.rpow_one] using h
  exact hpower.trans (mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hM _))

/-- Lower bound on the norm Hessian inside the box. -/
theorem normHessian_lower {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ)
    (hlo : ∀ i, 43 / 100 ≤ |v i|) (hhi : ∀ i, |v i| ≤ 157 / 100) :
    lowerHessianCoefficient p * euclideanSq (h - radialCoefficient p v h • v) ≤
      normHessian p v h := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hv : v ≠ 0 := by intro hv; have hh := hlo 0; norm_num [hv] at hh
  have hN := lpNorm_pos hp0 hv
  have hden := lpNorm_pred_le_three_mul (p := p) (by linarith) (by norm_num) v hhi
  have hweight : (43 / 100 : ℝ) ^ (p - 2) *
      euclideanSq (h - radialCoefficient p v h • v) ≤
        powerResidual p v h (radialCoefficient p v h) := by
    simp only [euclideanSq, powerResidual, Finset.mul_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) (hlo i) (by linarith))
      (sq_nonneg _)
  have hcoefficient : lowerHessianCoefficient p ≤
      ((p - 1) / lpNorm p v ^ (p - 1)) * (43 / 100 : ℝ) ^ (p - 2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (p - 1) * (43 / 100 : ℝ) ^ (p - 2) by positivity)
      (Real.rpow_pos_of_pos hN _) hden
    calc
      _ ≤ ((p - 1) * (43 / 100 : ℝ) ^ (p - 2)) / lpNorm p v ^ (p - 1) := hh
      _ = _ := by ring
  rw [normHessian_eq_div hp0]
  calc
    _ ≤ (((p - 1) / lpNorm p v ^ (p - 1)) * (43 / 100 : ℝ) ^ (p - 2)) *
        euclideanSq (h - radialCoefficient p v h • v) :=
      mul_le_mul_of_nonneg_right hcoefficient (euclideanSq_nonneg _)
    _ = ((p - 1) / lpNorm p v ^ (p - 1)) *
        ((43 / 100 : ℝ) ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)

private theorem erased_residual_sq_le (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) ≤ 2 * euclideanSq h := by
  have hkv : 0 < |v k| := by linarith
  have hr (i : Fin 3) (hik : i ≠ k) : |v i / v k| ≤ 19 / 81 := by
    rw [abs_div, div_le_iff₀ hkv]
    linarith [hi i hik]
  have hsq (i : Fin 3) (hik : i ≠ k) : (v i / v k) ^ 2 ≤ (19 / 81 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hr i hik)
  have hterm (i : Fin 3) (hik : i ≠ k) : (h i - h k / v k * v i) ^ 2 ≤
      2 * (h i) ^ 2 + 2 * (h k) ^ 2 * (19 / 81 : ℝ) ^ 2 := by
    have hyoung := sq_nonneg (h i + h k * (v i / v k))
    have hm := mul_le_mul_of_nonneg_left (hsq i hik) (sq_nonneg (h k))
    have he : h k / v k * v i = h k * (v i / v k) := by ring
    rw [he]
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ.erase k)
    (fun i hi ↦ hterm i (Finset.mem_erase.mp hi).1)
  have hsum : (∑ i ∈ Finset.univ.erase k, (h i) ^ 2) + (h k) ^ 2 = euclideanSq h := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ k)
  norm_num only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  nlinarith [sq_nonneg (h k)]

/-- Upper bound on the norm Hessian inside the box. -/
theorem normHessian_upper {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    normHessian p v h ≤ upperHessianCoefficient p * euclideanSq h := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hkv : v k ≠ 0 := by intro he; norm_num [he] at hk
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : 81 / 50 ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm hp1 v k)
  have hden : (81 / 50 : ℝ) ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow (by norm_num) hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      (19 / 50 : ℝ) ^ (p - 2) * (2 * euclideanSq h) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    have he : powerResidual p v h (h k / v k) =
        ∑ i ∈ Finset.univ.erase k, |v i| ^ (p - 2) * (h i - h k / v k * v i) ^ 2 := by
      rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero]
    rw [he]
    calc
      _ ≤ ∑ i ∈ Finset.univ.erase k, (19 / 50 : ℝ) ^ (p - 2) *
          (h i - h k / v k * v i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi'
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
          (sq_nonneg _)
      _ = (19 / 50 : ℝ) ^ (p - 2) *
          (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (erased_residual_sq_le v h k hk hi) (by positivity)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / (81 / 50 : ℝ) ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) * ((19 / 50 : ℝ) ^ (p - 2) * (2 * euclideanSq h)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / (81 / 50 : ℝ) ^ (p - 1)) * ((19 / 50 : ℝ) ^ (p - 2) * (2 * euclideanSq h)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by positivity)
        (mul_nonneg (by norm_num) (euclideanSq_nonneg h)))
    _ = _ := by unfold upperHessianCoefficient; ring

end HlawkaSchatten.DiagonalConstruction
