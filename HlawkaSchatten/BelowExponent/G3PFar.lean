/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Compact
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import all HlawkaSchatten.BelowExponent.G1
import all HlawkaSchatten.BelowExponent.G1Far
import all HlawkaSchatten.BelowExponent.G1Large
import all HlawkaSchatten.BelowExponent.G1Compact

/-! Transverse upper bounds for the G3 p = 1 chart at all positive heights. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set
open private criticalQ_lo criticalQ_hi from HlawkaSchatten.BelowExponent.G1Far
open private absPower_convex from HlawkaSchatten.BelowExponent.G1
open private absPower_deriv from HlawkaSchatten.BelowExponent.G1Large
open private variance_tangent from HlawkaSchatten.BelowExponent.G1Compact

noncomputable section

private def f (x : ℝ) : ℝ := |x| ^ criticalQ

private def signedPower (r x : ℝ) : ℝ := if 0 ≤ x then |x| ^ r else -|x| ^ r

private def D (x : ℝ) : ℝ := criticalQ * signedPower (criticalQ - 1) x

private theorem q_lower : 1 < criticalQ := by linarith [criticalQ_lo]

private theorem f_deriv (x : ℝ) : HasDerivAt f (D x) x := absPower_deriv q_lower x

private theorem signedPower_gap {r x y : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hxy : x ≤ y) :
    signedPower r y - signedPower r x ≤ (2 : ℝ) ^ (1 - r) * (y - x) ^ r := by
  have hK : 1 ≤ (2 : ℝ) ^ (1 - r) := Real.one_le_rpow (by norm_num) (by linarith)
  have hside {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : b ^ r - a ^ r ≤ (b - a) ^ r := by
    have h := Real.rpow_add_le_add_rpow ha (sub_nonneg.mpr hab) hr₀ hr₁
    rw [show a + (b - a) = b by ring] at h
    linarith only [h]
  have hscale : (y - x) ^ r ≤ (2 : ℝ) ^ (1 - r) * (y - x) ^ r :=
    le_mul_of_one_le_left (Real.rpow_nonneg (sub_nonneg.mpr hxy) _) hK
  by_cases hx : 0 ≤ x
  · have hy := hx.trans hxy
    simpa only [signedPower, ite_eq_left hx, ite_eq_left hy, abs_of_nonneg hx, abs_of_nonneg hy] using
      (hside hx hxy).trans hscale
  by_cases hy : 0 ≤ y
  · have hx₁ := lt_of_not_ge hx
    have h := (Real.concaveOn_rpow hr₀ hr₁).2 (show -x ∈ Ici 0 from neg_nonneg.mpr hx₁.le)
      (show y ∈ Ici 0 from hy) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simp only [smul_eq_mul] at h
    rw [show (1 / 2 : ℝ) * (-x) + 1 / 2 * y = (y - x) / 2 by ring,
      Real.div_rpow (sub_nonneg.mpr hxy) (by norm_num)] at h
    have heq : 2 * ((y - x) ^ r / (2 : ℝ) ^ r) = (2 : ℝ) ^ (1 - r) * (y - x) ^ r := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      ring
    simp only [signedPower, ite_eq_right hx, ite_eq_left hy, abs_of_neg hx₁, abs_of_nonneg hy]
    linarith only [h, heq]
  · have hx₁ := lt_of_not_ge hx
    have hy₁ := lt_of_not_ge hy
    have h := hside (show 0 ≤ -y by linarith) (show -y ≤ -x by linarith)
    rw [show -x - -y = y - x by ring] at h
    simp only [signedPower, ite_eq_right hx, ite_eq_right hy, abs_of_neg hx₁, abs_of_neg hy₁]
    linarith only [h, hscale]

private theorem D_holder (x y : ℝ) :
    |D y - D x| ≤ criticalQ * (2 : ℝ) ^ (2 - criticalQ) * |y - x| ^ (criticalQ - 1) := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge hxy)
  have hconv := absPower_convex (q := criticalQ) q_lower.le
  have hd : Monotone D := by
    intro a b hab
    have hm := hconv.monotoneOn_deriv (fun t _ => (f_deriv t).differentiableAt)
      (mem_univ a) (mem_univ b) hab
    change deriv f a ≤ deriv f b at hm
    simpa only [(f_deriv a).deriv, (f_deriv b).deriv] using hm
  rw [abs_of_nonneg (sub_nonneg.mpr (hd hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
  unfold D
  rw [← mul_sub, mul_assoc, show 2 - criticalQ = 1 - (criticalQ - 1) by ring]
  exact mul_le_mul_of_nonneg_left
    (signedPower_gap (by linarith [q_lower]) (by linarith [criticalQ_hi]) hxy) (by linarith [q_lower])

private theorem f_remainder (x d : ℝ) :
    f (x + d) - f x - d * D x ≤ (2 : ℝ) ^ (2 - criticalQ) * |d| ^ criticalQ := by
  let K := (2 : ℝ) ^ (2 - criticalQ)
  let R (t : ℝ) := f (x + t * d) - f x - t * d * D x - K * |d| ^ criticalQ * f t
  have hd (t : ℝ) : HasDerivAt R
      ((D (x + t * d) - D x) * d - K * |d| ^ criticalQ * D t) t := by
    have h₁ := (f_deriv (x + t * d)).comp t (((hasDerivAt_id t).mul_const d).const_add x)
    have h₂ := (((hasDerivAt_id t).mul_const d).mul_const (D x))
    convert (((h₁.sub_const (f x)).sub h₂).sub ((f_deriv t).const_mul (K * |d| ^ criticalQ))) using 1
    · rfl
    · ring
  have hR : AntitoneOn R (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    intro t ht
    rw [interior_Ici] at ht
    have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [(hd t).deriv, sub_nonpos]
    have h := D_holder x (x + t * d)
    rw [show x + t * d - x = t * d by ring, abs_mul, abs_of_nonneg ht₀,
      Real.mul_rpow ht₀ (abs_nonneg d)] at h
    have hh := mul_le_mul_of_nonneg_right h (abs_nonneg d)
    rw [show (criticalQ * K * (t ^ (criticalQ - 1) * |d| ^ (criticalQ - 1))) * |d| =
        criticalQ * K * t ^ (criticalQ - 1) * (|d| ^ (criticalQ - 1) * |d|) by ring] at hh
    have hpow : |d| ^ (criticalQ - 1) * |d| = |d| ^ criticalQ := by
      by_cases hz : |d| = 0
      · rw [hz, mul_zero, Real.zero_rpow (ne_of_gt (by linarith [q_lower]))]
      · rw [← Real.rpow_add_one hz, sub_add_cancel]
    rw [hpow] at hh
    have hDt : D t = criticalQ * t ^ (criticalQ - 1) := by
      simp only [D, signedPower, ite_eq_left ht₀, abs_of_nonneg ht₀]
    rw [hDt]
    have hsign := le_abs_self ((D (x + t * d) - D x) * d)
    rw [abs_mul] at hsign
    change criticalQ * K * t ^ (criticalQ - 1) * |d| ^ criticalQ ≥ _ at hh
    linarith only [hsign, hh]
  have h := hR (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show (1 : ℝ) ∈ Ici 0 from zero_le_one) zero_le_one
  dsimp [R, f] at h
  simp only [one_mul, zero_mul, add_zero, sub_self, abs_one, Real.one_rpow, abs_zero,
    Real.zero_rpow (ne_of_gt (by linarith [q_lower] : 0 < criticalQ)), mul_zero, mul_one] at h
  exact sub_nonpos.mp h

private theorem f_tangent (x d : ℝ) : f x + d * D x ≤ f (x + d) := by
  let g (t : ℝ) := f (x + t * d)
  have hg : ConvexOn ℝ univ g := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ u v hu hv huv
    simp only [g, smul_eq_mul]
    rw [show x + (u * a + v * b) * d = u * (x + a * d) + v * (x + b * d) by
      linear_combination -x * huv]
    exact (absPower_convex q_lower.le).2 (mem_univ _) (mem_univ _) hu hv huv
  have hd : HasDerivAt g (D x * d) 0 := by
    simpa [g, Function.comp_def] using (f_deriv (x + (0 : ℝ) * d)).comp 0
      (((hasDerivAt_id (0 : ℝ)).mul_const d).const_add x)
  have h := hg.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) zero_lt_one hd
  simp only [slope_def_field, g, sub_zero, div_one, one_mul, zero_mul, add_zero] at h
  linarith

theorem g3FarIncrement_div_le_power {h Z s : ℝ} (hh : 0 < h) :
    balancedFarIncrement criticalQ (1 - h) Z s / h ≤ 2 * |s| ^ criticalQ := by
  let y := Z + h * s
  have ht := f_tangent y (-h * s)
  rw [show y + -h * s = Z by dsimp [y]; ring] at ht
  have hR := f_remainder y (-2*s)
  rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg s), ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), sub_add_cancel, Real.rpow_ofNat] at hR
  apply (div_le_iff₀ hh).2
  unfold balancedFarIncrement
  change ((1 - (1 - h)) / 2) * f (Z - (1 + (1 - h)) * s) +
    ((1 + (1 - h)) / 2) * f (Z + (1 - (1 - h)) * s) - f Z ≤ _
  rw [show Z - (1 + (1 - h)) * s = y + -2*s by dsimp [y]; ring,
    show Z + (1 - (1 - h)) * s = y by dsimp [y]; ring]
  have h := mul_le_mul_of_nonneg_right hR (show 0 ≤ h/2 by positivity)
  linarith only [ht, h]

theorem g3FarIncrement_div_le_quadratic {h Z s : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hZ : Z ≠ 0) : balancedFarIncrement criticalQ (1 - h) Z s / h ≤
      criticalQ / 2 * (2 - h) * |Z| ^ (criticalQ - 2) * s ^ 2 := by
  have hZ₀ := abs_pos.mpr hZ
  have he : |1 - h| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hh₁)]; linarith
  have hc : 0 ≤ 1 - (1 - h) ^ 2 := by
    rw [show 1 - (1 - h) ^ 2 = h * (2 - h) by ring]
    exact mul_nonneg hh.le (by linarith)
  have hVariance := balancedFarIncrement_le_variance (q := criticalQ) (e := 1-h)
    (by linarith [q_lower]) (by linarith [criticalQ_hi]) he Z s
  have hTan := variance_tangent hZ₀ (add_nonneg (sq_nonneg Z) (mul_nonneg hc (sq_nonneg s)))
  have hratio : |Z| ^ criticalQ / |Z| ^ (2 : ℕ) = |Z| ^ (criticalQ - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hZ₀]
  rw [hratio] at hTan
  have hZeq : |Z| ^ (criticalQ - 2) * Z ^ 2 = |Z| ^ criticalQ := by
    rw [← sq_abs Z, ← Real.rpow_two, ← Real.rpow_add hZ₀, sub_add_cancel]
  apply (div_le_iff₀ hh).2
  have hh' : (criticalQ / 2) * |Z| ^ (criticalQ - 2) * (1 - (1 - h)^2) * s^2 =
      criticalQ / 2 * (2 - h) * |Z| ^ (criticalQ - 2) * s ^ 2 * h := by ring
  have htan' : (Z^2 + (1 - (1 - h)^2) * s^2) ^ (criticalQ / 2) ≤ |Z|^criticalQ +
      (criticalQ / 2) * |Z| ^ (criticalQ - 2) * (1 - (1 - h)^2) * s^2 := by
    linarith only [hTan, congrArg (fun x : ℝ => (criticalQ / 2) * x) hZeq]
  linarith only [hVariance, htan', hh']

end

end HlawkaSchatten.BelowExponent
