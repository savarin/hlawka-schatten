/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeAlgebra
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact integral forms for the first- and second-order SC power multipliers. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open MeasureTheory Set
open scoped Interval

noncomputable section

def sideFirstFactor (p x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1 + t * x) ^ (p - 1)

def sideSecondFactor (p x : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, (1 - t) * (1 + t * x) ^ (p - 2)

private theorem shift_pos {x t : ℝ} (hx : -1 < x) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + t * x := by
  rcases le_total 0 x with hp | hp
  · have h := mul_nonneg ht.1 hp
    linarith only [h]
  · have h := mul_le_mul_of_nonpos_right ht.2 hp
    linarith only [h, hx]

private theorem shift_power_cont {x : ℝ} (hx : -1 < x) (p : ℝ) :
    ContinuousOn (fun t : ℝ => (1 + t * x) ^ p) (Icc (0 : ℝ) 1) := by
  have h : Continuous (fun t : ℝ => 1 + t * x) := by fun_prop
  exact h.continuousOn.rpow_const (fun t ht => Or.inl (shift_pos hx ht).ne')

private theorem shift_power_deriv {p x t : ℝ} (ht : 0 < 1 + t * x) :
    HasDerivAt (fun y : ℝ => (1 + y * x) ^ p) (p * x * (1 + t * x) ^ (p - 1)) t := by
  have h := (Real.hasDerivAt_rpow_const (p := p) (Or.inl ht.ne')).comp t
    (((hasDerivAt_id t).mul_const x).const_add 1)
  convert h using 1
  · rfl
  · ring

theorem side_first_factor_eq {p x : ℝ} (hx : -1 < x) :
    (1 + x) ^ p - 1 = p * x * sideFirstFactor p x := by
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun y : ℝ => (1 + y * x) ^ p)
        (p * x * (1 + t * x) ^ (p - 1)) t := by
    rw [uIcc_of_le zero_le_one] at ht
    exact shift_power_deriv (shift_pos hx ht)
  have hcont := (shift_power_cont hx (p - 1)).const_mul (p*x)
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simpa only [intervalIntegral.integral_const_mul, one_mul, zero_mul, add_zero,
    Real.one_rpow, sideFirstFactor] using h.symm

theorem side_second_factor_eq {p x : ℝ} (hx : -1 < x) :
    powerRemainder p x = (p * (p - 1) / 2) * x ^ 2 * sideSecondFactor p x := by
  let P (t : ℝ) := (1 + t * x) ^ p
  let D (t : ℝ) := p * x * (1 + t * x) ^ (p - 1)
  let F (t : ℝ) := (1 - t) * D t + P t
  let g (t : ℝ) := (1 - t) * (1 + t * x) ^ (p - 2)
  let c := p * (p - 1) * x ^ 2
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt F (c * g t) t := by
    rw [uIcc_of_le zero_le_one] at ht
    have hb := shift_pos hx ht
    have hP : HasDerivAt P (D t) t := shift_power_deriv hb
    have hraw := shift_power_deriv (p := p - 1) hb
    have hD : HasDerivAt D (c * (1 + t*x) ^ (p - 2)) t := by
      have h := hraw.const_mul (p*x)
      simp only [show p - 1 - 1 = p - 2 by ring] at h
      convert h using 1
      dsimp [c]
      ring
    have hL := (hasDerivAt_id t).const_sub (1 : ℝ)
    convert (hL.mul hD).add hP using 1
    · rfl
    · dsimp only [g]
      simp only [id_eq]
      ring
  have hL : Continuous (fun t : ℝ => 1-t) := by fun_prop
  have hG : ContinuousOn g (Icc (0 : ℝ) 1) := hL.continuousOn.mul (shift_power_cont hx _)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hG.const_mul c).intervalIntegrable_of_Icc zero_le_one)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [F, D, P, sub_self, zero_mul, zero_add, one_mul, mul_one, sub_zero, add_zero,
    Real.one_rpow] at h
  change c * (∫ t in (0 : ℝ)..1, g t) = (1 + x) ^ p - (p * x + 1) at h
  unfold powerRemainder sideSecondFactor
  change _ = _ * (2 * ∫ t in (0 : ℝ)..1, g t)
  dsimp only [c] at h
  linear_combination -h

private theorem factor_integral_cmp {x y p q : ℝ} {w : ℝ → ℝ}
    (hx : -1 < x) (hy : -1 < y) (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    (hw₀ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t)
    (hcmp : ∀ t ∈ Icc (0 : ℝ) 1, (1 + t*x) ^ p ≤ (1 + t*y) ^ q) :
    (∫ t in (0 : ℝ)..1, w t * (1 + t*x) ^ p) ≤
      ∫ t in (0 : ℝ)..1, w t * (1 + t*y) ^ q :=
  intervalIntegral.integral_mono_on zero_le_one
    ((hw.mul (shift_power_cont hx _)).intervalIntegrable_of_Icc zero_le_one)
    ((hw.mul (shift_power_cont hy _)).intervalIntegrable_of_Icc zero_le_one)
    (fun t ht => mul_le_mul_of_nonneg_left (hcmp t ht) (hw₀ t ht))

private theorem shift_antitone {x y p : ℝ} (hx : -1 < x) (hxy : x ≤ y) (hp : p ≤ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (1 + t*y) ^ p ≤ (1 + t*x) ^ p :=
  Real.rpow_le_rpow_of_nonpos (shift_pos hx ht)
    (add_le_add_right (mul_le_mul_of_nonneg_left hxy ht.1) 1) hp

theorem side_first_factor_antitone {p x y : ℝ} (hp : p ≤ 1) (hx : -1 < x) (hxy : x ≤ y) :
    sideFirstFactor p y ≤ sideFirstFactor p x := by
  simpa only [sideFirstFactor, one_mul] using
    factor_integral_cmp (w := fun _ => 1) (hx.trans_le hxy) hx continuousOn_const
      (by simp) (fun _ ht => shift_antitone hx hxy (sub_nonpos.mpr hp) ht)

theorem side_first_factor_monotone {p x y : ℝ} (hp : 1 ≤ p) (hx : -1 < x) (hxy : x ≤ y) :
    sideFirstFactor p x ≤ sideFirstFactor p y := by
  simpa only [sideFirstFactor, one_mul] using
    factor_integral_cmp (w := fun _ => 1) hx (hx.trans_le hxy) continuousOn_const
      (by simp) (fun _ ht =>
        Real.rpow_le_rpow (shift_pos hx ht).le
          (add_le_add_right (mul_le_mul_of_nonneg_left hxy ht.1) 1) (sub_nonneg.mpr hp))

theorem side_second_factor_antitone {p x y : ℝ} (hp : p ≤ 2) (hx : -1 < x) (hxy : x ≤ y) :
    sideSecondFactor p y ≤ sideSecondFactor p x := by
  unfold sideSecondFactor
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact factor_integral_cmp (w := fun t => 1-t) (hx.trans_le hxy) hx
    (by fun_prop) (fun _ ht => sub_nonneg.mpr ht.2)
    (fun _ ht => shift_antitone hx hxy (sub_nonpos.mpr hp) ht)

private theorem shift_parameter_mono {x p q t : ℝ} (hx : -1 < x)
    (ht : t ∈ Icc (0 : ℝ) 1) (h : if x ≤ 0 then q ≤ p else p ≤ q) :
    (1 + t * x) ^ p ≤ (1 + t * x) ^ q := by
  by_cases hz : x ≤ 0
  · have hm := mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    exact Real.rpow_le_rpow_of_exponent_ge (shift_pos hx ht) (by linarith only [hm])
      (by simpa only [ite_eq_left hz] using h)
  · have hm := mul_nonneg ht.1 (le_of_lt (lt_of_not_ge hz))
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hm])
      (by simpa only [ite_eq_right hz] using h)

theorem side_first_factor_exponent {x p q : ℝ} (hx : -1 < x)
    (h : if x ≤ 0 then q ≤ p else p ≤ q) :
    sideFirstFactor p x ≤ sideFirstFactor q x := by
  have hb : if x ≤ 0 then q-1 ≤ p-1 else p-1 ≤ q-1 := by
    by_cases hz : x ≤ 0 <;> simpa [hz] using h
  simpa only [sideFirstFactor, one_mul] using
    factor_integral_cmp (w := fun _ => 1) hx hx continuousOn_const
      (by simp) (fun _ ht => shift_parameter_mono hx ht hb)

theorem side_second_factor_exponent {x p q : ℝ} (hx : -1 < x)
    (h : if x ≤ 0 then q ≤ p else p ≤ q) :
    sideSecondFactor p x ≤ sideSecondFactor q x := by
  have hb : if x ≤ 0 then q-2 ≤ p-2 else p-2 ≤ q-2 := by
    by_cases hz : x ≤ 0 <;> simpa [hz] using h
  unfold sideSecondFactor
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact factor_integral_cmp (w := fun t => 1-t) hx hx
    (by fun_prop) (fun _ ht => sub_nonneg.mpr ht.2)
    (fun _ ht => shift_parameter_mono hx ht hb)

theorem side_first_factor_zero (p : ℝ) : sideFirstFactor p 0 = 1 := by
  simp [sideFirstFactor, intervalIntegral.integral_const]

theorem side_second_factor_zero (p : ℝ) : sideSecondFactor p 0 = 1 := by
  simp only [sideSecondFactor, mul_zero, add_zero, Real.one_rpow, mul_one]
  have h₁ : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h₁ h₂, intervalIntegral.integral_const, integral_id]
  norm_num

theorem side_scaled_second_eq {q y ℓ : ℝ} (hy : 0 < y) (hℓ : 0 < y+ℓ) :
    (y + ℓ) ^ q - y ^ q - q * y ^ (q - 1) * ℓ =
      (q * (q - 1) / 2) * y ^ (q - 2) * ℓ ^ 2 * sideSecondFactor q (ℓ / y) := by
  have hx : -1 < ℓ / y := (lt_div_iff₀ hy).2 (by linarith only [hℓ])
  have hshift : y + ℓ = y * (1 + ℓ/y) := by field_simp [hy.ne']
  have h₁ : y ^ (q-1) = y ^ q / y := by rw [Real.rpow_sub hy, Real.rpow_one]
  have h₂ : y ^ (q-2) = y ^ q / y ^ 2 := by rw [Real.rpow_sub hy, Real.rpow_two]
  have hfactor := side_second_factor_eq (p := q) hx
  unfold powerRemainder at hfactor
  rw [div_pow] at hfactor
  conv_lhs => rw [hshift, Real.mul_rpow hy.le (by linarith only [hx])]
  rw [h₁, h₂]
  linear_combination y ^ q * hfactor

end

end HlawkaSchatten.BelowExponent.Vertex
