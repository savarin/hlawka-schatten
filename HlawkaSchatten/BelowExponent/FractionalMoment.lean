/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-! Integrability and scaling of the real kernel used to recover fractional
moments from the positive stable Laplace transform. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set MeasureTheory

noncomputable def fractionalMomentKernel (α β t : ℝ) : ℝ :=
  (1 - Real.exp (-(t ^ α))) * t ^ (-β - 1)

theorem fractionalMomentKernel_pos (α β : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < fractionalMomentKernel α β t := by
  unfold fractionalMomentKernel
  exact mul_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (Real.rpow_pos_of_pos ht _))))
    (Real.rpow_pos_of_pos ht _)

theorem integrable_fractionalMomentKernel {α β : ℝ} (hβ : 0 < β) (hβα : β < α) :
    IntegrableOn (fractionalMomentKernel α β) (Ioi 0) := by
  have hmeas : Measurable (fractionalMomentKernel α β) := by unfold fractionalMomentKernel; fun_prop
  have hnear : IntegrableOn (fractionalMomentKernel α β) (Ioo 0 1) := by
    apply ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).2
      (show -1 < α + (-β-1) by linarith)).mono' hmeas.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (fractionalMomentKernel_pos _ _ ht.1),
      Real.rpow_add ht.1]
    unfold fractionalMomentKernel
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.1.le _)
    linarith [Real.add_one_le_exp (-(t ^ α))]
  have hfar : IntegrableOn (fractionalMomentKernel α β) (Ici 1) := by
    apply Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
    apply (integrableOn_Ioi_rpow_of_lt (show -β-1 < -1 by linarith) zero_lt_one).mono'
      hmeas.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_pos (fractionalMomentKernel_pos _ _ ht₀)]
    unfold fractionalMomentKernel
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht₀.le _) (by linarith [Real.exp_pos (-(t^α))])
  exact (hnear.union hfar).mono_set (by intro t ht; exact lt_or_ge t 1 |>.imp (fun h => ⟨ht,h⟩) id)

theorem integral_fractionalMomentKernel_pos {α β : ℝ} (hβ : 0 < β) (hβα : β < α) :
    0 < ∫ t in Ioi 0, fractionalMomentKernel α β t := by
  have hp (t : ℝ) (ht : t ∈ Ioi 0) := fractionalMomentKernel_pos α β ht
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hp t ht).le)
    (integrable_fractionalMomentKernel hβ hβα)]
  have hs : Function.support (fractionalMomentKernel α β) ∩ Ioi 0 = Ioi 0 :=
    inter_eq_right.mpr (fun t ht => (hp t ht).ne')
  rw [hs]
  simp

theorem integral_scaled_fractionalMomentKernel {α β b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi 0, (1 - Real.exp (-((b * t)^α))) * t^(-β-1)) =
      b^β * ∫ t in Ioi 0, fractionalMomentKernel α β t := by
  have hscale {t : ℝ} (ht : 0 < t) :
      (1 - Real.exp (-((b*t)^α))) * t^(-β-1) =
      b^(β+1) * fractionalMomentKernel α β (b*t) := by
    unfold fractionalMomentKernel
    rw [show -β-1 = -(β+1) by ring]
    simp only [Real.mul_rpow hb.le ht.le, Real.rpow_neg hb.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hb (β+1))]
  calc
    _ = ∫ t in Ioi 0, b^(β+1) * fractionalMomentKernel α β (b*t) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => hscale ht)
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 hb, mul_zero,
        smul_eq_mul, Real.rpow_add hb, Real.rpow_one]
      field_simp

noncomputable def fractionalMomentConstant (α β : ℝ) : ℝ :=
  ∫ t in Ioi 0, fractionalMomentKernel α β t

private theorem scaled_kernel_integral {α β b : ℝ} (hα : 0 < α) (hβ : 0 < β) (hb : 0 ≤ b) :
    (∫ t in Ioi 0, (1 - Real.exp (-((b*t)^α))) * t^(-β-1)) =
      b^β * fractionalMomentConstant α β := by
  rcases hb.eq_or_lt with h | h
  · subst b
    simp [Real.zero_rpow hα.ne', Real.zero_rpow hβ.ne']
  · exact integral_scaled_fractionalMomentKernel h

/-- A nonnegative variable with the indicated Laplace transform has a finite
fractional moment, with a scale-independent positive normalization. -/
theorem fractionalMoment_of_laplace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {α β b : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) (hβα : β < α)
    (hb : 0 ≤ b) (f : Ω → ℝ) (hf : Measurable f) (hf₀ : ∀ y, 0 ≤ f y)
    (hl : ∀ t : ℝ, 0 < t → (∫ y, Real.exp (-t*f y) ∂μ) = Real.exp (-((b*t)^α))) :
    Integrable (fun y => f y ^ β) μ ∧
    (∫ y, f y ^ β ∂μ) = b^β * (fractionalMomentConstant α β / fractionalMomentConstant 1 β) := by
  let K (t : ℝ) (y : Ω) := (1 - Real.exp (-t * f y)) * t ^ (-β-1)
  let G (t : ℝ) := (1 - Real.exp (-((b*t)^α))) * t ^ (-β-1)
  have hα := hβ.trans hβα
  have hC : 0 < fractionalMomentConstant 1 β := integral_fractionalMomentKernel_pos hβ hβ₁
  have hG : (∫ t in Ioi 0, G t) = b^β * fractionalMomentConstant α β :=
    scaled_kernel_integral hα hβ hb
  have hGi : IntegrableOn G (Ioi 0) := by
    rcases hb.eq_or_lt with h | h
    · subst b
      simp [G, Real.zero_rpow hα.ne']
    · by_contra H
      rw [integral_undef H] at hG
      exact (mul_pos (Real.rpow_pos_of_pos h β) (integral_fractionalMomentKernel_pos hβ hβα)).ne hG
  have hKm : Measurable (Function.uncurry K) := by unfold K Function.uncurry; fun_prop
  have hexp (t : ℝ) (ht : 0 < t) : Integrable (fun y => Real.exp (-t*f y)) μ := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hf₀ y))
  have hKi (t : ℝ) (ht : 0 < t) : Integrable (K t) μ :=
    ((integrable_const (1:ℝ)).sub (hexp t ht)).mul_const _
  have hint (t : ℝ) (ht : 0 < t) : (∫ y, K t y ∂μ) = G t := by
    unfold K G
    rw [integral_mul_const, integral_sub (integrable_const _) (hexp t ht), integral_const, hl t ht]
    simp
  have hprod : Integrable (Function.uncurry K) ((volume.restrict (Ioi 0)).prod μ) := by
    refine (integrable_prod_iff hKm.aestronglyMeasurable).2
      ⟨ae_restrict_of_forall_mem measurableSet_Ioi hKi, hGi.congr ?_⟩
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    change G t = ∫ y, ‖K t y‖ ∂μ
    rw [← hint t ht]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      have hn : 0 ≤ K t y := mul_nonneg
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (hf₀ y))))
        (Real.rpow_nonneg ht.le _)
      simp [Real.norm_eq_abs, abs_of_nonneg hn]
  have hfint (y : Ω) : (∫ t in Ioi 0, K t y) = f y ^ β * fractionalMomentConstant 1 β := by
    simpa only [K, Real.rpow_one, neg_mul, mul_comm (f y)] using
      (scaled_kernel_integral (α := 1) zero_lt_one hβ (hf₀ y))
  have hfi := hprod.integral_prod_right
  change Integrable (fun y => ∫ t in Ioi 0, K t y) μ at hfi
  simp_rw [hfint] at hfi
  constructor
  · simpa only [mul_assoc, mul_inv_cancel₀ hC.ne', mul_one] using hfi.mul_const (fractionalMomentConstant 1 β)⁻¹
  · have he := integral_integral_swap hprod
    change (∫ t in Ioi 0, ∫ y, K t y ∂μ) = ∫ y, (∫ t in Ioi 0, K t y) ∂μ at he
    simp_rw [hfint] at he
    rw [setIntegral_congr_fun measurableSet_Ioi hint, hG, integral_mul_const] at he
    rw [← mul_div_assoc]
    exact (eq_div_iff hC.ne').2 he.symm

end HlawkaSchatten.BelowExponent
