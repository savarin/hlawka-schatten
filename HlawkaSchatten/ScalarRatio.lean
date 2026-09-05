/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Topology.Compactification.OnePoint.Basic
import HlawkaSchatten.ScalarBregman

/-!
# The scalar Bregman--Mazur ratio

This file starts the compact scalar-reduction layer of the Schatten Hlawka
argument.  The raw quotient has a removable singularity at `t = 1`; the
regularized version installs its second-order limiting value.
-/

namespace HlawkaSchatten

open Filter Set
open scoped OnePoint Topology

/-- The Bregman-to-Mazur ratio after normalizing the second scalar to one. -/
noncomputable def scalarRatio (p t : ℝ) : ℝ :=
  scalarBregman p t 1 / (scalarMazur p t - 1) ^ 2

/-- The scalar ratio with its removable value installed at `t = 1`. -/
noncomputable def regularizedScalarRatio (p t : ℝ) : ℝ :=
  if t = 1 then 2 * (p - 1) / p ^ 2 else scalarRatio p t

/-- Explicit formula (1) from the audited proof source. -/
theorem scalarRatio_eq_explicit {p : ℝ} (hp : p ≠ 0) (t : ℝ) :
    scalarRatio p t =
      (|t| ^ p - p * t + p - 1) /
        (p * (signedPower (p / 2) t - 1) ^ 2) := by
  unfold scalarRatio scalarBregman powerPotential powerGradient scalarMazur
  simp
  field_simp [hp]
  ring

private noncomputable def positiveRatioNumerator (p t : ℝ) : ℝ :=
  t ^ p - p * t + (p - 1)

private noncomputable def positiveRatioDenominator (p t : ℝ) : ℝ :=
  p * (t ^ (p / 2) - 1) ^ 2

private noncomputable def positiveRatioNumeratorDeriv (p t : ℝ) : ℝ :=
  p * t ^ (p - 1) - p

private noncomputable def positiveRatioDenominatorDeriv (p t : ℝ) : ℝ :=
  p ^ 2 * (t ^ (p / 2) - 1) * t ^ (p / 2 - 1)

private noncomputable def positiveRatioNumeratorDeriv2 (p t : ℝ) : ℝ :=
  p * (p - 1) * t ^ (p - 2)

private noncomputable def positiveRatioDenominatorDeriv2 (p t : ℝ) : ℝ :=
  p ^ 2 * ((p / 2) * t ^ (p / 2 - 1) * t ^ (p / 2 - 1) +
    (t ^ (p / 2) - 1) * (p / 2 - 1) * t ^ (p / 2 - 2))

private noncomputable def invertedPositiveRatio (p s : ℝ) : ℝ :=
  (1 - p * s ^ (p - 1) + (p - 1) * s ^ p) /
    (p * (1 - s ^ (p / 2)) ^ 2)

private noncomputable def invertedNegativeRatio (p s : ℝ) : ℝ :=
  (1 + p * s ^ (p - 1) + (p - 1) * s ^ p) /
    (p * (1 + s ^ (p / 2)) ^ 2)

private theorem scalarRatio_eq_invertedPositiveRatio {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) :
    scalarRatio p t = invertedPositiveRatio p t⁻¹ := by
  rw [scalarRatio_eq_explicit hp.ne']
  simp only [abs_of_pos ht, signedPower, sign_pos ht, SignType.coe_one, one_mul,
    invertedPositiveRatio, Real.inv_rpow ht.le]
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hthalf : 0 < t ^ (p / 2) := Real.rpow_pos_of_pos ht (p / 2)
  have hsq : (t ^ (p / 2)) ^ 2 = t ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hsq' : (t ^ (p * (1 / 2))) ^ 2 = t ^ p := by
    convert hsq using 1; ring
  have hprod : t * t ^ (-1 + p) = t ^ p := by
    calc
      t * t ^ (-1 + p) = t ^ (1 : ℝ) * t ^ (-1 + p) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-1 + p)) := (Real.rpow_add ht _ _).symm
      _ = t ^ p := by ring_nf
  have hprod' : t * t ^ (p - 1) = t ^ p := by
    convert hprod using 1; ring
  field_simp [hp.ne', ht.ne', htp.ne', hthalf.ne']
  rw [hsq]
  congr 1
  ring_nf
  linear_combination -(t ^ p * p) * hprod

private theorem scalarRatio_neg_eq_invertedNegativeRatio {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) :
    scalarRatio p (-t) = invertedNegativeRatio p t⁻¹ := by
  rw [scalarRatio_eq_explicit hp.ne']
  rw [signedPower_neg]
  rw [show signedPower (p / 2) t = t ^ (p / 2) by
    simp [signedPower, sign_pos ht, abs_of_pos ht]]
  simp only [abs_neg, abs_of_pos ht, invertedNegativeRatio, Real.inv_rpow ht.le,
    mul_neg, sub_neg_eq_add]
  rw [show (-t ^ (p / 2) - 1) ^ 2 = (t ^ (p / 2) + 1) ^ 2 by ring]
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hthalf : 0 < t ^ (p / 2) := Real.rpow_pos_of_pos ht (p / 2)
  have hsq : (t ^ (p / 2)) ^ 2 = t ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hprod : t * t ^ (-1 + p) = t ^ p := by
    calc
      t * t ^ (-1 + p) = t ^ (1 : ℝ) * t ^ (-1 + p) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + (-1 + p)) := (Real.rpow_add ht _ _).symm
      _ = t ^ p := by ring_nf
  field_simp [hp.ne', ht.ne', htp.ne', hthalf.ne']
  rw [hsq]
  ring_nf
  linear_combination (t ^ p * p) * hprod

private theorem tendsto_invertedPositiveRatio_zero {p : ℝ} (hp : 1 < p) :
    Tendsto (invertedPositiveRatio p) (𝓝 0) (𝓝 (1 / p)) := by
  have hcont : ContinuousAt (invertedPositiveRatio p) 0 := by
    unfold invertedPositiveRatio
    have hr1 : ContinuousAt (fun s : ℝ ↦ s ^ (p - 1)) 0 :=
      continuousAt_id.rpow_const (Or.inr (sub_nonneg.mpr hp.le))
    have hrp : ContinuousAt (fun s : ℝ ↦ s ^ p) 0 :=
      continuousAt_id.rpow_const (Or.inr (zero_lt_one.trans hp).le)
    have hrh : ContinuousAt (fun s : ℝ ↦ s ^ (p / 2)) 0 :=
      continuousAt_id.rpow_const (Or.inr (half_pos (zero_lt_one.trans hp)).le)
    have hnum : ContinuousAt
        (fun s : ℝ ↦ 1 - p * s ^ (p - 1) + (p - 1) * s ^ p) 0 :=
      (continuousAt_const.sub (continuousAt_const.mul hr1)).add
        (continuousAt_const.mul hrp)
    have hden : ContinuousAt (fun s : ℝ ↦ p * (1 - s ^ (p / 2)) ^ 2) 0 :=
      continuousAt_const.mul ((continuousAt_const.sub hrh).pow 2)
    apply hnum.div hden
    simp [Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne',
      (zero_lt_one.trans hp).ne']
  have hval : invertedPositiveRatio p 0 = 1 / p := by
    unfold invertedPositiveRatio
    rw [Real.zero_rpow (sub_pos.mpr hp).ne', Real.zero_rpow (zero_lt_one.trans hp).ne',
      Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne']
    ring
  rw [← hval]
  exact hcont.tendsto

private theorem tendsto_invertedNegativeRatio_zero {p : ℝ} (hp : 1 < p) :
    Tendsto (invertedNegativeRatio p) (𝓝 0) (𝓝 (1 / p)) := by
  have hcont : ContinuousAt (invertedNegativeRatio p) 0 := by
    unfold invertedNegativeRatio
    have hr1 : ContinuousAt (fun s : ℝ ↦ s ^ (p - 1)) 0 :=
      continuousAt_id.rpow_const (Or.inr (sub_nonneg.mpr hp.le))
    have hrp : ContinuousAt (fun s : ℝ ↦ s ^ p) 0 :=
      continuousAt_id.rpow_const (Or.inr (zero_lt_one.trans hp).le)
    have hrh : ContinuousAt (fun s : ℝ ↦ s ^ (p / 2)) 0 :=
      continuousAt_id.rpow_const (Or.inr (half_pos (zero_lt_one.trans hp)).le)
    have hnum : ContinuousAt
        (fun s : ℝ ↦ 1 + p * s ^ (p - 1) + (p - 1) * s ^ p) 0 :=
      (continuousAt_const.add (continuousAt_const.mul hr1)).add
        (continuousAt_const.mul hrp)
    have hden : ContinuousAt (fun s : ℝ ↦ p * (1 + s ^ (p / 2)) ^ 2) 0 :=
      continuousAt_const.mul ((continuousAt_const.add hrh).pow 2)
    apply hnum.div hden
    simp [Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne',
      (zero_lt_one.trans hp).ne']
  have hval : invertedNegativeRatio p 0 = 1 / p := by
    unfold invertedNegativeRatio
    rw [Real.zero_rpow (sub_pos.mpr hp).ne', Real.zero_rpow (zero_lt_one.trans hp).ne',
      Real.zero_rpow (half_pos (zero_lt_one.trans hp)).ne']
    ring
  rw [← hval]
  exact hcont.tendsto

/-- The positive infinite endpoint of the raw scalar ratio is `1 / p`. -/
theorem tendsto_scalarRatio_atTop {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) atTop (𝓝 (1 / p)) := by
  have hlim := (tendsto_invertedPositiveRatio_zero hp).comp tendsto_inv_atTop_zero
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (scalarRatio_eq_invertedPositiveRatio (zero_lt_one.trans hp) ht).symm

/-- The regularization does not change the positive infinite endpoint. -/
theorem tendsto_regularizedScalarRatio_atTop {p : ℝ} (hp : 1 < p) :
    Tendsto (regularizedScalarRatio p) atTop (𝓝 (1 / p)) := by
  apply (tendsto_scalarRatio_atTop hp).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  simp [regularizedScalarRatio, ht.ne']

/-- The negative infinite endpoint of the raw scalar ratio is also `1 / p`. -/
theorem tendsto_scalarRatio_atBot {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) atBot (𝓝 (1 / p)) := by
  have hinv : Tendsto (fun t : ℝ ↦ (-t)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop
  have hlim := (tendsto_invertedNegativeRatio_zero hp).comp hinv
  apply hlim.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have hpos : 0 < -t := neg_pos.mpr ht
  simpa using (scalarRatio_neg_eq_invertedNegativeRatio (zero_lt_one.trans hp) hpos).symm

/-- The regularization does not change the negative infinite endpoint. -/
theorem tendsto_regularizedScalarRatio_atBot {p : ℝ} (hp : 1 < p) :
    Tendsto (regularizedScalarRatio p) atBot (𝓝 (1 / p)) := by
  apply (tendsto_scalarRatio_atBot hp).congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have ht1 : t ≠ 1 := by linarith
  simp [regularizedScalarRatio, ht1]

private theorem hasDerivAt_positiveRatioNumerator (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioNumerator p) (positiveRatioNumeratorDeriv p t) t := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ p) (p * t ^ (p - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht)
  have hlin : HasDerivAt (fun x : ℝ ↦ p * x) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  unfold positiveRatioNumerator positiveRatioNumeratorDeriv
  convert! (hpow.sub hlin).add_const (p - 1) using 1

private theorem hasDerivAt_positiveRatioDenominator (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioDenominator p) (positiveRatioDenominatorDeriv p t) t := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ (p / 2))
      ((p / 2) * t ^ (p / 2 - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht)
  unfold positiveRatioDenominator positiveRatioDenominatorDeriv
  convert! ((hpow.sub_const 1).pow 2).const_mul p using 1; (norm_num; ring)

private theorem hasDerivAt_positiveRatioNumeratorDeriv (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioNumeratorDeriv p) (positiveRatioNumeratorDeriv2 p t) t := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ (p - 1))
      ((p - 1) * t ^ (p - 2)) t := by
    convert Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht) using 1; ring
  unfold positiveRatioNumeratorDeriv positiveRatioNumeratorDeriv2
  convert! hpow.const_mul p |>.sub_const p using 1; ring

private theorem hasDerivAt_positiveRatioDenominatorDeriv (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioDenominatorDeriv p)
      (positiveRatioDenominatorDeriv2 p t) t := by
  unfold positiveRatioDenominatorDeriv positiveRatioDenominatorDeriv2
  have h₁ := (Real.hasDerivAt_rpow_const (p := p / 2) (Or.inl ht)).sub_const 1
  have h₂ := Real.hasDerivAt_rpow_const (p := p / 2 - 1) (Or.inl ht)
  have hfun :
      (fun x : ℝ ↦ p ^ 2 * (x ^ (p / 2) - 1) * x ^ (p / 2 - 1)) =
        fun x ↦ p ^ 2 * ((x ^ (p / 2) - 1) * x ^ (p / 2 - 1)) := by
    funext x
    ring
  rw [hfun]
  convert! (h₁.mul h₂).const_mul (p ^ 2) using 1; ring

private theorem positiveRatioDenominatorDeriv_ne_zero {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) (ht1 : t ≠ 1) :
    positiveRatioDenominatorDeriv p t ≠ 0 := by
  unfold positiveRatioDenominatorDeriv
  have hpow : t ^ (p / 2) ≠ 1 := by
    intro heq
    have heq' : t ^ (p / 2) = (1 : ℝ) ^ (p / 2) := by simpa using heq
    exact ht1 ((Real.strictMonoOn_rpow_Ici_of_exponent_pos (half_pos hp)).injOn
      (show t ∈ Set.Ici 0 from ht.le) (by simp) heq')
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hp.ne') (sub_ne_zero.mpr hpow))
    (Real.rpow_pos_of_pos ht _).ne'

/-- The raw quotient tends to the installed second-order value at `t = 1`. -/
theorem tendsto_scalarRatio_one {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hN2cont : ContinuousAt (positiveRatioNumeratorDeriv2 p) 1 := by
    unfold positiveRatioNumeratorDeriv2
    fun_prop (disch := norm_num)
  have hD2cont : ContinuousAt (positiveRatioDenominatorDeriv2 p) 1 := by
    unfold positiveRatioDenominatorDeriv2
    fun_prop (disch := norm_num)
  have hD2pos : 0 < positiveRatioDenominatorDeriv2 p 1 := by
    unfold positiveRatioDenominatorDeriv2
    norm_num
    positivity
  have hsecond : Tendsto
      (fun t ↦ positiveRatioNumeratorDeriv2 p t / positiveRatioDenominatorDeriv2 p t)
      (𝓝 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
    have hcont := hN2cont.div hD2cont hD2pos.ne'
    have hval : positiveRatioNumeratorDeriv2 p 1 /
        positiveRatioDenominatorDeriv2 p 1 = 2 * (p - 1) / p ^ 2 := by
      unfold positiveRatioNumeratorDeriv2 positiveRatioDenominatorDeriv2
      norm_num
      field_simp [hp0]
    rw [← hval]
    exact hcont.tendsto
  have hN1zero : Tendsto (positiveRatioNumeratorDeriv p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioNumeratorDeriv p one_ne_zero).continuousAt
    have hval : positiveRatioNumeratorDeriv p 1 = 0 := by
      simp [positiveRatioNumeratorDeriv]
    rw [← hval]
    exact hcont.tendsto
  have hD1zero : Tendsto (positiveRatioDenominatorDeriv p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioDenominatorDeriv p one_ne_zero).continuousAt
    have hval : positiveRatioDenominatorDeriv p 1 = 0 := by
      simp [positiveRatioDenominatorDeriv]
    rw [← hval]
    exact hcont.tendsto
  have hfirst : Tendsto
      (fun t ↦ positiveRatioNumeratorDeriv p t / positiveRatioDenominatorDeriv p t)
      (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioNumeratorDeriv p ht).filter_mono nhdsWithin_le_nhds
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioDenominatorDeriv p ht).filter_mono nhdsWithin_le_nhds
    · exact (hD2cont.eventually_ne hD2pos.ne').filter_mono nhdsWithin_le_nhds
    · exact tendsto_nhdsWithin_of_tendsto_nhds hN1zero
    · exact tendsto_nhdsWithin_of_tendsto_nhds hD1zero
    · exact tendsto_nhdsWithin_of_tendsto_nhds hsecond
  have hNzero : Tendsto (positiveRatioNumerator p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioNumerator p one_ne_zero).continuousAt
    have hval : positiveRatioNumerator p 1 = 0 := by simp [positiveRatioNumerator]
    rw [← hval]
    exact hcont.tendsto
  have hDzero : Tendsto (positiveRatioDenominator p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioDenominator p one_ne_zero).continuousAt
    have hval : positiveRatioDenominator p 1 = 0 := by simp [positiveRatioDenominator]
    rw [← hval]
    exact hcont.tendsto
  have hraw : Tendsto
      (fun t ↦ positiveRatioNumerator p t / positiveRatioDenominator p t)
      (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioNumerator p ht).filter_mono nhdsWithin_le_nhds
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioDenominator p ht).filter_mono nhdsWithin_le_nhds
    · have hpos : ∀ᶠ t : ℝ in 𝓝[≠] 1, 0 < t :=
        (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hpos] with t ht1 ht
      exact positiveRatioDenominatorDeriv_ne_zero (zero_lt_one.trans hp) ht (by simpa using ht1)
    · exact tendsto_nhdsWithin_of_tendsto_nhds hNzero
    · exact tendsto_nhdsWithin_of_tendsto_nhds hDzero
    · exact hfirst
  apply hraw.congr'
  have hpos : ∀ᶠ t : ℝ in 𝓝[≠] 1, 0 < t :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos] with t ht
  rw [scalarRatio_eq_explicit hp0]
  simp only [abs_of_pos ht, signedPower, sign_pos ht, SignType.coe_one, one_mul]
  unfold positiveRatioNumerator positiveRatioDenominator
  ring

/-- The regularized scalar ratio is continuous at its removable point. -/
theorem continuousAt_regularizedScalarRatio_one {p : ℝ} (hp : 1 < p) :
    ContinuousAt (regularizedScalarRatio p) 1 := by
  have hfun : regularizedScalarRatio p = Function.update (scalarRatio p) 1
      (2 * (p - 1) / p ^ 2) := by
    funext t
    by_cases ht : t = 1
    · subst t
      simp [regularizedScalarRatio]
    · simp [regularizedScalarRatio, ht]
  rw [hfun]
  exact continuousAt_update_same.mpr (tendsto_scalarRatio_one hp)

@[simp]
theorem regularizedScalarRatio_one (p : ℝ) :
    regularizedScalarRatio p 1 = 2 * (p - 1) / p ^ 2 := by
  simp [regularizedScalarRatio]

theorem regularizedScalarRatio_of_ne (p : ℝ) {t : ℝ} (ht : t ≠ 1) :
    regularizedScalarRatio p t = scalarRatio p t := by
  simp [regularizedScalarRatio, ht]

/-- The Mazur denominator vanishes only at the removable point. -/
theorem scalarMazur_eq_one_iff {p : ℝ} (hp : 0 < p) (t : ℝ) :
    scalarMazur p t = 1 ↔ t = 1 := by
  have hmono : StrictMono (signedPower (p / 2)) :=
    strictMono_signedPower (half_pos hp)
  constructor
  · intro h
    apply hmono.injective
    simpa [scalarMazur, signedPower] using h
  · rintro rfl
    simp [scalarMazur, signedPower]

theorem scalarMazur_sub_one_ne_zero {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 1) :
    scalarMazur p t - 1 ≠ 0 := by
  rw [sub_ne_zero]
  exact (scalarMazur_eq_one_iff hp t).not.mpr ht

/-- Away from the removable point, the scalar ratio is strictly positive. -/
theorem scalarRatio_pos {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : t ≠ 1) :
    0 < scalarRatio p t := by
  exact div_pos (scalarBregman_pos hp ht)
    (sq_pos_of_ne_zero (scalarMazur_sub_one_ne_zero (zero_lt_one.trans hp) ht))

/-- The regularized ratio is positive at every finite real parameter. -/
theorem regularizedScalarRatio_pos {p : ℝ} (hp : 1 < p) (t : ℝ) :
    0 < regularizedScalarRatio p t := by
  by_cases ht : t = 1
  · rw [ht, regularizedScalarRatio_one]
    exact div_pos (mul_pos zero_lt_two (sub_pos.mpr hp)) (sq_pos_of_pos (zero_lt_one.trans hp))
  · rw [regularizedScalarRatio_of_ne p ht]
    exact scalarRatio_pos hp ht

/-- The regularized scalar ratio is continuous on the finite real line. -/
theorem continuous_regularizedScalarRatio {p : ℝ} (hp : 1 < p) :
    Continuous (regularizedScalarRatio p) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 1
  · subst t
    exact continuousAt_regularizedScalarRatio_one hp
  · have hratio : ContinuousAt (scalarRatio p) t := by
      unfold scalarRatio
      have hmazur : ContinuousAt (scalarMazur p) t := by
        exact (continuous_signedPower (half_pos (zero_lt_one.trans hp))).continuousAt
      have hbregman : ContinuousAt (fun x : ℝ ↦ scalarBregman p x 1) t := by
        unfold scalarBregman powerPotential
        fun_prop (disch := positivity)
      exact hbregman.div ((hmazur.sub continuousAt_const).pow 2)
        (pow_ne_zero 2 (scalarMazur_sub_one_ne_zero (zero_lt_one.trans hp) ht))
    apply hratio.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht] with x hx
    exact regularizedScalarRatio_of_ne p hx

/-- At zero the ratio is the finite endpoint value `(p - 1) / p`. -/
theorem regularizedScalarRatio_zero {p : ℝ} (hp : 1 < p) :
    regularizedScalarRatio p 0 = (p - 1) / p := by
  rw [regularizedScalarRatio_of_ne p zero_ne_one]
  rw [scalarRatio]
  simp only [scalarMazur_zero]
  norm_num
  unfold scalarBregman powerPotential powerGradient
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  simp [hp0]
  field_simp [hp0]
  ring

/-- At the Hilbert exponent the regularized scalar ratio is constantly `1 / 2`. -/
theorem regularizedScalarRatio_two (t : ℝ) :
    regularizedScalarRatio 2 t = 1 / 2 := by
  by_cases ht : t = 1
  · subst t
    norm_num
  · rw [regularizedScalarRatio_of_ne 2 ht]
    unfold scalarRatio
    rw [scalarBregman_eq_mazur_sq_at_two]
    have hden : (scalarMazur 2 t - scalarMazur 2 1) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      rw [sub_ne_zero]
      simpa using ht
    simp only [scalarMazur_two] at hden ⊢
    field_simp [hden]

/-- Normalization of a scalar Bregman divergence by a nonzero second argument. -/
theorem scalarBregman_normalize (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    scalarBregman p a b = |b| ^ p * scalarBregman p (a / b) 1 := by
  have hab : b * (a / b) = a := by field_simp
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hscale := scalarBregman_mul_of_pos p ((-a) / (-b)) 1 (neg_pos.mpr hbneg)
    simpa [abs_of_neg hbneg, hb, hab] using hscale
  · have hscale := scalarBregman_mul_of_pos p (a / b) 1 hbpos
    simpa [abs_of_pos hbpos, hb, hab] using hscale

/-- The squared Mazur distance has the same degree-`p` normalization. -/
theorem scalarMazur_distance_sq_normalize (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (scalarMazur p a - scalarMazur p b) ^ 2 =
      |b| ^ p * (scalarMazur p (a / b) - 1) ^ 2 := by
  have hab : b * (a / b) = a := by field_simp
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hA : scalarMazur p (-a) =
        (-b) ^ (p / 2) * scalarMazur p (a / b) := by
      simpa [hb, hab] using scalarMazur_mul_of_pos p ((-a) / (-b)) (neg_pos.mpr hbneg)
    have hB : scalarMazur p (-b) = (-b) ^ (p / 2) := by
      simpa [scalarMazur, signedPower] using
        scalarMazur_mul_of_pos p 1 (neg_pos.mpr hbneg)
    have hpow : ((-b) ^ (p / 2)) ^ 2 = (-b) ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (neg_nonneg.mpr hbneg.le)]
      congr 1
      ring
    rw [abs_of_neg hbneg]
    calc
      (scalarMazur p a - scalarMazur p b) ^ 2 =
          (scalarMazur p (-a) - scalarMazur p (-b)) ^ 2 := by simp; ring
      _ = (-b) ^ p * (scalarMazur p (a / b) - 1) ^ 2 := by
        rw [hA, hB, ← hpow]
        ring
  · have hA : scalarMazur p a = b ^ (p / 2) * scalarMazur p (a / b) := by
      simpa [hab] using scalarMazur_mul_of_pos p (a / b) hbpos
    have hB : scalarMazur p b = b ^ (p / 2) := by
      simpa [scalarMazur, signedPower] using scalarMazur_mul_of_pos p 1 hbpos
    have hpow : (b ^ (p / 2)) ^ 2 = b ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbpos.le]
      congr 1
      ring
    rw [abs_of_pos hbpos, hA, hB, ← hpow]
    ring

/-- The normalized scalar quotient is exactly `scalarRatio (a / b)`. -/
theorem scalarBregman_div_mazur_sq_eq_scalarRatio (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    scalarBregman p a b / (scalarMazur p a - scalarMazur p b) ^ 2 =
      scalarRatio p (a / b) := by
  rw [scalarBregman_normalize p a hb, scalarMazur_distance_sq_normalize p a hb]
  unfold scalarRatio
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos (abs_pos.mpr hb) p).ne'

/-- The scalar ratio on the one-point compactification of the real line. -/
noncomputable def compactifiedScalarRatio (p : ℝ) : OnePoint ℝ → ℝ :=
  fun x ↦ x.elim (1 / p) (regularizedScalarRatio p)

@[simp]
theorem compactifiedScalarRatio_infty (p : ℝ) :
    compactifiedScalarRatio p ∞ = 1 / p := rfl

@[simp]
theorem compactifiedScalarRatio_coe (p t : ℝ) :
    compactifiedScalarRatio p (t : OnePoint ℝ) = regularizedScalarRatio p t := rfl

/-- Both infinite directions glue to the same value, so the compactified ratio is continuous. -/
theorem continuous_compactifiedScalarRatio {p : ℝ} (hp : 1 < p) :
    Continuous (compactifiedScalarRatio p) := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Tendsto (regularizedScalarRatio p) (coclosedCompact ℝ) (𝓝 (1 / p))
    rw [Filter.coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop]
    exact (tendsto_regularizedScalarRatio_atBot hp).sup
      (tendsto_regularizedScalarRatio_atTop hp)
  · exact continuous_regularizedScalarRatio hp

theorem compactifiedScalarRatio_pos {p : ℝ} (hp : 1 < p) (x : OnePoint ℝ) :
    0 < compactifiedScalarRatio p x := by
  induction x using OnePoint.rec with
  | infty =>
      simp only [compactifiedScalarRatio_infty]
      exact div_pos zero_lt_one (zero_lt_one.trans hp)
  | coe t => simpa using regularizedScalarRatio_pos hp t

/-- Compactness produces finite positive global lower and upper scalar constants. -/
theorem exists_compactifiedScalarRatio_bounds {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
        compactifiedScalarRatio p x ≤ M := by
  have hcont := continuous_compactifiedScalarRatio hp
  obtain ⟨m, hm0, hm⟩ := isCompact_univ.exists_forall_le' hcont.continuousOn
    (fun x _ ↦ compactifiedScalarRatio_pos hp x)
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  refine ⟨m, compactifiedScalarRatio p x, hm0, hm x (Set.mem_univ x), ?_⟩
  intro y
  exact ⟨hm y (Set.mem_univ y), hx (Set.mem_univ y)⟩

/-- Squaring the scalar Mazur map recovers the degree-`p` absolute power. -/
theorem scalarMazur_sq {p : ℝ} (hp : 0 < p) (a : ℝ) :
    (scalarMazur p a) ^ 2 = |a| ^ p := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow hp.ne']
  · have habs : 0 < |a| := abs_pos.mpr ha
    have hpow : (|a| ^ (p / 2)) ^ 2 = |a| ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul habs.le]
      congr 1
      ring
    rcases lt_or_gt_of_ne ha with haneg | hapos
    · simp [scalarMazur, signedPower, sign_neg haneg, hpow]
    · simp [scalarMazur, signedPower, sign_pos hapos, hpow]

theorem scalarBregman_zero_right {p : ℝ} (hp : 0 < p) (a : ℝ) :
    scalarBregman p a 0 = (1 / p) * (scalarMazur p a - scalarMazur p 0) ^ 2 := by
  rw [scalarMazur_zero, sub_zero, scalarMazur_sq hp]
  unfold scalarBregman powerPotential
  simp [hp.ne']
  ring

/-- A global compactified ratio bound is exactly a two-sided scalar comparison. -/
theorem scalarBregman_two_sided_of_compactified_bounds {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M) (a b : ℝ) :
    m * (scalarMazur p a - scalarMazur p b) ^ 2 ≤ scalarBregman p a b ∧
      scalarBregman p a b ≤ M * (scalarMazur p a - scalarMazur p b) ^ 2 := by
  by_cases hab : a = b
  · subst b
    simp
  by_cases hb : b = 0
  · subst b
    rw [scalarBregman_zero_right (zero_lt_one.trans hp)]
    have hendpoint := hbound (∞ : OnePoint ℝ)
    simp only [compactifiedScalarRatio_infty] at hendpoint
    have hsq : 0 ≤ (scalarMazur p a - scalarMazur p 0) ^ 2 := sq_nonneg _
    constructor <;> nlinarith
  · have ht : a / b ≠ 1 := by
      intro heq
      apply hab
      field_simp [hb] at heq
      linarith
    have hdist : 0 < (scalarMazur p a - scalarMazur p b) ^ 2 := by
      apply sq_pos_of_ne_zero
      rw [sub_ne_zero]
      exact (strictMono_signedPower
        (half_pos (zero_lt_one.trans hp))).injective.ne hab
    have hfactor : scalarBregman p a b =
        scalarRatio p (a / b) * (scalarMazur p a - scalarMazur p b) ^ 2 := by
      apply (div_eq_iff hdist.ne').mp
      exact scalarBregman_div_mazur_sq_eq_scalarRatio p a hb
    have hratio := hbound (a / b : OnePoint ℝ)
    rw [compactifiedScalarRatio_coe, regularizedScalarRatio_of_ne p ht] at hratio
    rw [hfactor]
    constructor <;> nlinarith

/-- Positive finite scalar comparison constants exist for every `1 < p`. -/
theorem exists_scalarBregman_two_sided {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ a b : ℝ,
      m * (scalarMazur p a - scalarMazur p b) ^ 2 ≤ scalarBregman p a b ∧
        scalarBregman p a b ≤ M * (scalarMazur p a - scalarMazur p b) ^ 2 := by
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_compactifiedScalarRatio_bounds hp
  exact ⟨m, M, hm, hmM, scalarBregman_two_sided_of_compactified_bounds hp hbound⟩

end HlawkaSchatten
