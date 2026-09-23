/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.ScalarEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit uniform estimates above the cutoff

Rational logarithm bounds separate the cyclic witness and scalar envelope
at the common intermediate value `939 * p / 2000`.
-/

namespace HlawkaSchatten.DiagonalConstruction

/-- Rational bounds on `log 2`. -/
theorem log_two_bounds : (693 : ℝ) / 1000 < Real.log 2 ∧ Real.log 2 < 347 / 500 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

/-- The tangent bound `log(p) ≤ p/256 + 23/5` for `p ≥ 256`. -/
theorem log_le_cutoff_tangent {p : ℝ} (hp : 256 ≤ p) :
    Real.log p ≤ p / 256 + 23 / 5 := by
  have hp0 : 0 < p := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < p / 256 by positivity)
  rw [Real.log_div hp0.ne' (by norm_num)] at h
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 8
    norm_num at hh
    exact hh
  rw [h256] at h
  linarith [log_two_bounds.2]

/-- Bounds on `1/p` for `p ≥ 256`. -/
theorem cutoff_inverse_bounds {p : ℝ} (hp : 256 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1 / 256 := by
  have hp0 : 0 < p := by linarith
  exact ⟨inv_pos.mpr hp0, by simpa using (one_div_le_one_div_of_le (by norm_num) hp)⟩

/-- Bounds on `log(p)/p` for `p ≥ 256`. -/
theorem log_mul_inv_bounds {p : ℝ} (hp : 256 ≤ p) :
    0 ≤ Real.log p * p⁻¹ ∧ Real.log p * p⁻¹ ≤ 7 / 320 := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  have hl := Real.log_nonneg (show 1 ≤ p by linarith)
  have hm := mul_le_mul_of_nonneg_right (log_le_cutoff_tangent hp) hi.1.le
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  constructor
  · positivity
  · nlinarith

/-- The explicit cyclic parameter, written using `exp` for its estimates. -/
noncomputable def constructionParameter (p : ℝ) : ℝ := Real.exp (-(Real.log p * p⁻¹))

/-- The construction parameter lies in `[1/2, 1]` for `p ≥ 256`. -/
theorem constructionParameter_bounds {p : ℝ} (hp : 256 ≤ p) :
    1 / 2 ≤ constructionParameter p ∧ constructionParameter p ≤ 1 := by
  have hl := log_mul_inv_bounds hp
  have he := Real.add_one_le_exp (-(Real.log p * p⁻¹))
  constructor
  · dsimp [constructionParameter]
    linarith
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)

/-- Raising the construction parameter to `p`. -/
theorem constructionParameter_power {p : ℝ} (hp : 0 < p) :
    constructionParameter p ^ p = p⁻¹ := by
  rw [constructionParameter, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -(Real.log p * p⁻¹) * p = -Real.log p := by field_simp
  rw [he, Real.exp_neg, Real.exp_log hp]

/-- The construction parameter satisfies `1 - t ≤ log(p)/p`. -/
theorem constructionParameter_deficit {p : ℝ} :
    1 - constructionParameter p ≤ Real.log p * p⁻¹ := by
  have h := Real.add_one_le_exp (-(Real.log p * p⁻¹))
  dsimp [constructionParameter]
  linarith

/-- The bound `3^(1/p) ≤ 1 + 2/p` for `p ≥ 1`. -/
theorem three_root_le {p : ℝ} (hp : 1 ≤ p) :
    (3 : ℝ) ^ (1 / p) ≤ 1 + 2 * p⁻¹ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hi : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have h := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ 2 * p⁻¹ by linarith) hp
  have hpow : ((3 : ℝ) ^ (1 / p)) ^ p = 3 := by
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hp0.ne', Real.rpow_one]
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) hp0).mp
  rw [hpow]
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  nlinarith

/-- `cyclicB` is at least 2 for all `t`. -/
theorem cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (cyclicB_nonneg p t) hp).mp
  rw [cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith

/-- The cyclic singleton norm at the witness exceeds 1. -/
theorem cyclicA_witness_ge_one {p : ℝ} (hp : 256 ≤ p) :
    1 ≤ cyclicA p (constructionParameter p) := by
  have hp0 : 0 < p := by linarith
  rw [cyclicA, constructionParameter_power hp0]
  apply Real.one_le_rpow
  · have h := (cutoff_inverse_bounds hp).1
    linarith
  · positivity

/-- `cyclicA - 1` at the witness is bounded above. -/
theorem cyclicA_witness_sub_one_le {p : ℝ} (hp : 256 ≤ p) :
    cyclicA p (constructionParameter p) - 1 ≤ (347 / 500 : ℝ) * p⁻¹ + (p⁻¹) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  let a := Real.log (2 + p⁻¹)
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith [hi.1])
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (2 + p⁻¹) / 2 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hlog
  have ha : a ≤ 347 / 500 + p⁻¹ / 2 := by dsimp [a]; linarith [log_two_bounds.2]
  have ha7 : a ≤ 7 / 10 := by linarith [hi.2]
  have haSq : a ^ 2 ≤ 1 / 2 := by nlinarith
  have har : 0 ≤ a * p⁻¹ := mul_nonneg ha0 hi.1.le
  have har1 : a * p⁻¹ ≤ 1 := by nlinarith [hi.2]
  have he := Real.norm_exp_sub_one_sub_id_le (x := a * p⁻¹)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg har] using har1)
  have he' := (le_abs_self (Real.exp (a * p⁻¹) - 1 - a * p⁻¹)).trans he
  simp only [Real.norm_eq_abs, abs_of_nonneg har] at he'
  have hm := mul_le_mul_of_nonneg_right ha hi.1.le
  have hs := mul_le_mul_of_nonneg_right haSq (sq_nonneg p⁻¹)
  have hA : cyclicA p (constructionParameter p) = Real.exp (a * p⁻¹) := by
    rw [cyclicA, constructionParameter_power hp0, add_comm,
      Real.rpow_def_of_pos (by positivity)]
    simp only [one_div, a]
  rw [hA]
  nlinarith

/-- Lower bound on the cyclic ratio numerator at the witness. -/
theorem cyclic_witness_numerator_lower {p : ℝ} (hp : 256 ≤ p) :
    2 - (Real.log p + 3) * p⁻¹ ≤
      3 * cyclicA p (constructionParameter p) -
        (3 : ℝ) ^ (1 / p) * |2 - constructionParameter p| := by
  have hi := cutoff_inverse_bounds hp
  have ht := constructionParameter_bounds hp
  have hu := constructionParameter_deficit (p := p)
  have hl := log_mul_inv_bounds hp
  have hA := cyclicA_witness_ge_one hp
  have hc := three_root_le (show 1 ≤ p by linarith)
  have hm := mul_le_mul hc
    (show 2 - constructionParameter p ≤ 1 + Real.log p * p⁻¹ by linarith)
    (show 0 ≤ 2 - constructionParameter p by linarith) (by positivity)
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 - constructionParameter p)]
  have hsmall := mul_le_mul_of_nonneg_right hl.2 hi.1.le
  nlinarith

/-- Upper bound on the cyclic ratio denominator at the witness. -/
theorem cyclic_witness_denominator_upper {p : ℝ} (hp : 256 ≤ p) :
    6 * cyclicA p (constructionParameter p) - 3 * cyclicB p (constructionParameter p) ≤
      6 * ((347 / 500 : ℝ) * p⁻¹ + (p⁻¹) ^ 2) := by
  have hA := cyclicA_witness_sub_one_le hp
  have hB := cyclicB_ge_two (t := constructionParameter p) (show 0 < p by linarith)
  linarith

/-- The cyclic constant exceeds the rational separator `939/2000 · p`. -/
theorem cyclicConstant_gt_separator {p : ℝ} (hp : 256 ≤ p) :
    (939 / 2000 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpi2 : p * (p⁻¹) ^ 2 = p⁻¹ := by rw [pow_two, ← mul_assoc, hpi, one_mul]
  have ht := constructionParameter_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith) (by linarith [ht.1])
  have hnum := cyclic_witness_numerator_lower hp
  have hden := cyclic_witness_denominator_upper hp
  have hdenP := mul_le_mul_of_nonneg_left hden hp0.le
  have hlog := mul_le_mul_of_nonneg_right (log_le_cutoff_tangent hp) hi.1.le
  have hratio : (939 / 2000 : ℝ) * p < cyclicRatio p (constructionParameter p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    nlinarith
  exact hratio.trans_le (cyclicRatio_le_constant (by linarith)
    ⟨ht.1, by linarith [ht.2]⟩)

/-- The `p`-th power of `q₀ = 53/150` is bounded. -/
theorem q0_power_le_half_inverse {p : ℝ} (hp : 256 ≤ p) :
    (53 / 150 : ℝ) ^ p ≤ p⁻¹ / 2 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 2 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 4 * (2 : ℝ) ^ (p - 2) := by
    rw [show p = (p - 2) + 2 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 2 * p ≤ (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (53 / 150 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p := Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ ≤ (2 * p)⁻¹ := inv_anti₀ (by positivity) htwo
    _ = p⁻¹ / 2 := by field_simp

/-- Lower bound on `1 - scalarEnvelopeRoot(q₀)` for `p ≥ 256`. -/
theorem scalarEnvelopeRoot_q0_deficit_lower {p : ℝ} (hp : 256 ≤ p) :
    (693 / 1000 : ℝ) * p⁻¹ - (p⁻¹) ^ 2 ≤
      1 - scalarEnvelopeRoot p (53 / 150) := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  let a := (53 / 150 : ℝ) ^ p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a ≤ p⁻¹ / 2 := q0_power_le_half_inverse hp
  let d := Real.log 2 - Real.log (1 + a)
  have hdLower : 693 / 1000 - p⁻¹ / 2 ≤ d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + a by positivity)
    dsimp [d]
    linarith [log_two_bounds.1]
  have hdUpper : d ≤ 347 / 500 := by
    have h := Real.log_nonneg (show 1 ≤ 1 + a by linarith)
    dsimp [d]
    linarith [log_two_bounds.2]
  have hd0 : 0 ≤ d := by linarith [hi.2]
  have hdSq : d ^ 2 ≤ 1 / 2 := by nlinarith
  have hdr0 : 0 ≤ d * p⁻¹ := mul_nonneg hd0 hi.1.le
  have hdr1 : d * p⁻¹ ≤ 1 := by nlinarith [hi.2]
  have he := Real.norm_exp_sub_one_sub_id_le (x := -(d * p⁻¹))
    (by simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hdr0] using hdr1)
  have he' := (le_abs_self (Real.exp (-(d * p⁻¹)) - 1 - -(d * p⁻¹))).trans he
  simp only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hdr0] at he'
  have hm := mul_le_mul_of_nonneg_right hdLower hi.1.le
  have hs := mul_le_mul_of_nonneg_right hdSq (sq_nonneg p⁻¹)
  have hg : scalarEnvelopeRoot p (53 / 150) = Real.exp (-(d * p⁻¹)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d, a]
    simp only [one_div]
    ring
  rw [hg]
  nlinarith

/-- The scalar envelope at `q₀` is below the separator. -/
theorem scalarEnvelope_q0_lt_separator {p : ℝ} (hp : 256 ≤ p) :
    scalarEnvelope p (53 / 150) < (939 / 2000 : ℝ) * p := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpi2 : p * (p⁻¹) ^ 2 = p⁻¹ := by rw [pow_two, ← mul_assoc, hpi, one_mul]
  have h := scalarEnvelopeRoot_q0_deficit_lower hp
  have hm := mul_le_mul_of_nonneg_left h hp0.le
  rw [scalarEnvelope, div_lt_iff₀ (scalarEnvelope_denominator_pos hp0 (by norm_num) (by norm_num))]
  nlinarith

/-- The cyclic constant exceeds `p/3`. -/
theorem cyclicConstant_gt_exponent_third {p : ℝ} (hp : 256 ≤ p) :
    p / 3 < cyclicConstant p := by
  have h := cyclicConstant_gt_separator hp
  linarith

/-- The scalar envelope at `q₀` is below the cyclic constant. -/
theorem scalarEnvelope_q0_lt_cyclicConstant {p : ℝ} (hp : 256 ≤ p) :
    scalarEnvelope p (53 / 150) < cyclicConstant p :=
  (scalarEnvelope_q0_lt_separator hp).trans (cyclicConstant_gt_separator hp)

end HlawkaSchatten.DiagonalConstruction
