/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Transfer
public import HlawkaSchatten.BelowExponent.FractionalMoment
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Positive stable moments and diagonal means

Independence gives the Laplace transform of a weighted sum of positive stable variables.
Its fractional moment then represents the smaller-exponent norm as a positive multiple
of the mean of diagonally rescaled larger-exponent norms.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open MeasureTheory HlawkaSchatten.DiagonalConstruction
open scoped NNReal

/-- A one-dimensional Laplace identity fixes the transform of every nonnegative weighted sum. -/
theorem laplace_weighted_sum {ι : Type*} [Fintype ι] (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (α : ℝ) (hμ : ∀ u : ℝ, 0 ≤ u →
      (∫ y : ℝ≥0, Real.exp (-u*y) ∂μ) = Real.exp (-(u^α)))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y : ι → ℝ≥0, Real.exp (-t * ∑ i, a i * y i) ∂(Measure.pi fun _ => μ)) =
      Real.exp (-(t^α) * ∑ i, (a i)^α) := by
  have factor (y : ι → ℝ≥0) :
      Real.exp (-t * ∑ i, a i * y i) = ∏ i, Real.exp (-(t*a i) * y i) := by
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [factor]
  rw [integral_fintype_prod_eq_prod (fun i (u : ℝ≥0) => Real.exp (-(t*a i) * u))]
  simp_rw [hμ _ (mul_nonneg ht (ha _)), Real.mul_rpow ht (ha _)]
  rw [← Real.exp_sum, Finset.mul_sum]
  simp [neg_mul]

noncomputable def stableWeights {n : ℕ} (p : ℝ) (y : Fin n → ℝ≥0) : Fin n → ℝ :=
  fun i => (y i : ℝ)^(1/p)

theorem lpNorm_stableWeights {p : ℝ} (hp : 0 < p) {n : ℕ} (x : Fin n → ℝ) (y : Fin n → ℝ≥0) :
    lpNorm p (diagonalScale (stableWeights p y) x) = (∑ i, |x i|^p * y i)^(1/p) := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ‖(y i : ℝ)^(1/p) * x i‖ ^ p = _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (y i).coe_nonneg _),
    Real.mul_rpow (Real.rpow_nonneg (y i).coe_nonneg _) (abs_nonneg _),
    ← Real.rpow_mul (y i).coe_nonneg, one_div_mul_cancel hp.ne', Real.rpow_one, mul_comm]

/-- Push the weighted-moment measure forward to a measure on real diagonal scalings. -/
theorem diagonalMean_of_weighted_moments {r p c : ℝ} (hp : 0 < p) (hc : 0 < c)
    {n : ℕ} (μ : Measure (Fin n → ℝ≥0))
    (hi : ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) →
      Integrable (fun y : Fin n → ℝ≥0 => (∑ i, a i * y i)^(1/p)) μ)
    (hm : ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) →
      (∫ y : Fin n → ℝ≥0, (∑ i, a i * y i)^(1/p) ∂μ) = c * (∑ i, (a i)^(r/p))^(1/r)) :
    HasDiagonalMean r p n := by
  have hW : Measurable (stableWeights (n := n) p) := by unfold stableWeights; fun_prop
  have hN (x : Fin n → ℝ) : Continuous (fun w : Fin n → ℝ => lpNorm p (diagonalScale w x)) := by
    unfold HlawkaSchatten.DiagonalConstruction.lpNorm
    change Continuous (fun w : Fin n → ℝ => (∑ i, ‖w i * x i‖^p)^(1/p))
    fun_prop (disch := positivity)
  refine ⟨μ.map (stableWeights p), c, hc, ?_, ?_⟩
  · intro x
    apply (integrable_map_measure (hN x).aestronglyMeasurable hW.aemeasurable).2
    simpa only [Function.comp_def, lpNorm_stableWeights hp] using
      hi (fun i => |x i|^p) (fun i => Real.rpow_nonneg (abs_nonneg _) _)
  · intro x
    rw [integral_map hW.aemeasurable (hN x).aestronglyMeasurable]
    simp_rw [lpNorm_stableWeights hp]
    rw [hm _ (fun i => Real.rpow_nonneg (abs_nonneg _) _)]
    simp only [HlawkaSchatten.DiagonalConstruction.lpNorm, Real.norm_eq_abs,
      ← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ r hp.ne']

/-- The one-dimensional positive stable probability law specified by its Laplace transform. -/
def HasPositiveStable (α : ℝ) : Prop :=
  ∃ μ : Measure ℝ≥0, IsProbabilityMeasure μ ∧ ∀ t : ℝ, 0 ≤ t →
    (∫ y : ℝ≥0, Real.exp (-t*y) ∂μ) = Real.exp (-(t^α))

/-- A positive stable law of index `r / p` gives the diagonal mean in every finite dimension. -/
theorem diagonalMean_of_positiveStable {r p : ℝ} (hr : 1 < r) (hrp : r < p)
    (hs : HasPositiveStable (r/p)) (n : ℕ) : HasDiagonalMean r p n := by
  obtain ⟨μ, hprob, hl⟩ := hs
  have hr₀ : 0 < r := by linarith
  have hp : 0 < p := hr₀.trans hrp
  have hα : 0 < r/p := div_pos hr₀ hp
  have hβ : 0 < 1/p := one_div_pos.mpr hp
  have hβ₁ : 1/p < 1 := (div_lt_one hp).2 (hr.trans hrp)
  have hβα : 1/p < r/p := (div_lt_div_iff_of_pos_right hp).2 hr
  let c := fractionalMomentConstant (r/p) (1/p) / fractionalMomentConstant 1 (1/p)
  have hc : 0 < c := div_pos (integral_fractionalMomentKernel_pos hβ hβα)
    (integral_fractionalMomentKernel_pos hβ hβ₁)
  let ν : Measure (Fin n → ℝ≥0) := Measure.pi fun _ => μ
  have hm (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
      Integrable (fun y : Fin n → ℝ≥0 => (∑ i, a i * y i)^(1/p)) ν ∧
      (∫ y : Fin n → ℝ≥0, (∑ i, a i * y i)^(1/p) ∂ν) = c * (∑ i, (a i)^(r/p))^(1/r) := by
    let A := ∑ i, (a i)^(r/p)
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (ha i) _)
    let b := A ^ (1/(r/p))
    have hb : 0 ≤ b := Real.rpow_nonneg hA _
    have hbα : b ^ (r/p) = A := by
      rw [show b = A ^ (1/(r/p)) from rfl, ← Real.rpow_mul hA, one_div_mul_cancel hα.ne', Real.rpow_one]
    have hf (y : Fin n → ℝ≥0) : 0 ≤ ∑ i, a i * y i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (y i).coe_nonneg
    obtain ⟨hi, he⟩ := fractionalMoment_of_laplace ν hβ hβ₁ hβα hb
      (fun y : Fin n → ℝ≥0 => ∑ i, a i * y i) (by fun_prop) hf (fun t ht => by
        rw [laplace_weighted_sum μ (r/p) hl a ha ht.le, Real.mul_rpow hb ht.le, hbα]
        congr 1
        dsimp [A]
        ring)
    refine ⟨hi, ?_⟩
    have hpow : 1 / (r/p) * (1/p) = 1/r := by field_simp
    change (∫ y : Fin n → ℝ≥0, (∑ i, a i * y i)^(1/p) ∂ν) = b^(1/p) * c at he
    simp only [b, ← Real.rpow_mul hA, hpow] at he
    exact he.trans (mul_comm _ _)
  exact diagonalMean_of_weighted_moments hp hc ν (fun a ha => (hm a ha).1) (fun a ha => (hm a ha).2)

end HlawkaSchatten.BelowExponent
