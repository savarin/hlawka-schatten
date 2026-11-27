/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Transfer
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! The exponent 2 in every finite real dimension, by averaging the scalar
Hlawka inequality over real Gaussian projections. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open MeasureTheory ProbabilityTheory HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open scoped RealInnerProductSpace

private theorem gaussian_abs_integral_pos : 0 < ∫ y : ℝ, |y| ∂(gaussianReal 0 1) := by
  have hi : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs
  rw [integral_pos_iff_support_of_nonneg (fun y => abs_nonneg y) hi]
  have hs : Function.support (fun y : ℝ => |y|) = ({0} : Set ℝ)ᶜ := by
    ext y
    simp [Function.mem_support]
  have hz : gaussianReal 0 1 ({0} : Set ℝ) = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (measure_singleton _)
  rw [hs, measure_compl (measurableSet_singleton _) (measure_ne_top _ _), hz]
  simp

private theorem gaussian_integral_abs_dual {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    (∫ w, |L w| ∂(stdGaussian E)) = (∫ y : ℝ, |y| ∂(gaussianReal 0 1)) * ‖L‖ := by
  have hmap : (stdGaussian E).map L = (gaussianReal 0 1).map (‖L‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
      gaussianReal_map_const_mul]
    simp [Real.toNNReal]
  calc
    _ = ∫ y : ℝ, |y| ∂((stdGaussian E).map L) :=
      (integral_map L.continuous.aemeasurable continuous_abs.aestronglyMeasurable).symm
    _ = ∫ y : ℝ, |‖L‖ * y| ∂(gaussianReal 0 1) := by
      rw [hmap, integral_map (by fun_prop) continuous_abs.aestronglyMeasurable]
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (norm_nonneg L)]; rw [integral_const_mul, mul_comm]

/-- Constant-one Hlawka for any finite-dimensional real inner product space. -/
theorem hilbert_hlawka (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : HasHlawkaConstant (fun x : E => ‖x‖) 1 := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let D (w : E) := (innerSL ℝ w).toLinearMap.toAddMonoidHom
  have heq (x w : E) : D w x = innerSL ℝ x w := real_inner_comm _ _
  apply hlawka_of_mean (stdGaussian E) D abs _ gaussian_abs_integral_pos
    ((hasHlawkaConstant_one_iff abs).2 real_abs_hlawka)
  · intro x
    simpa only [heq] using (IsGaussian.integrable_dual (stdGaussian E) (innerSL ℝ x)).abs
  · intro x
    simpa only [heq, innerSL_apply_norm] using gaussian_integral_abs_dual (innerSL ℝ x)

/-- The mission inequality at the left endpoint holds in every real dimension. -/
theorem hlawka_two (n : ℕ) : HasHlawkaConstant (lpNorm 2 : (Fin n → ℝ) → ℝ) 1 := by
  apply (hasHlawkaConstant_one_iff _).2
  intro x y z
  have h := (hasHlawkaConstant_one_iff _).1 (hilbert_hlawka (EuclideanSpace ℝ (Fin n)))
    (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  have hnorm (a : Fin n → ℝ) : lpNorm 2 a = ‖WithLp.toLp 2 a‖ := by
    rw [PiLp.norm_eq_sum (by norm_num : 0 < (2 : ENNReal).toReal)]
    simp [DiagonalConstruction.lpNorm]
  simpa only [hnorm, WithLp.toLp_add] using h

end HlawkaSchatten.BelowExponent
