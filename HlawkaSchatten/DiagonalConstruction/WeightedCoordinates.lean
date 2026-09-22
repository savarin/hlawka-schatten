/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Concavity under common coordinate reweighting -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

noncomputable def weightedNorm (p : ℝ) (x w : ι → ℝ) : ℝ :=
  (∑ i, w i * |x i| ^ p) ^ (1 / p)

noncomputable def reweight (p : ℝ) (w x : ι → ℝ) : ι → ℝ :=
  fun i ↦ w i ^ (1 / p) * x i

omit [Fintype ι] in
theorem reweight_add (p : ℝ) (w x y : ι → ℝ) :
    reweight p w (x + y) = reweight p w x + reweight p w y := by
  ext i
  exact mul_add _ _ _

theorem lpNorm_reweight {p : ℝ} (hp : 0 < p) (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : lpNorm p (reweight p w x) = weightedNorm p x w := by
  unfold lpNorm weightedNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [reweight, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw i) (1 / p))]
  rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
    ← Real.rpow_mul (hw i), one_div_mul_cancel hp.ne', Real.rpow_one]

theorem weightedNorm_one (p : ℝ) (x : ι → ℝ) :
    weightedNorm p x (fun _ ↦ 1) = lpNorm p x := by
  simp [weightedNorm, lpNorm, Real.norm_eq_abs]

theorem continuous_weightedNorm {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    Continuous (weightedNorm p x) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).mul continuous_const).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

omit [Fintype ι] in
theorem convex_nonnegative_weights : Convex ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
  intro w hw v hv a b ha hb _ i
  exact add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hv i))

theorem concaveOn_weightedNorm {p : ℝ} (hp : 1 < p) (x : ι → ℝ) :
    ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} (weightedNorm p x) := by
  refine ⟨convex_nonnegative_weights, ?_⟩
  intro w hw v hv a b ha hb hab
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hwSum : 0 ≤ ∑ i, w i * |x i| ^ p :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hvSum : 0 ≤ ∑ i, v i * |x i| ^ p :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hv i) (Real.rpow_nonneg (abs_nonneg _) _)
  have h := (Real.concaveOn_rpow (one_div_nonneg.mpr hp0.le)
    ((div_le_one hp0).mpr hp.le)).2
    hwSum hvSum ha hb hab
  simpa only [weightedNorm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] using h

end HlawkaSchatten.DiagonalConstruction
