/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Finite-dimensional Schatten quantities

This file gives the definition needed by the Hlawka boundary. Mathlib's
singular-value sequence is finitely supported, so the power sum is finite
without choosing bases or matrix dimensions.
-/

namespace HlawkaSchatten

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The sum of the `p`-th powers of the singular values of `T`. -/
noncomputable def singularValuePowerSum (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ i ∈ T.singularValues.support, (T.singularValues i) ^ p

/--
The finite-dimensional Schatten `p` quantity: the `1 / p` power of the
sum of the `p`-th powers of the singular values.

For the norm laws, the intended range is `1 ≤ p`. Keeping the definition
total makes boundary statements straightforward while putting analytic
hypotheses on the theorems that need them.
-/
noncomputable def schattenPNorm (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  (singularValuePowerSum p T) ^ (1 / p)

/-- The unit sphere described by a singular-value power sum.  This is the
normalization naturally used by the Mazur map before taking the outer
`p`-th root in the Schatten norm. -/
def schattenPowerSphere (p : ℝ) :=
  {T : E →ₗ[𝕜] F // singularValuePowerSum p T = 1}

theorem singularValuePowerSum_nonneg (p : ℝ) (T : E →ₗ[𝕜] F) :
    0 ≤ singularValuePowerSum p T := by
  unfold singularValuePowerSum
  exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (T.singularValues_nonneg i) _

theorem schattenPNorm_nonneg (p : ℝ) (T : E →ₗ[𝕜] F) :
    0 ≤ schattenPNorm p T :=
  Real.rpow_nonneg (singularValuePowerSum_nonneg p T) _

theorem singularValuePowerSum_pos (p : ℝ) {T : E →ₗ[𝕜] F}
    (hT : T ≠ 0) : 0 < singularValuePowerSum p T := by
  unfold singularValuePowerSum
  have hsupport : T.singularValues.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact T.singularValues_eq_zero_iff.not.mpr hT
  apply Finset.sum_pos'
  · exact fun i _ ↦ Real.rpow_nonneg (T.singularValues_nonneg i) _
  · obtain ⟨i, hi⟩ := hsupport
    refine ⟨i, hi, Real.rpow_pos_of_pos ?_ p⟩
    exact (T.singularValues_pos_iff_ne_zero i).mpr (Finsupp.mem_support_iff.mp hi)

theorem schattenPNorm_pos (p : ℝ) {T : E →ₗ[𝕜] F} (hT : T ≠ 0) :
    0 < schattenPNorm p T :=
  Real.rpow_pos_of_pos (singularValuePowerSum_pos p hT) _

theorem schattenPNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (T : E →ₗ[𝕜] F) :
    schattenPNorm p T = 0 ↔ T = 0 := by
  constructor
  · intro h
    by_contra hT
    exact (schattenPNorm_pos p hT).ne' h
  · rintro rfl
    simp [schattenPNorm, singularValuePowerSum, hp.ne']

/-- For a positive exponent, unit Schatten norm is equivalent to unit
singular-value power sum. -/
theorem schattenPNorm_eq_one_iff {p : ℝ} (hp : 0 < p) (T : E →ₗ[𝕜] F) :
    schattenPNorm p T = 1 ↔ singularValuePowerSum p T = 1 := by
  let s := singularValuePowerSum p T
  have hs : 0 ≤ s := singularValuePowerSum_nonneg p T
  constructor
  · intro h
    have hspos : 0 < s := by
      by_contra hn
      have hs0 : s = 0 := le_antisymm (le_of_not_gt hn) hs
      unfold schattenPNorm at h
      rw [show singularValuePowerSum p T = s by rfl, hs0,
        Real.zero_rpow (one_div_ne_zero hp.ne')] at h
      norm_num at h
    have hpow := congrArg (fun x : ℝ => x ^ p) h
    simp only [Real.one_rpow] at hpow
    change (s ^ (1 / p)) ^ p = 1 at hpow
    rw [← Real.rpow_mul hs] at hpow
    rw [show 1 / p * p = 1 by field_simp [hp.ne'], Real.rpow_one] at hpow
    exact hpow
  · intro h
    unfold schattenPNorm
    rw [h, Real.one_rpow]

@[simp]
theorem singularValuePowerSum_zero (p : ℝ) :
    singularValuePowerSum p (0 : E →ₗ[𝕜] F) = 0 := by
  simp [singularValuePowerSum]

@[simp]
theorem schattenPNorm_zero (p : ℝ) (hp : p ≠ 0) :
    schattenPNorm p (0 : E →ₗ[𝕜] F) = 0 := by
  simp [schattenPNorm, hp]

/-- At exponent two, the singular-value power sum is the real trace of the
domain Gram operator. -/
theorem singularValuePowerSum_two_eq_re_trace (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 2 T =
      RCLike.re ((T.adjoint.comp T).trace 𝕜 E) := by
  have hrank : Module.finrank 𝕜 T.range ≤ Module.finrank 𝕜 E :=
    T.finrank_range_le
  have hsum :
      (∑ i ∈ Finset.range (Module.finrank 𝕜 T.range), T.singularValues i ^ 2) =
        ∑ i ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues i ^ 2 := by
    apply Finset.sum_subset (Finset.range_mono hrank)
    intro i hi hi'
    have hirank : Module.finrank 𝕜 T.range ≤ i := by
      exact Nat.le_of_not_gt (fun hlt ↦ hi' (Finset.mem_range.mpr hlt))
    rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr hirank]
    norm_num
  unfold singularValuePowerSum
  rw [T.support_singularValues]
  simp_rw [Real.rpow_two]
  rw [T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues rfl]
  simp_rw [← T.sq_singularValues_fin rfl]
  exact hsum.trans (Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ T.singularValues i ^ 2) (Module.finrank 𝕜 E)).symm

/-- Squaring the Schatten-2 quantity recovers its power sum. -/
theorem schattenPNorm_two_sq (T : E →ₗ[𝕜] F) :
    schattenPNorm 2 T ^ 2 = singularValuePowerSum 2 T := by
  unfold schattenPNorm
  norm_num
  convert Real.rpow_inv_natCast_pow (singularValuePowerSum_nonneg 2 T)
    (by norm_num : (2 : ℕ) ≠ 0) using 1
  norm_num

end HlawkaSchatten
