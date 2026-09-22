/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Normalization
import HlawkaSchatten.DiagonalConstruction.TailEstimates

/-! # Scalar confinement of a normalized strict counterexample -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

theorem normalized_failure_total_lt_q0 {p : ℝ} (hp : 256 ≤ p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    lpNorm p (x + y + z) < 53 / 150 := by
  have hp1 : 1 < p := by linarith
  have hK := one_le_cyclicConstant hp1
  have hq1 := normalized_failure_total_lt_one hp1.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp1 hK x y z hS hf
  by_contra hn
  have hq0 : (53 / 150 : ℝ) ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp1.le
    (show (53 / 150 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hq1⟩) hq0
  linarith [scalarEnvelope_q0_lt_cyclicConstant hp]

/-- The scalar data used by the coordinate argument. -/
theorem normalized_failure_confinement {p : ℝ} (hp : 256 ≤ p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 53 / 150) ∧
      pairGapSum (lpNorm p) x y z < 2 / p ∧
      (22 / 75 < lpNorm p x ∧ lpNorm p x < 53 / 150) ∧
      (22 / 75 < lpNorm p y ∧ lpNorm p y < 53 / 150) ∧
      (22 / 75 < lpNorm p z ∧ lpNorm p z < 53 / 150) := by
  have hp1 : 1 < p := by linarith
  have hq := normalized_failure_total_lt_q0 hp x y z hS hf
  have hqLower : 1 / 3 ≤ lpNorm p (x + y + z) := by linarith
  have hD := pairGapSum_nonneg hp1.le x y z
  have hK := cyclicConstant_gt_exponent_third hp
  have hmul := mul_le_mul_of_nonneg_right hK.le hD
  have hf' := hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf'
  have hsmall : pairGapSum (lpNorm p) x y z < 2 / p := by
    rw [lt_div_iff₀ (show 0 < p by linarith)]
    nlinarith
  exact ⟨⟨hqLower, hq⟩, hsmall, ⟨by linarith, hx.trans_lt hq⟩,
    ⟨by linarith, hy.trans_lt hq⟩, ⟨by linarith, hz.trans_lt hq⟩⟩

end HlawkaSchatten.DiagonalConstruction
