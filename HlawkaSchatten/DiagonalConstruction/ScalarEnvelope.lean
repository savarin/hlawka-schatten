/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.ScalarBounds
import HlawkaSchatten.DiagonalConstruction.CyclicWitness

/-! # Monotonicity of the scalar envelope -/

namespace HlawkaSchatten.DiagonalConstruction

theorem cyclicConstant_le_exponent {p : ℝ} (hp : 1 < p) : cyclicConstant p ≤ p := by
  obtain ⟨t, ht, heq⟩ := cyclic_maximum_attained hp
  rw [← heq]
  exact cyclicRatio_le_of_real_constant hp (lp_hlawka_le_exponent hp) (by linarith [ht.1])

theorem scalarEnvelopeRoot_eq_lpNorm {p q : ℝ} (hq : 0 ≤ q) :
    scalarEnvelopeRoot p q = (1 / 2 : ℝ) ^ (1 / p) * lpNorm p ![1, q] := by
  simp only [scalarEnvelopeRoot, lpNorm, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, abs_one, abs_of_nonneg hq, Real.one_rpow]
  rw [show (1 + q ^ p) / 2 = (1 / 2 : ℝ) * (1 + q ^ p) by ring,
    Real.mul_rpow (by norm_num) (by positivity)]

theorem convexOn_scalarEnvelopeRoot {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (Set.Ici 0) (scalarEnvelopeRoot p) := by
  refine ⟨convex_Ici _, ?_⟩
  intro q hq r hr a b ha hb hab
  have hqr : 0 ≤ a * q + b * r := add_nonneg (mul_nonneg ha hq) (mul_nonneg hb hr)
  have heq : ![1, a * q + b * r] = a • ![1, q] + b • ![1, r] := by
    ext i
    fin_cases i <;> simp [hab]
  have h := (convexOn_lpNorm (ι := Fin 2) (E := ℝ) hp).2
    (Set.mem_univ ![1, q]) (Set.mem_univ ![1, r]) ha hb hab
  simp only [smul_eq_mul]
  rw [scalarEnvelopeRoot_eq_lpNorm hqr, scalarEnvelopeRoot_eq_lpNorm hq,
    scalarEnvelopeRoot_eq_lpNorm hr, heq]
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / p))
  simpa only [smul_eq_mul, mul_add, mul_left_comm] using hm

@[simp]
theorem scalarEnvelopeRoot_one (p : ℝ) : scalarEnvelopeRoot p 1 = 1 := by
  norm_num [scalarEnvelopeRoot]

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

/-- Convexity of the root makes its secant quotient nonincreasing. -/
theorem antitoneOn_scalarEnvelope {p : ℝ} (hp : 1 ≤ p) :
    AntitoneOn (scalarEnvelope p) (Set.Ico 0 1) := by
  intro r hr q hq hrq
  have hp0 := zero_lt_one.trans_le hp
  have hrne : 1 - r ≠ 0 := by linarith [hr.2]
  let a := (1 - q) / (1 - r)
  let b := (q - r) / (1 - r)
  have ha : 0 ≤ a := div_nonneg (by linarith [hq.2]) (by linarith [hr.2])
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hrq) (by linarith [hr.2])
  have hab : a + b = 1 := by dsimp [a, b]; field_simp [hrne]; ring
  have hpoint : a • r + b • (1 : ℝ) = q := by
    dsimp [a, b, smul_eq_mul]
    field_simp [hrne]
    ring
  have hconv := (convexOn_scalarEnvelopeRoot hp).2 hr.1 (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    ha hb hab
  rw [hpoint, scalarEnvelopeRoot_one] at hconv
  simp only [smul_eq_mul] at hconv
  have hm := mul_le_mul_of_nonneg_left hconv (by linarith [hr.2] : 0 ≤ 1 - r)
  have heq : (1 - r) * (a * scalarEnvelopeRoot p r + b * 1) =
      (1 - q) * scalarEnvelopeRoot p r + (q - r) := by
    dsimp [a, b]
    field_simp [hrne]
  rw [heq] at hm
  rw [scalarEnvelope, scalarEnvelope,
    div_le_div_iff₀ (scalarEnvelope_denominator_pos hp0 hq.1 hq.2)
      (scalarEnvelope_denominator_pos hp0 hr.1 hr.2)]
  nlinarith

end HlawkaSchatten.DiagonalConstruction
