/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Basic
import HlawkaSchatten.DiagonalConstruction.WeightedConvex
import HlawkaSchatten.ScalarBregman
import Mathlib.Analysis.Convex.Jensen

/-!
# The weighted scalar estimate for arbitrary coordinate triples

The weights are the three input norms. Applying the scalar convexity
inequality coordinate by coordinate yields the dimension-independent power
estimate used to confine a hypothetical counterexample.
-/

namespace HlawkaSchatten.DiagonalConstruction

theorem weighted_abs_rpow_div {a : ℝ} (ha : 0 < a) (p x : ℝ) :
    a * |x / a| ^ p = |x| ^ p / a ^ (p - 1) := by
  rw [abs_div, abs_of_pos ha, Real.div_rpow (abs_nonneg x) ha.le,
    Real.rpow_sub ha, Real.rpow_one]
  field_simp

theorem rpow_div_pred {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    a ^ p / a ^ (p - 1) = a := by
  by_cases h : a = 0
  · subst a
    simp [ne_of_gt (zero_lt_one.trans hp), ne_of_gt (sub_pos.mpr hp)]
  · have ha0 := lt_of_le_of_ne ha (Ne.symm h)
    rw [Real.rpow_sub ha0, Real.rpow_one]
    field_simp

theorem weighted_scalar_power {p a b c : ℝ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    |x + y| ^ p / (a + b) ^ (p - 1) +
      |x + z| ^ p / (a + c) ^ (p - 1) +
      |y + z| ^ p / (b + c) ^ (p - 1) ≤
    |x| ^ p / a ^ (p - 1) + |y| ^ p / b ^ (p - 1) + |z| ^ p / c ^ (p - 1) +
      |x + y + z| ^ p / (a + b + c) ^ (p - 1) := by
  have h := weighted_convex_hlawka (convexOn_abs_rpow hp.le) ha hb hc
    (x / a) (y / b) (z / c)
  simp only [weightedPairs, weightedTotal,
    mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ hb.ne', mul_div_cancel₀ _ hc.ne'] at h
  simpa only [weighted_abs_rpow_div ha, weighted_abs_rpow_div hb,
    weighted_abs_rpow_div hc, weighted_abs_rpow_div (add_pos ha hb),
    weighted_abs_rpow_div (add_pos ha hc), weighted_abs_rpow_div (add_pos hb hc),
    weighted_abs_rpow_div (add_pos (add_pos ha hb) hc)] using h

variable {ι : Type*} [Fintype ι]

theorem weighted_lp_power_of_ne {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    weighted_scalar_power hp (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hy)
      (lpNorm_pos hp0 hz) (x i) (y i) (z i))
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Real.norm_eq_abs] at h
  change
    (∑ i, ‖(x + y) i‖ ^ p) / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      (∑ i, ‖(x + z) i‖ ^ p) / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      (∑ i, ‖(y + z) i‖ ^ p) / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    (∑ i, ‖x i‖ ^ p) / lpNorm p x ^ (p - 1) +
      (∑ i, ‖y i‖ ^ p) / lpNorm p y ^ (p - 1) +
      (∑ i, ‖z i‖ ^ p) / lpNorm p z ^ (p - 1) +
      (∑ i, ‖(x + y + z) i‖ ^ p) /
        (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) at h
  simpa only [← lpNorm_rpow hp0, rpow_div_pred hp (lpNorm_nonneg p x),
    rpow_div_pred hp (lpNorm_nonneg p y), rpow_div_pred hp (lpNorm_nonneg p z)] using h

theorem weighted_lp_power {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hx : x = 0
  · subst x
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p y),
      rpow_div_pred hp (lpNorm_nonneg p z)]
  by_cases hy : y = 0
  · subst y
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p x),
      rpow_div_pred hp (lpNorm_nonneg p z)]
    ring_nf
    rfl
  by_cases hz : z = 0
  · subst z
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p x),
      rpow_div_pred hp (lpNorm_nonneg p y)]
    ring_nf
    rfl
  exact weighted_lp_power_of_ne hp x y z hx hy hz

theorem normalized_power_le {p a b : ℝ} (hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    b ^ p / a ^ (p - 1) ≤ b := by
  by_cases h : a = 0
  · have hb0 : b = 0 := le_antisymm (h ▸ hba) hb
    simp [h, hb0, (zero_lt_one.trans hp).ne']
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos ha0 (p - 1))).mpr
  have hpow := Real.rpow_le_rpow hb hba (sub_nonneg.mpr hp.le)
  have he : b ^ p = b * b ^ (p - 1) := by
    by_cases hb0 : b = 0
    · simp [hb0, (zero_lt_one.trans hp).ne']
    · rw [Real.rpow_sub (lt_of_le_of_ne hb (Ne.symm hb0)), Real.rpow_one]
      field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hpow hb

theorem normalized_power_deficit_le {p a b : ℝ} (hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    a - b ^ p / a ^ (p - 1) ≤ p * (a - b) := by
  by_cases h : a = 0
  · have hb0 : b = 0 := le_antisymm (h ▸ hba) hb
    simp [h, hb0, (zero_lt_one.trans hp).ne']
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
  have hbern := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ b / a - 1 by linarith [div_nonneg hb ha]) hp.le
  have habs : |b / a| = b / a := abs_of_nonneg (div_nonneg hb ha)
  have he := weighted_abs_rpow_div ha0 p b
  rw [habs, abs_of_nonneg hb] at he
  have hm := mul_le_mul_of_nonneg_left hbern ha
  have hr : a * (b / a) = b := mul_div_cancel₀ b ha0.ne'
  simp only [add_sub_cancel] at hm
  nlinarith

/-- A rough but uniform bound, also controlling triples with zero pair deficit. -/
theorem lp_hlawka_le_exponent {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    tripleGap (lpNorm p) x y z ≤ p * pairGapSum (lpNorm p) x y z := by
  have hx := lpNorm_nonneg p x
  have hy := lpNorm_nonneg p y
  have hz := lpNorm_nonneg p z
  have hxy := lpNorm_add hp.le x y
  have hxz := lpNorm_add hp.le x z
  have hyz := lpNorm_add hp.le y z
  have htotal : lpNorm p (x + y + z) ≤ lpNorm p x + lpNorm p y + lpNorm p z :=
    (lpNorm_add hp.le (x + y) z).trans (add_le_add hxy le_rfl)
  have h0 := weighted_lp_power hp x y z
  have h1 := normalized_power_deficit_le hp (add_nonneg hx hy)
    (lpNorm_nonneg p (x + y)) hxy
  have h2 := normalized_power_deficit_le hp (add_nonneg hx hz)
    (lpNorm_nonneg p (x + z)) hxz
  have h3 := normalized_power_deficit_le hp (add_nonneg hy hz)
    (lpNorm_nonneg p (y + z)) hyz
  have h4 := normalized_power_le hp (add_nonneg (add_nonneg hx hy) hz)
    (lpNorm_nonneg p (x + y + z)) htotal
  dsimp only [tripleGap, pairGapSum, pairGap]
  nlinarith

theorem weighted_mean_power_le {p : ℝ} (hp : 1 < p) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, a i = 2) :
    ((∑ i, b i) / 2) ^ p ≤ (∑ i, b i ^ p / a i ^ (p - 1)) / 2 := by
  have h := (convexOn_abs_rpow hp.le).map_sum_le (t := Finset.univ)
    (w := fun i ↦ a i / 2) (p := fun i ↦ b i / a i)
    (fun i _ ↦ div_nonneg (ha i).le (by norm_num))
    (by rw [← Finset.sum_div, hs]; norm_num) (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have hmean (i : ι) : a i / 2 * (b i / a i) = b i / 2 := by
    field_simp [(ha i).ne']
  have hpower (i : ι) : a i / 2 * |b i / a i| ^ p =
      (b i ^ p / a i ^ (p - 1)) / 2 := by
    calc
      _ = (a i * |b i / a i| ^ p) / 2 := by ring
      _ = _ := by rw [weighted_abs_rpow_div (ha i), abs_of_nonneg (hb i)]
  have habs : |(∑ i, b i) / 2| = (∑ i, b i) / 2 :=
    abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ ↦ hb i) (by norm_num))
  simpa only [hmean, hpower, ← Finset.sum_div, habs] using h

noncomputable def scalarEnvelopeRoot (p q : ℝ) : ℝ := ((1 + q ^ p) / 2) ^ (1 / p)

noncomputable def scalarEnvelope (p q : ℝ) : ℝ :=
  (1 - q) / (2 * (1 - scalarEnvelopeRoot p q))

/-- The full total-norm-dependent envelope before dividing by the pair gap. -/
theorem normalized_pair_sum_le {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1) :
    lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z) ≤
      2 * scalarEnvelopeRoot p (lpNorm p (x + y + z)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let a : Fin 3 → ℝ := ![lpNorm p x + lpNorm p y,
    lpNorm p x + lpNorm p z, lpNorm p y + lpNorm p z]
  let b : Fin 3 → ℝ := ![lpNorm p (x + y), lpNorm p (x + z), lpNorm p (y + z)]
  have ha : ∀ i, 0 < a i := by
    intro i
    fin_cases i
    · exact add_pos (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hy)
    · exact add_pos (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hz)
    · exact add_pos (lpNorm_pos hp0 hy) (lpNorm_pos hp0 hz)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> exact lpNorm_nonneg p _
  have hsum : ∑ i, a i = 2 := by
    simp only [a, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith
  have hmean := weighted_mean_power_le hp a b ha hb hsum
  have hweighted := weighted_lp_power hp x y z
  rw [hS, Real.one_rpow, div_one] at hweighted
  simp only [a, b, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hmean
  have hpow : ((lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z)) / 2) ^ p ≤
      (1 + lpNorm p (x + y + z) ^ p) / 2 := by linarith
  have hbase : 0 ≤ (1 + lpNorm p (x + y + z) ^ p) / 2 :=
    div_nonneg (add_nonneg zero_le_one
      (Real.rpow_nonneg (lpNorm_nonneg p (x + y + z)) p)) (by norm_num)
  have hroot : scalarEnvelopeRoot p (lpNorm p (x + y + z)) ^ p =
      (1 + lpNorm p (x + y + z) ^ p) / 2 := by
    rw [scalarEnvelopeRoot, ← Real.rpow_mul hbase,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  rw [← hroot] at hpow
  have h := (Real.rpow_le_rpow_iff
    (div_nonneg (add_nonneg (add_nonneg (lpNorm_nonneg p (x + y))
      (lpNorm_nonneg p (x + z))) (lpNorm_nonneg p (y + z))) (by norm_num))
    (Real.rpow_nonneg hbase _) hp0).mp hpow
  change (lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z)) / 2 ≤
    scalarEnvelopeRoot p (lpNorm p (x + y + z)) at h
  linarith

end HlawkaSchatten.DiagonalConstruction
