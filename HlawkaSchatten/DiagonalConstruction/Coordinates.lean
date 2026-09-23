/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Confinement

/-! # Large pair coordinates and signed coordinate permutations -/

namespace HlawkaSchatten.DiagonalConstruction

/-- The `p`-norm is at most `3^(1/p)` times the max entry. -/
theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

/-- The bound `1 - 3^(-1/p) ≤ log(3)/p`. -/
theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith

/-- A signed entry is at most the norm. -/
theorem signed_entry_le_norm {p s : ℝ} (hp : 1 ≤ p) (hs : |s| = 1)
    (x : Fin 3 → ℝ) (i : Fin 3) : s * x i ≤ lpNorm p x := by
  calc
    _ ≤ |s * x i| := le_abs_self _
    _ = |x i| := by rw [abs_mul, hs, one_mul]
    _ ≤ _ := norm_apply_le_lpNorm hp x i

/-- Small pair gap forces two large entries with one common sign. -/
theorem exists_large_signed_pair {p : ℝ} (hp : 256 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 53 / 150) (hy : lpNorm p y < 53 / 150)
    (hgap : pairGap (lpNorm p) x y < 2 / p) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 14 / (5 * p) < s * x i ∧
      lpNorm p y - 14 / (5 * p) < s * y i := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |(x + y) i|)
    Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 (x + y) i (fun j ↦ hi j (Finset.mem_univ _))
  let c := ((3 : ℝ) ^ (1 / p))⁻¹
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hmax' : c * lpNorm p (x + y) ≤ |x i + y i| := by
    have hm := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |(x + y) i|) = |(x + y) i| := by
      dsimp [c]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [he] at hm
    exact hm
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
  have hs0 : 0 ≤ lpNorm p x + lpNorm p y := add_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg p y)
  have hbound : lpNorm p x + lpNorm p y - |x i + y i| < 14 / (5 * p) := by
    have hS : lpNorm p x + lpNorm p y < 53 / 75 := by linarith
    have hdef := mul_le_mul_of_nonneg_right hd hs0
    have hg := pairGap_nonneg hp1 x y
    have hgap' := mul_le_mul_of_nonneg_right hc1 hg
    have hlogP : 0 ≤ Real.log 3 / p := by positivity
    have hSlog := mul_le_mul_of_nonneg_left hS.le hlogP
    have hlogDiv := (div_lt_div_iff_of_pos_right hp0).mpr hlog3
    have hlogLast := mul_lt_mul_of_pos_right hlogDiv (by norm_num : (0 : ℝ) < 53 / 75)
    dsimp only [pairGap] at hgap hg hgap'
    have hnum : Real.log 3 / p * (53 / 75 : ℝ) + 2 / p < 14 / (5 * p) := by
      have hrat : (11 / 10 : ℝ) / p * (53 / 75) + 2 / p < 14 / (5 * p) := by
        apply (mul_lt_mul_iff_left₀ hp0).mp
        field_simp
        norm_num
      linarith
    nlinarith
  by_cases hi0 : 0 ≤ x i + y i
  · rw [abs_of_nonneg hi0] at hbound
    have hxi := signed_entry_le_norm hp1 (s := 1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := 1) (by norm_num) y i
    exact ⟨i, 1, Or.inl rfl, by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    have hxi := signed_entry_le_norm hp1 (s := -1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := -1) (by norm_num) y i
    exact ⟨i, -1, Or.inr rfl, by linarith, by linarith⟩

/-- A simultaneous coordinate permutation and reflection. -/
def orient (e : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ s i * x (e i)

/-- Orientation distributes over addition. -/
theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _

/-- The `p`-norm is invariant under orientation. -/
theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e

/-- The deficit is invariant under orientation. -/
theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]

end HlawkaSchatten.DiagonalConstruction
