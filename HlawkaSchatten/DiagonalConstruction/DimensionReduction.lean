/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.WeightedCoordinates
import HlawkaSchatten.DiagonalConstruction.Sparsification
import Mathlib.Data.Fin.VecNotation

/-!
# Reduction of a failed bound to three real coordinates

Common coordinate weights preserve the three pair power sums. The positive
part of the target inequality is concave in these weights, so the sparse
minimizer lemma reduces the question to at most three nonzero coordinates.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

private theorem pair_power_sum_pos {p a b c : ℝ} (hp : 0 < p)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    0 < |a + b| ^ p + |a + c| ^ p + |b + c| ^ p := by
  have h1 := Real.rpow_nonneg (abs_nonneg (a + b)) p
  have h2 := Real.rpow_nonneg (abs_nonneg (a + c)) p
  have h3 := Real.rpow_nonneg (abs_nonneg (b + c)) p
  by_contra hn
  have hn' : |a + b| ^ p + |a + c| ^ p + |b + c| ^ p ≤ 0 := le_of_not_gt hn
  have hab : a + b = 0 := abs_eq_zero.mp
    ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp (by linarith : |a + b| ^ p = 0))
  have hac : a + c = 0 := abs_eq_zero.mp
    ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp (by linarith : |a + c| ^ p = 0))
  have hbc : b + c = 0 := abs_eq_zero.mp
    ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp (by linarith : |b + c| ^ p = 0))
  rcases h with h | h | h <;> apply h <;> linarith

private theorem bound_of_fin_three_active {p K : ℝ} (hp : 1 < p) (hK : 1 / 2 ≤ K)
    (h3 : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) K)
    (x y z : ι → ℝ) (hrow : ∀ i, x i ≠ 0 ∨ y i ≠ 0 ∨ z i ≠ 0) :
    tripleGap (lpNorm p) x y z ≤ K * pairGapSum (lpNorm p) x y z := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans hp
  let A : ι → Fin 3 → ℝ := fun i ↦ ![|x i + y i| ^ p, |x i + z i| ^ p, |y i + z i| ^ p]
  let b : Fin 3 → ℝ := fun k ↦ ∑ i, A i k
  let F : (ι → ℝ) → ℝ := fun w ↦
    (2 * K - 1) * (weightedNorm p x w + weightedNorm p y w + weightedNorm p z w) +
      weightedNorm p (x + y + z) w
  have hA : ∀ i k, 0 ≤ A i k := by
    intro i k
    fin_cases k <;> exact Real.rpow_nonneg (abs_nonneg _) p
  have hpos : ∀ i, 0 < ∑ k, A i k := by
    intro i
    simpa only [A, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      pair_power_sum_pos hp0 (hrow i)
  have hF : Continuous F :=
    (continuous_const.mul (((continuous_weightedNorm hp0 x).add
      (continuous_weightedNorm hp0 y)).add (continuous_weightedNorm hp0 z))).add
        (continuous_weightedNorm hp0 (x + y + z))
  have hconc : ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} F := by
    exact (ConcaveOn.smul (by linarith : 0 ≤ 2 * K - 1)
      (((concaveOn_weightedNorm hp x).add (concaveOn_weightedNorm hp y)).add
        (concaveOn_weightedNorm hp z))).add (concaveOn_weightedNorm hp (x + y + z))
  have hseed : (fun _ : ι ↦ (1 : ℝ)) ∈ momentFiber A b := by
    exact ⟨fun _ ↦ zero_le_one, fun _ ↦ by simp [b]⟩
  obtain ⟨w, hw, hmin, hcard⟩ := exists_sparse_concave_minimizer A b hA hpos F hF hconc _ hseed
  let J := {i : ι // w i ≠ 0}
  let R : (ι → ℝ) → J → ℝ := fun v j ↦ reweight p w v j.1
  have hadd (u v : ι → ℝ) : R (u + v) = R u + R v := by
    ext j
    exact congrFun (reweight_add p w u v) j.1
  have hnorm (v : ι → ℝ) : lpNorm p (R v) = weightedNorm p v w := by
    change lpNorm p (fun j : J ↦ reweight p w v j.1) = _
    rw [lpNorm_subtype hp0 (reweight p w v) (fun i ↦ w i ≠ 0)]
    · exact lpNorm_reweight hp0 w v hw.1
    · intro i hi
      simp [reweight, not_ne_iff.mp hi, hp0.ne']
  have hxy : weightedNorm p (x + y) w = lpNorm p (x + y) := by
    unfold weightedNorm lpNorm
    congr 1
    simpa only [A, b, Pi.add_apply, Real.norm_eq_abs, Matrix.cons_val_zero] using hw.2 0
  have hxz : weightedNorm p (x + z) w = lpNorm p (x + z) := by
    unfold weightedNorm lpNorm
    congr 1
    simpa only [A, b, Pi.add_apply, Real.norm_eq_abs, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hw.2 1
  have hyz : weightedNorm p (y + z) w = lpNorm p (y + z) := by
    unfold weightedNorm lpNorm
    congr 1
    simpa only [A, b, Pi.add_apply, Real.norm_eq_abs, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using hw.2 2
  have h := (hasHlawkaConstant_of_card_le_three hp0 hcard h3) (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd, hnorm, hxy, hxz, hyz] at h
  dsimp only [F] at hmin
  simp only [weightedNorm_one] at hmin
  dsimp only [tripleGap, pairGapSum, pairGap]
  nlinarith

/-- A real coordinate inequality in dimension three implies the same bound
in every finite coordinate dimension, for constants at least one half. -/
theorem real_bound_of_fin_three {p K : ℝ} (hp : 1 < p) (hK : 1 / 2 ≤ K)
    (h3 : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) K) :
    HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) K := by
  classical
  intro x y z
  have hp0 : 0 < p := zero_lt_one.trans hp
  let P := fun i ↦ x i ≠ 0 ∨ y i ≠ 0 ∨ z i ≠ 0
  let J := {i : ι // P i}
  let R : (ι → ℝ) → J → ℝ := fun v j ↦ v j.1
  have hadd (u v : ι → ℝ) : R (u + v) = R u + R v := rfl
  have hnorm (v : ι → ℝ) (hv : ∀ i, x i = 0 → y i = 0 → z i = 0 → v i = 0) :
      lpNorm p (R v) = lpNorm p v := by
    apply lpNorm_subtype hp0 v P
    intro i hi
    have hzero : x i = 0 ∧ y i = 0 ∧ z i = 0 := by simpa [P] using hi
    exact hv i hzero.1 hzero.2.1 hzero.2.2
  have h := bound_of_fin_three_active hp hK h3 (R x) (R y) (R z) (fun j ↦ j.2)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  rw [hnorm x (by intros; assumption), hnorm y (by intros; assumption),
    hnorm z (by intros; assumption),
    hnorm (x + y + z) (by intros; simp_all),
    hnorm (x + y) (by intros; simp_all),
    hnorm (x + z) (by intros; simp_all),
    hnorm (y + z) (by intros; simp_all)] at h
  exact h

end HlawkaSchatten.DiagonalConstruction
