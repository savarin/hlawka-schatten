/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Cyclic
import Mathlib.Data.Fin.VecNotation

/-!
# Cyclic witnesses and the necessary lower bound

The three cyclic vectors have equal norms and their ratio is the scalar
formula defining the comparison constant. Zero padding preserves all seven
norms, so the lower bound holds in every dimension at least three.
-/

namespace HlawkaSchatten.DiagonalConstruction

def cyclicX (t : ℝ) : Fin 3 → ℝ := ![-t, 1, 1]
def cyclicY (t : ℝ) : Fin 3 → ℝ := ![1, -t, 1]
def cyclicZ (t : ℝ) : Fin 3 → ℝ := ![1, 1, -t]

theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t) = cyclicA p t := by
  simp [lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicY t) = cyclicA p t := by
  simp [lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicXY (p t : ℝ) :
    lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

theorem lpNorm_cyclicXZ (p t : ℝ) :
    lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

theorem lpNorm_cyclicYZ (p t : ℝ) :
    lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp

theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring

theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

theorem cyclicRatio_le_of_real_constant {p C : ℝ} (hp : 1 < p)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) C)
    {t : ℝ} (ht : 0 ≤ t) : cyclicRatio p t ≤ C := by
  have h := hC (cyclicX t) (cyclicY t) (cyclicZ t)
  rw [cyclic_tripleGap (zero_lt_one.trans hp) ht, cyclic_pairGapSum ht] at h
  exact (div_le_iff₀ (cyclic_denominator_pos hp ht)).mpr h

theorem real_constant_of_complex_constant {p C : ℝ} {n : ℕ}
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) C := by
  intro x y z
  have h := hC (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  have hadd (u v : Fin n → ℝ) :
      (fun i ↦ (u i : ℂ)) + (fun i ↦ (v i : ℂ)) =
        fun i ↦ ((u + v) i : ℂ) := by ext; simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_ofReal] using h

theorem cyclicConstant_le_of_complex_constant {p C : ℝ} (hp : 1 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C) :
    cyclicConstant p ≤ C := by
  obtain ⟨t, ht, heq⟩ := cyclic_maximum_attained hp
  rw [← heq]
  exact cyclicRatio_le_of_real_constant hp
    (hasHlawkaConstant_fin_three_of_ge (zero_lt_one.trans hp) hn
      (real_constant_of_complex_constant hC)) (by linarith [ht.1])

end HlawkaSchatten.DiagonalConstruction
