/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.DiagonalConstruction.CoordinateNorm
public import HlawkaSchatten.GapComparison.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-! Relate Route T's zero-sum quartet to the published mission predicate.
The first two dimensions also admit direct proofs. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem hasHlawkaConstant_one_iff {E : Type*} [Add E] (N : E → ℝ) :
    HasHlawkaConstant N 1 ↔ ∀ x y z, N (x+y) + N (x+z) + N (y+z) ≤
      N x + N y + N z + N (x+y+z) := by
  unfold HasHlawkaConstant tripleGap pairGapSum pairGap
  constructor <;> intro h x y z <;> specialize h x y z <;> linarith

/-- The final specialization of the quartet theorem works in every additive commutative group. -/
theorem hasHlawkaConstant_one_of_zeroSum {E : Type*} [AddCommGroup E] (N : E → ℝ)
    (hneg : ∀ x, N (-x) = N x)
    (hq : ∀ f : Fin 4 → E, (∑ i, f i) = 0 →
      N (f 0 + f 3) + N (f 0 + f 2) + N (f 0 + f 1) ≤ ∑ i, N (f i)) :
    HasHlawkaConstant N 1 := by
  apply (hasHlawkaConstant_one_iff N).2
  intro x y z
  have hz : (∑ i : Fin 4, ![x, y, z, -(x+y+z)] i) = 0 := by
    simp [Fin.sum_univ_succ]
  have hs := hq _ hz
  have hpair : x + -(x+y+z) = -(y+z) := by abel
  simp [Fin.sum_univ_succ, -neg_add_rev, hpair, hneg] at hs
  linarith

/-- The scalar Hlawka inequality, using each possible sign of the three pair sums. -/
theorem real_abs_hlawka (x y z : ℝ) :
    |x+y| + |x+z| + |y+z| ≤ |x| + |y| + |z| + |x+y+z| := by
  rcases abs_choice (x+y) with h₁ | h₁ <;>
    rcases abs_choice (x+z) with h₂ | h₂ <;>
    rcases abs_choice (y+z) with h₃ | h₃ <;>
    linarith only [h₁, h₂, h₃, le_abs_self x, neg_le_abs x, le_abs_self y, neg_le_abs y,
      le_abs_self z, neg_le_abs z, le_abs_self (x+y+z), neg_le_abs (x+y+z)]

theorem lpNorm_fin_one {p : ℝ} (hp : 0 < p) (x : Fin 1 → ℝ) : lpNorm p x = |x 0| := by
  simp only [lpNorm, Fin.sum_univ_one, Real.norm_eq_abs]
  rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem hlawka_fin_one {p : ℝ} (hp : 0 < p) :
    HasHlawkaConstant (lpNorm p : (Fin 1 → ℝ) → ℝ) 1 := by
  apply (hasHlawkaConstant_one_iff _).2
  intro x y z
  simpa only [lpNorm_fin_one hp, Pi.add_apply] using real_abs_hlawka (x 0) (y 0) (z 0)

theorem hlawka_fin_zero (p : ℝ) :
    HasHlawkaConstant (lpNorm p : (Fin 0 → ℝ) → ℝ) 1 := by
  apply (hasHlawkaConstant_one_iff _).2
  intro x y z
  simp only [lpNorm, Finset.univ_eq_empty, Finset.sum_empty]
  have hz : 0 ≤ (0 : ℝ) ^ (1 / p) := Real.rpow_nonneg (by norm_num) _
  linarith

end HlawkaSchatten.BelowExponent
