/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactInteger

/-! The integer checker gives the original compact G1 inequalities. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G1CompactData

private theorem num_eq (a : ℚ) : (a.num : ℚ) = a * (a.den : ℚ) :=
  (div_eq_iff (by exact_mod_cast a.den_ne_zero)).mp a.num_div_den

theorem intCorner_sound (P : G1CompactParams) (l : Nat) (hP : P.l = (l : ℚ)/4096)
    (j : Fin 129) (h : intCorner l (intCoefficients P) j = true) :
    compactCost P (knot j) ≤ P.l + (1-P.l)*ordinate j := by
  let A := P.k * P.l ^ 2 / P.μ
  let B := P.β
  let C := P.α
  let x : ℚ := (knotNum j : ℚ)
  let o : ℚ := (lowerOrdinates[(knotNum j).natAbs]?.getD 0 : ℚ)
  let m : ℚ := (4096 * 256) ^ 2 * (A.den : ℚ) * B.den * C.den
  let s : ℚ := 4096 * 2 ^ 36
  have hpos : 0 < m * s := by
    dsimp [m, s]
    have ha : (0 : ℚ) < A.den := by exact_mod_cast A.den_pos
    have hb : (0 : ℚ) < B.den := by exact_mod_cast B.den_pos
    have hc : (0 : ℚ) < C.den := by exact_mod_cast C.den_pos
    positivity
  unfold intCorner at h
  have hi := (Int.cast_le (R := ℚ)).2 (of_decide_eq_true h)
  dsimp [intCoefficients] at hi
  push_cast at hi
  rw [num_eq (P.k * P.l ^ 2 / P.μ), num_eq P.β, num_eq P.α] at hi
  have hgoal : A * (x / 256 - 1) ^ 2 + B +
      C * ((1 - (l : ℚ)/4096) * (x/256) + (l : ℚ)/4096) ^ 2 ≤
      (l : ℚ)/4096 + (1 - (l : ℚ)/4096) * (o / 2 ^ 36) := by
    apply le_of_mul_le_mul_left _ hpos
    convert hi using 1 <;> dsimp [m, s, A, B, C, x, o] <;> ring
  simpa only [compactCost, knot, ordinate, tangentScale, A, B, C, x, o, hP, Nat.cast_pow, Nat.cast_ofNat] using hgoal

theorem intSlab_sound (i : Fin 13) (hi : intSlab i = true) :
    ∀ right j, compactCornersOK i right j := by
  intro right j
  have hbins : (List.finRange 64).all (intBin i right) = true := by
    simp only [intSlab, intSide, Bool.and_eq_true] at hi
    rcases hi with ⟨h₀, h₁⟩
    cases right
    · exact h₀
    · exact h₁
  have hbin := List.all_eq_true.mp hbins j (List.mem_finRange _)
  intro z hz edge
  have hbox := List.all_eq_true.mp hbin z (List.mem_finRange _)
  unfold intBox at hbox
  rw [decide_eq_true hz, Bool.not_true, Bool.false_or] at hbox
  simp only [Bool.and_eq_true] at hbox
  obtain ⟨hleft, hright⟩ := hbox
  have hP : (compactParams i right j).l = (lengthNum i right : ℚ)/4096 := rfl
  cases edge
  · exact intCorner_sound _ _ hP z.castSucc hleft
  · exact intCorner_sound _ _ hP z.succ hright

end HlawkaSchatten.BelowExponent.G1CompactData
