/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalCheck
public import HlawkaSchatten.BelowExponent.VertexWeights

/-! Transport the checked rational fifth powers and local refinements to real coefficient intervals.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def RatBounds.Contains (b : RatBounds) (x : ℝ) := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

/-- No rounding assumptions are made about the supplied rational witnesses. -/
theorem rootBounds_sound {A B S R : RatBounds} (hc : rootBoundsOK A B S R = true)
    {a b s r : ℝ} (ha : A.Contains a) (hb : B.Contains b) (hs : S.Contains s)
    (hr : r^5 = a^2*b^3/s^2) : R.Contains r := by
  simp only [rootBoundsOK, decide_eq_true_eq] at hc
  obtain ⟨hA, hB, hS, hR, hRR, low, high⟩ := hc
  have a₀ : (0:ℝ) ≤ A.lo := by exact_mod_cast hA
  have b₀ : (0:ℝ) ≤ B.lo := by exact_mod_cast hB
  have s₀ : (0:ℝ) < S.lo := by exact_mod_cast hS
  have r₀ : (0:ℝ) ≤ R.lo := by exact_mod_cast hR
  have rr : (R.lo:ℝ) ≤ R.hi := by exact_mod_cast hRR
  have rs := r₀.trans rr
  have sa := s₀.trans_le hs.1
  have low' : (R.lo:ℝ)^5 * (S.hi:ℝ)^2 ≤ (A.lo:ℝ)^2 * (B.lo:ℝ)^3 := by exact_mod_cast low
  have high' : (A.hi:ℝ)^2 * (B.hi:ℝ)^3 ≤ (R.hi:ℝ)^5 * (S.lo:ℝ)^2 := by exact_mod_cast high
  have hodd : Odd (5 : ℕ) := by decide
  constructor
  · apply hodd.pow_le_pow.mp
    rw [hr, le_div_iff₀ (sq_pos_of_pos sa)]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ sa.le hs.2 2) (pow_nonneg r₀ 5)).trans
      (low'.trans (mul_le_mul (pow_le_pow_left₀ a₀ ha.1 2) (pow_le_pow_left₀ b₀ hb.1 3)
        (pow_nonneg b₀ 3) (sq_nonneg a)))
  · apply hodd.pow_le_pow.mp
    rw [hr, div_le_iff₀ (sq_pos_of_pos sa)]
    exact (mul_le_mul (pow_le_pow_left₀ (a₀.trans ha.1) ha.2 2)
      (pow_le_pow_left₀ (b₀.trans hb.1) hb.2 3) (pow_nonneg (b₀.trans hb.1) 3) (sq_nonneg _)).trans
      (high'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ s₀.le hs.1 2) (pow_nonneg rs 5)))

theorem radical_mem_of_checks {ε : ℝ} {e : Row} {j : Fin 3} {A B S R : RatBounds}
    (hc : rootBoundsOK A B S R = true) (ha : A.Contains ((1-ε)*(1-e j)+ε*cross e j))
    (hb : B.Contains (1-ε*e j)) (hs : S.Contains (sigmaTwo e)) :
    R.Contains (radical ε e j) := by
  have hc' := hc
  simp only [rootBoundsOK, decide_eq_true_eq] at hc'
  have hb' : (0:ℝ) ≤ B.lo := by exact_mod_cast hc'.2.1
  have hn : 0 ≤ radicand ε e j :=
    div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (hb'.trans hb.1) 3)) (sq_nonneg _)
  exact rootBounds_sound hc ha hb hs (radical_fifth hn)

/-- Refining the parent root only requires rational interval operations on this identity. -/
theorem fifth_refinement {r a B : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (h : r^5 = B) :
    r = a + (B-a^5)/(r^4+r^3*a+r^2*a^2+r*a^3+a^4) := by
  have hd : 0 < r^4+r^3*a+r^2*a^2+r*a^3+a^4 := by positivity
  rw [← h]
  field_simp [hd.ne']
  ring

end HlawkaSchatten.BelowExponent.Vertex
