/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetConeRow
public import HlawkaSchatten.BelowExponent.FacetNumericSound

/-! A box can omit base corner checks only inside the real facet cone. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

noncomputable section

def chartRow (j : Fin 3) (a b : ℝ) : Row :=
  ![![1, a, b], ![a, 1, b], ![a, b, 1]] j

private theorem lower_of_gate {D r n m : Nat} (hD : 0 < D) (hr : 0 < r)
    (hgate : D * r ≤ (m - D) * (r + n)) {x : ℝ} (hx : (m : ℝ) ≤ x) :
    (r : ℝ) / ((r : ℝ) + n) ≤ x / D - 1 := by
  have hpos : 0 < D * r := Nat.mul_pos hD hr
  have hm : D ≤ m := by
    by_contra! h
    rw [Nat.sub_eq_zero_of_le h.le, zero_mul] at hgate
    exact hpos.not_ge hgate
  have hmul : (D : ℝ) * r ≤ ((m : ℝ) - D) * ((r : ℝ) + n) := by
    exact_mod_cast hgate
  have hs : 0 < (r : ℝ) + n := by exact_mod_cast Nat.add_pos_left hr n
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hh : (D : ℝ) * r ≤ (x - D) * ((r : ℝ) + n) :=
    hmul.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hx _) hs.le)
  have h := (div_le_div_iff₀ hs hDr).2 (by linarith only [hh] :
    (r : ℝ) * D ≤ (x - D) * ((r : ℝ) + n))
  rwa [sub_div, div_self hDr.ne'] at h

private theorem upper_of_gate {D r n m : Nat} (hD : 0 < D) (hr : 0 < r)
    (hgate : D * r ≤ (D - m) * (r + n)) {x : ℝ} (hx : x ≤ (m : ℝ)) :
    x / D - 1 ≤ -((r : ℝ) / ((r : ℝ) + n)) := by
  have hpos : 0 < D * r := Nat.mul_pos hD hr
  have hm : m ≤ D := by
    by_contra! h
    rw [Nat.sub_eq_zero_of_le h.le, zero_mul] at hgate
    exact hpos.not_ge hgate
  have hmul : (D : ℝ) * r ≤ ((D : ℝ) - m) * ((r : ℝ) + n) := by
    exact_mod_cast hgate
  have hs : 0 < (r : ℝ) + n := by exact_mod_cast Nat.add_pos_left hr n
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hh : (D : ℝ) * r ≤ ((D : ℝ) - x) * ((r : ℝ) + n) :=
    hmul.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hx _) hs.le)
  have h := (div_le_div_iff₀ hs hDr).2 (by linarith only [hh] :
    (r : ℝ) * D ≤ ((D : ℝ) - x) * ((r : ℝ) + n))
  rw [sub_div, div_self hDr.ne'] at h
  linarith only [h]

theorem isConeBox_sound (P : Prism) {j : Fin 3} {A2 B1 B2 : Nat} {a b : ℝ}
    (hr : 0 < P.radiusDen) (hgate : isConeBox P j.val A2 B1 B2 = true)
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 2 * (ctx.Da : ℝ))
    (ha : a ≤ (A2 : ℝ)) (hbL : (B1 : ℝ) ≤ b) (hbR : b ≤ (B2 : ℝ)) :
    FacetRatioCone ((P.radiusNum : ℝ) / P.radiusDen)
      (chartRow j (a / ctx.Da - 1) (b / ctx.Da - 1)) := by
  let ρ : ℝ := (P.radiusNum : ℝ) / P.radiusDen
  let m : ℝ := (P.radiusDen : ℝ) / ((P.radiusDen : ℝ) + P.radiusNum)
  let x := a / ctx.Da - 1
  let y := b / ctx.Da - 1
  have hD : 0 < ctx.Da := by decide
  have hDr : (0 : ℝ) < ctx.Da := by exact_mod_cast hD
  have hrR : (0 : ℝ) < P.radiusDen := by exact_mod_cast hr
  have hsum : 0 < (P.radiusDen : ℝ) + P.radiusNum := by positivity
  have hm₀ : 0 ≤ m := div_nonneg hrR.le hsum.le
  have hm₁ : m ≤ 1 := (div_le_one₀ hsum).2 (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hρ : 0 ≤ ρ := div_nonneg (Nat.cast_nonneg _) hrR.le
  have hprod : (1 + ρ) * m = 1 := by
    dsimp [ρ, m]
    field_simp
  simp only [isConeBox, Bool.and_eq_true] at hgate
  have hx₁ : x ≤ -m := upper_of_gate hD hr (TC.ble_true.mp hgate.1) ha
  have hx₀ : -1 ≤ x := by dsimp [x]; linarith [div_nonneg ha₀ hDr.le]
  have hy₀ : -1 ≤ y := by dsimp [y]; linarith [div_nonneg hb₀ hDr.le]
  have hy₁ : y ≤ 1 := by
    have hh := (div_le_iff₀ hDr).2 hb₁
    dsimp [y]
    linarith
  have hxNP : x ≤ 0 := by linarith only [hx₁, hm₀]
  have hxr : m ≤ -x ∧ -x ≤ 1 := ⟨by linarith only [hx₁], by linarith only [hx₀]⟩
  let z := chartRow j x y
  have hin : ((∀ i, 0 ≤ facetFlip z i) ∨ (∀ i, facetFlip z i ≤ 0)) ∧
      ∀ i, m ≤ |facetFlip z i| ∧ |facetFlip z i| ≤ 1 := by
    fin_cases j
    · have hyN : y ≤ -m := upper_of_gate hD hr
        (TC.ble_true.mp (by simpa using hgate.2)) hbR
      have hyNP : y ≤ 0 := by linarith only [hyN, hm₀]
      refine ⟨Or.inl (fun i => ?_), fun i => ?_⟩
      · fin_cases i <;> simp [z, chartRow, facetFlip, hxNP, hyNP]
      · fin_cases i <;> simp [z, chartRow, facetFlip, abs_of_nonpos hxNP, abs_of_nonpos hyNP, hm₁]
        all_goals constructor <;> linarith
    · have hyP : m ≤ y := lower_of_gate hD hr
        (TC.ble_true.mp (by simpa using hgate.2)) hbL
      have hyNN : 0 ≤ y := hm₀.trans hyP
      refine ⟨Or.inr (fun i => ?_), fun i => ?_⟩
      · fin_cases i <;> simp [z, chartRow, facetFlip, hxNP, hyNN]
      · fin_cases i <;> simp [z, chartRow, facetFlip, abs_of_nonpos hxNP, abs_of_nonneg hyNN,
          hxr, hm₁, hyP, hy₁]
    · have hyP : m ≤ y := lower_of_gate hD hr
        (TC.ble_true.mp (by simpa using hgate.2)) hbL
      have hyNN : 0 ≤ y := hm₀.trans hyP
      refine ⟨Or.inr (fun i => ?_), fun i => ?_⟩
      · fin_cases i <;> simp [z, chartRow, facetFlip, hxNP, hyNN]
      · fin_cases i <;> simp [z, chartRow, facetFlip, abs_of_nonpos hxNP, abs_of_nonneg hyNN,
          hxr, hm₁, hyP, hy₁]
  refine ⟨hin.1, fun i k => (hin.2 i).2.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left (hin.2 k).1 (by linarith : 0 ≤ 1 + ρ)
  rwa [hprod] at h

end

end HlawkaSchatten.BelowExponent.FacetNumeric
