/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConePowers
public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds
public import HlawkaSchatten.BelowExponent.G3Power

/-! Rational endpoint witnesses for the SC Taylor multipliers. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def sidePowerOK (p x : ℚ) (P : RatBounds) : Bool :=
  decide (-1 < x ∧ 0 < p ∧ 0 ≤ P.lo ∧ 0 ≤ P.hi) &&
    G3Power.crossLE P.lo (1+x) p.den p.num.natAbs &&
    G3Power.crossLE (1+x) P.hi p.num.natAbs p.den

def firstPoint (p x : ℚ) (P : RatBounds) : RatBounds :=
  if x = 0 then RatBounds.point 1
  else (P.sub (RatBounds.point 1)).mul (RatBounds.point (1 / (p*x)))

def secondPoint (p x : ℚ) (P : RatBounds) : RatBounds :=
  if x = 0 then RatBounds.point 1
  else ((P.sub (RatBounds.point 1)).sub (RatBounds.point (p*x))).mul
    (RatBounds.point (2 / (p*(p-1)*x^2)))

structure FactorSamples where
  lowerPower : RatBounds
  upperPower : RatBounds

def exponentLower (P : RatBounds) (x : ℚ) : ℚ := if x ≤ 0 then P.hi else P.lo
def exponentUpper (P : RatBounds) (x : ℚ) : ℚ := if x ≤ 0 then P.lo else P.hi
def argumentLower (X : RatBounds) (inc : Bool) : ℚ := if inc then X.lo else X.hi
def argumentUpper (X : RatBounds) (inc : Bool) : ℚ := if inc then X.hi else X.lo

def firstFactorRangeOK (P X : RatBounds) (inc : Bool) (W : FactorSamples) : Bool :=
  let x₀ := argumentLower X inc
  let x₁ := argumentUpper X inc
  decide (-1 < X.lo) &&
    sidePowerOK (exponentLower P x₀) x₀ W.lowerPower &&
    sidePowerOK (exponentUpper P x₁) x₁ W.upperPower

def firstFactorRange (P X : RatBounds) (inc : Bool) (W : FactorSamples) : RatBounds :=
  let x₀ := argumentLower X inc
  let x₁ := argumentUpper X inc
  ⟨(firstPoint (exponentLower P x₀) x₀ W.lowerPower).lo,
    (firstPoint (exponentUpper P x₁) x₁ W.upperPower).hi⟩

def secondFactorRangeOK (P X : RatBounds) (W : FactorSamples) : Bool :=
  decide (-1 < X.lo ∧ exponentLower P X.hi ≠ 1 ∧ exponentUpper P X.lo ≠ 1) &&
    sidePowerOK (exponentLower P X.hi) X.hi W.lowerPower &&
    sidePowerOK (exponentUpper P X.lo) X.lo W.upperPower

def secondFactorRange (P X : RatBounds) (W : FactorSamples) : RatBounds :=
  ⟨(secondPoint (exponentLower P X.hi) X.hi W.lowerPower).lo,
    (secondPoint (exponentUpper P X.lo) X.lo W.upperPower).hi⟩

noncomputable section

theorem sidePowerOK_sound {p x : ℚ} {P : RatBounds} (h : sidePowerOK p x P = true) :
    P.Contains ((1 + (x : ℝ)) ^ (p : ℝ)) := by
  simp only [sidePowerOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hx, hp, hl, hr, hlo, hhi⟩ := h
  have hxR : (-1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hb : (0 : ℝ) ≤ ((1+x : ℚ) : ℝ) := by push_cast; linarith only [hxR]
  have hlR : (0 : ℝ) ≤ (P.lo : ℝ) := by exact_mod_cast hl
  have hrR : (0 : ℝ) ≤ (P.hi : ℝ) := by exact_mod_cast hr
  have he : (p.num.natAbs : ℝ) / p.den = (p : ℝ) := by
    have hn := Rat.num_nonneg.mpr hp.le
    have hnum : (p.num.natAbs : ℤ) = p.num :=
      (Int.natCast_natAbs p.num).trans (abs_of_nonneg hn)
    have hnumR : (p.num.natAbs : ℝ) = (p.num : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hnum
    rw [Rat.cast_def, hnumR]
  have left := G3Power.crossLE_lower p.den_pos hlo
  have right := G3Power.crossLE_upper p.den_pos hhi
  rw [abs_of_nonneg hb, abs_of_nonneg hlR, he] at left
  rw [abs_of_nonneg hb, abs_of_nonneg hrR, he] at right
  push_cast at left right
  exact ⟨left, right⟩

theorem firstPoint_sound {p x : ℚ} {P : RatBounds} (h : sidePowerOK p x P = true) :
    (firstPoint p x P).Contains (sideFirstFactor (p : ℝ) (x : ℝ)) := by
  have hP := sidePowerOK_sound h
  have hb : -1 < x ∧ 0 < p ∧ 0 ≤ P.lo ∧ 0 ≤ P.hi := by
    simp only [sidePowerOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hx : (-1 : ℝ) < (x : ℝ) := by exact_mod_cast hb.1
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hb.2.1
  unfold firstPoint
  split
  · rename_i hz
    subst x
    simpa only [Rat.cast_zero, side_first_factor_zero, Rat.cast_one] using RatBounds.point_mem 1
  · rename_i hz
    have hxr : (x : ℝ) ≠ 0 := by exact_mod_cast hz
    have hf := side_first_factor_eq (p := (p : ℝ)) hx
    have hg := RatBounds.mul_mem (RatBounds.sub_mem hP (RatBounds.point_mem 1))
      (RatBounds.point_mem (1 / (p*x)))
    push_cast at hg
    have he : ((1 + (x : ℝ)) ^ (p : ℝ)-1) * (1 / ((p : ℝ)*(x : ℝ))) =
        sideFirstFactor (p : ℝ) (x : ℝ) := by
      rw [hf]
      field_simp [hp.ne', hxr]
    rwa [he] at hg

theorem secondPoint_sound {p x : ℚ} {P : RatBounds} (h : sidePowerOK p x P = true)
    (hp₁ : p ≠ 1) :
    (secondPoint p x P).Contains (sideSecondFactor (p : ℝ) (x : ℝ)) := by
  have hP := sidePowerOK_sound h
  have hb : -1 < x ∧ 0 < p ∧ 0 ≤ P.lo ∧ 0 ≤ P.hi := by
    simp only [sidePowerOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hx : (-1 : ℝ) < (x : ℝ) := by exact_mod_cast hb.1
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hb.2.1
  have hp₁r : (p : ℝ) ≠ 1 := by exact_mod_cast hp₁
  unfold secondPoint
  split
  · rename_i hz
    subst x
    simpa only [Rat.cast_zero, side_second_factor_zero, Rat.cast_one] using RatBounds.point_mem 1
  · rename_i hz
    have hxr : (x : ℝ) ≠ 0 := by exact_mod_cast hz
    have hf := side_second_factor_eq (p := (p : ℝ)) hx
    have hg := RatBounds.mul_mem (RatBounds.sub_mem
      (RatBounds.sub_mem hP (RatBounds.point_mem 1)) (RatBounds.point_mem (p*x)))
      (RatBounds.point_mem (2 / (p*(p-1)*x^2)))
    push_cast at hg
    have he : powerRemainder (p : ℝ) (x : ℝ) * (2 / ((p : ℝ)*((p : ℝ)-1)*(x : ℝ)^2)) =
        sideSecondFactor (p : ℝ) (x : ℝ) := by
      rw [hf]
      field_simp [hp.ne', hxr, sub_ne_zero.mpr hp₁r]
    change (((1 + (x : ℝ)) ^ (p : ℝ))-1-(p : ℝ)*(x : ℝ)) * _ = _ at he
    rwa [he] at hg

private theorem exponent_ends {F : ℝ → ℝ → ℝ} {P : RatBounds} {p : ℝ} {x : ℚ}
    (hx : -1 < (x : ℝ)) (hp : P.Contains p)
    (hF : ∀ {s t : ℝ}, -1 < (x : ℝ) → (if (x : ℝ) ≤ 0 then t ≤ s else s ≤ t) →
      F s (x : ℝ) ≤ F t (x : ℝ)) :
    F (exponentLower P x : ℝ) (x : ℝ) ≤ F p (x : ℝ) ∧
      F p (x : ℝ) ≤ F (exponentUpper P x : ℝ) (x : ℝ) := by
  by_cases hn : x ≤ 0
  · have hn' : (x : ℝ) ≤ 0 := by exact_mod_cast hn
    simp only [exponentLower, exponentUpper, ite_eq_left hn]
    exact ⟨hF hx (by simpa only [ite_eq_left hn'] using hp.2),
      hF hx (by simpa only [ite_eq_left hn'] using hp.1)⟩
  · have hn' : ¬ (x : ℝ) ≤ 0 := fun h => hn (by exact_mod_cast h)
    simp only [exponentLower, exponentUpper, ite_eq_right hn]
    exact ⟨hF hx (by simpa only [ite_eq_right hn'] using hp.1),
      hF hx (by simpa only [ite_eq_right hn'] using hp.2)⟩

theorem firstFactorRange_sound {P X : RatBounds} {inc : Bool} {W : FactorSamples} {p x : ℝ}
    (h : firstFactorRangeOK P X inc W = true) (hp : P.Contains p) (hx : X.Contains x)
    (hm : if inc then 1 ≤ p else p ≤ 1) :
    (firstFactorRange P X inc W).Contains (sideFirstFactor p x) := by
  simp only [firstFactorRangeOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hdom, h₀, h₁⟩ := h
  have hl : (-1 : ℝ) < (X.lo : ℝ) := by exact_mod_cast hdom
  have hr : (-1 : ℝ) < (X.hi : ℝ) := hl.trans_le (hx.1.trans hx.2)
  have hL : -1 < (argumentLower X inc : ℝ) := by cases inc <;> assumption
  have hU : -1 < (argumentUpper X inc : ℝ) := by cases inc <;> assumption
  have hE₀ := exponent_ends hL hp side_first_factor_exponent
  have hE₁ := exponent_ends hU hp side_first_factor_exponent
  have hX₀ : sideFirstFactor p (argumentLower X inc : ℝ) ≤ sideFirstFactor p x := by
    cases inc
    · exact side_first_factor_antitone hm (hl.trans_le hx.1) hx.2
    · exact side_first_factor_monotone hm hl hx.1
  have hX₁ : sideFirstFactor p x ≤ sideFirstFactor p (argumentUpper X inc : ℝ) := by
    cases inc
    · exact side_first_factor_antitone hm hl hx.1
    · exact side_first_factor_monotone hm (hl.trans_le hx.1) hx.2
  exact ⟨(firstPoint_sound h₀).1.trans (hE₀.1.trans hX₀),
    hX₁.trans (hE₁.2.trans (firstPoint_sound h₁).2)⟩

theorem secondFactorRange_sound {P X : RatBounds} {W : FactorSamples} {p x : ℝ}
    (h : secondFactorRangeOK P X W = true) (hp : P.Contains p) (hx : X.Contains x)
    (hm : p ≤ 2) : (secondFactorRange P X W).Contains (sideSecondFactor p x) := by
  simp only [secondFactorRangeOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hdom, hpL, hpR, h₀, h₁⟩ := h
  have hl : (-1 : ℝ) < (X.lo : ℝ) := by exact_mod_cast hdom
  have hr : (-1 : ℝ) < (X.hi : ℝ) := hl.trans_le (hx.1.trans hx.2)
  have hE₀ := exponent_ends hr hp side_second_factor_exponent
  have hE₁ := exponent_ends hl hp side_second_factor_exponent
  have hX₀ := side_second_factor_antitone hm (hl.trans_le hx.1) hx.2
  have hX₁ := side_second_factor_antitone hm hl hx.1
  exact ⟨(secondPoint_sound h₀ hpL).1.trans (hE₀.1.trans hX₀),
    hX₁.trans (hE₁.2.trans (secondPoint_sound h₁ hpR).2)⟩

end

end HlawkaSchatten.BelowExponent.Vertex
