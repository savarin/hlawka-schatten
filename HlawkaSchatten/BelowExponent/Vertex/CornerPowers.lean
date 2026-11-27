/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3Power
public import HlawkaSchatten.BelowExponent.Vertex.CornerGridData
public import HlawkaSchatten.BelowExponent.Vertex.DyadicBounds
public import HlawkaSchatten.BelowExponent.Vertex.CornerMinorants
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerLookup
import all HlawkaSchatten.BelowExponent.Interpolation
import Batteries.Tactic.OpenPrivate

/-! Shared checks for the three powers in the outer corner minorants. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open private abs_rpow_lerp_le from HlawkaSchatten.BelowExponent.Interpolation

def outerAxisMidpoint (i : Fin 34) : ℚ :=
  ((outerInterval i).lo + (outerInterval i).hi) / 2

def outerAbsQOK (x : ℚ) (P : RatBounds) : Bool :=
  decide (0 ≤ P.hi) && G3Power.tightLower x P.lo && G3Power.tightUpper x P.hi

theorem outerAbsQOK_sound {x : ℚ} {P : RatBounds} (h : outerAbsQOK x P = true) :
    P.Contains (|(x : ℝ)| ^ criticalQ) := by
  simp only [outerAbsQOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨G3Power.tightLower_sound h.1.2, G3Power.tightUpper_sound h.1.1 h.2⟩

def outerSignedFromQ (x : ℚ) (P : RatBounds) : DyadicBounds :=
  if x = 0 then DyadicBounds.point 0
  else DyadicBounds.ofRat (P.mul (RatBounds.point (1 / x)))

theorem outerSignedFromQ_sound {x : ℚ} {P : RatBounds}
    (h : P.Contains (|(x : ℝ)| ^ criticalQ)) :
    (outerSignedFromQ x P).Contains (signedPower criticalQ x) := by
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  by_cases hx : x = 0
  · subst x
    simpa [outerSignedFromQ, signedPower, Real.zero_rpow (sub_pos.mpr hq).ne'] using
      DyadicBounds.point_mem (0 : ℚ)
  · have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    have hpow := Real.rpow_sub (abs_pos.mpr hx') criticalQ 1
    rw [Real.rpow_one] at hpow
    have hsign : signedPower criticalQ (x : ℝ) = |(x : ℝ)| ^ criticalQ / (x : ℝ) := by
      rcases le_or_gt 0 (x : ℝ) with hs | hs
      · simpa only [signedPower, ite_eq_left hs, abs_of_nonneg hs] using hpow
      · rw [signedPower_eq_neg_rpow hq hs.le, ← abs_of_nonpos hs.le, hpow,
          abs_of_nonpos hs.le, div_neg, neg_neg]
    have hm := RatBounds.mul_mem h (RatBounds.point_mem (1 / x))
    rw [outerSignedFromQ, ite_eq_right hx, hsign]
    exact DyadicBounds.ofRat_mem (by simpa only [Rat.cast_div, Rat.cast_one, mul_one_div] using hm)

def outerSlopeFromQ (x : ℚ) (P : RatBounds) : DyadicBounds :=
  DyadicBounds.ofRat (P.mul (RatBounds.point (1 / x^2)))

theorem outerSlopeFromQ_sound {x : ℚ} {P : RatBounds} (hx : x ≠ 0)
    (h : P.Contains (|(x : ℝ)| ^ criticalQ)) :
    (outerSlopeFromQ x P).Contains (|(x : ℝ)| ^ (criticalQ-2)) := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  rw [Real.rpow_sub (abs_pos.mpr hx'), Real.rpow_two, sq_abs, div_eq_mul_one_div]
  have hm := RatBounds.mul_mem h (RatBounds.point_mem (1 / x^2))
  exact DyadicBounds.ofRat_mem (by push_cast at hm; exact hm)

def outerUpperTableOK (values : Array (Array ℤ)) : Bool :=
  (List.range 1026).all fun k =>
    let y := outerUpperEntry values k
    decide (0 ≤ y) && G3Power.tightUpper (outerKnot k) y

theorem outerRpowChord_sound {values : Array (Array ℤ)} (h : outerUpperTableOK values = true)
    {x : ℚ} (hx : |x| ≤ 4) : |(x : ℝ)| ^ criticalQ ≤ (outerRpowChord values x : ℝ) := by
  let j := outerChordIndex x
  let t := outerChordFraction x
  have hfloor : ((j : ℕ) : ℤ) = ⌊256 * |x|⌋ :=
    Int.toNat_of_nonneg (Int.floor_nonneg.mpr (mul_nonneg (by norm_num) (abs_nonneg x)))
  have hfloor' : (j : ℚ) = ((⌊256 * |x|⌋ : ℤ) : ℚ) := by exact_mod_cast hfloor
  have hle : (j : ℚ) ≤ 256 * |x| := by rw [hfloor']; exact Int.floor_le _
  have hlt : 256 * |x| < (j : ℚ) + 1 := by rw [hfloor']; exact Int.lt_floor_add_one _
  have hj : j ≤ 1024 := by
    exact_mod_cast (show (j : ℚ) ≤ 1024 by linarith only [hle, hx])
  have ht₀ : (0 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ t from sub_nonneg.mpr hle)
  have ht₁ : (t : ℝ) ≤ 1 := by
    exact_mod_cast (show t ≤ (1 : ℚ) by unfold t outerChordFraction; linarith only [hlt])
  have hu (k : Nat) (hk : k < 1026) :
      |(outerKnot k : ℝ)| ^ criticalQ ≤ (outerUpperEntry values k : ℝ) := by
    have hh := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    obtain ⟨hp, hc⟩ := Bool.and_eq_true_iff.mp hh
    exact G3Power.tightUpper_sound (of_decide_eq_true hp) hc
  have hq : 1 ≤ criticalQ := by linarith only [criticalQ_bracket.1]
  have href : (1-(t : ℝ))*(outerKnot j : ℝ) + (t : ℝ)*(outerKnot (j+1) : ℝ) = |(x : ℝ)| := by
    have hr : (t : ℝ) = 256 * |(x : ℝ)| - (j : ℝ) := by simp [t, outerChordFraction, j]
    simp only [outerKnot, Rat.cast_div, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
    norm_num
    rw [hr]
    ring
  have hb := abs_rpow_lerp_le hq ht₀ ht₁
    (outerKnot j : ℝ) (outerKnot (j+1) : ℝ)
  rw [href, abs_abs] at hb
  exact hb.trans (by
    push_cast [outerRpowChord]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hu j (by omega)) (sub_nonneg.mpr ht₁))
      (mul_le_mul_of_nonneg_left (hu (j+1) (by omega)) ht₀))

end HlawkaSchatten.BelowExponent.Vertex
