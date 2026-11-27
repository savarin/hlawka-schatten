/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen
import Mathlib.Tactic

/-! The common-denominator arithmetic gives the original exact rational endpoints. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

namespace CommonDen

private theorem dne (a : CommonDen) : (a.den : ℚ) ≠ 0 := by
  exact_mod_cast a.den_pos.ne'

@[simp] theorem ofRat_toBounds (x : ℚ) : (ofRat x).toBounds = point x := by
  simp [ofRat, toBounds, lower, upper, point, RatBounds.point, Rat.num_div_den]

@[simp] theorem ofBounds_toBounds (x : RatBounds) : (ofBounds x).toBounds = x := by
  unfold ofBounds
  split
  · rename_i h
    exact RatBounds.mk.injEq .. |>.mpr
      ⟨by simp [lower, Rat.num_div_den], by simp [upper, h, Rat.num_div_den]⟩
  · have h₀ : (x.lo.den : ℚ) ≠ 0 := by exact_mod_cast x.lo.den_pos.ne'
    have h₁ : (x.hi.den : ℚ) ≠ 0 := by exact_mod_cast x.hi.den_pos.ne'
    cases x with
    | mk l r =>
      change RatBounds.mk _ _ = RatBounds.mk _ _
      congr 1
      · simp only [lower, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at *
        exact (show _ = (l.num : ℚ) / l.den by field_simp).trans (Rat.num_div_den l)
      · simp only [upper, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at *
        exact (show _ = (r.num : ℚ) / r.den by field_simp).trans (Rat.num_div_den r)

@[simp] theorem add_toBounds (a b : CommonDen) :
    (a.add b).toBounds = a.toBounds.add b.toBounds := by
  unfold add
  split
  · rename_i h
    simp [toBounds, lower, upper, RatBounds.add, h, add_div]
  · have ha := dne a
    have hb := dne b
    simp only [toBounds, lower, upper, RatBounds.add, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul, RatBounds.mk.injEq]
    constructor <;> field_simp

@[simp] theorem sub_toBounds (a b : CommonDen) :
    (a.sub b).toBounds = a.toBounds.sub b.toBounds := by
  unfold sub
  split
  · rename_i h
    simp [toBounds, lower, upper, RatBounds.sub, h, sub_div]
  · have ha := dne a
    have hb := dne b
    simp only [toBounds, lower, upper, RatBounds.sub, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul, RatBounds.mk.injEq]
    constructor <;> field_simp

@[simp] theorem mul_toBounds (a b : CommonDen) :
    (a.mul b).toBounds = a.toBounds.mul b.toBounds := by
  have hd : (0 : ℚ) ≤ (a.den : ℚ) * b.den := by positivity
  simp only [mul, toBounds, lower, upper, RatBounds.mul, Int.cast_min, Int.cast_max,
    Int.cast_mul, Nat.cast_mul, div_mul_div_comm, min_div_div_right hd, max_div_div_right hd]

@[simp] theorem abs_toBounds (a : CommonDen) : a.abs.toBounds = absBounds a.toBounds := by
  have hd : (0 : ℚ) ≤ a.den := by positivity
  have h : (0 : ℚ) / a.den = 0 := zero_div _
  simp only [CommonDen.abs, absBounds, toBounds, lower, upper, Int.cast_max, Int.cast_neg,
    Int.cast_zero, Int.cast_abs, abs_div, abs_of_nonneg hd, ← neg_div,
    max_div_div_right hd, RatBounds.mk.injEq]
  exact ⟨by rw [← h, max_div_div_right hd]; simp, True.intro⟩

@[simp] theorem posPow_toBounds (a : CommonDen) (n : ℕ) :
    (a.posPow n).toBounds = G3P.posPow a.toBounds n := by
  simp [posPow, G3P.posPow, toBounds, lower, upper, div_pow]

@[simp] theorem evenPow_toBounds (a : CommonDen) (n : ℕ) :
    (a.evenPow n).toBounds = G3P.evenPow a.toBounds n := by simp [evenPow, G3P.evenPow]

end CommonDen

theorem nearTermsCommon_eq (B : Box) (positive : Bool) (w : RowWitness) :
    nearTermsCommon B positive w = nearTerms B positive w := by
  have lo (x : CommonDen) : x.lower = x.toBounds.lo := rfl
  have hi (x : CommonDen) : x.upper = x.toBounds.hi := rfl
  simp only [nearTermsCommon, nearTerms, lo, hi, CommonDen.mul_toBounds, CommonDen.sub_toBounds,
    CommonDen.add_toBounds, CommonDen.posPow_toBounds, CommonDen.evenPow_toBounds,
    CommonDen.abs_toBounds, CommonDen.ofBounds_toBounds, CommonDen.ofRat_toBounds]

theorem rowQuadCommon_eq (B : Box) (positive : Bool) (w : RowWitness) :
    rowQuadCommon B positive w = rowQuad B positive w := by
  cases h : w.far <;> simp [rowQuadCommon, rowQuad, adjustedLeading, h, nearTermsCommon_eq]

theorem CertTree.commonOK_eq (t : CertTree) (B : Box) (b : Bool) : t.commonOK B b = t.ok B b := by
  induction t generalizing B with
  | cone | empty => rfl
  | row w => simp [commonOK, ok, rowOKCommon, rowOK, rowQuadCommon_eq]
  | cut j m l r hl hr => simp only [commonOK, ok, hl, hr]

theorem CertTree.ok_of_commonOK {t : CertTree} {B : Box} {b : Bool}
    (h : t.commonOK B b = true) : t.ok B b = true :=
  (t.commonOK_eq B b).symm.trans h

end HlawkaSchatten.BelowExponent.G3P
