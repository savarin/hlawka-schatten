/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonKernelData
public import HlawkaSchatten.BelowExponent.G3PowerCoreSound
public import HlawkaSchatten.BelowExponent.G3PCommonDenSound
import Mathlib.Tactic

/-! Exact equality to the common interval and quadratic specifications. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

/-- A direct `Bool.rec` branch is the `if` on its Boolean test. -/
theorem boolRec_eq_ite {α : Sort _} (c : Bool) (x y : α) :
    (Bool.rec y x c : α) = if c = true then x else y := by
  cases c <;> simp

/-- The Boolean denominator test of the kernel forms selects the same branch as the Prop test. -/
theorem rec_natBeq {α : Sort _} (a b : Nat) (x y : α) :
    (Bool.rec y x (Nat.beq a b) : α) = if a = b then x else y := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

namespace CommonDen.Kernel

theorem minInt_eq (a b : Int) : minInt a b = min a b := by
  unfold minInt
  cases h : Int.ble' a b with
  | false =>
    have hab : b ≤ a := le_of_not_ge ((Int.ble'_eq_false a b) ▸ h)
    exact (min_eq_right hab).symm
  | true =>
    have hab : a ≤ b := (Int.ble'_eq_true a b) ▸ h
    exact (min_eq_left hab).symm

theorem maxInt_eq (a b : Int) : maxInt a b = max a b := by
  unfold maxInt
  cases h : Int.ble' a b with
  | false =>
    have hab : b ≤ a := le_of_not_ge ((Int.ble'_eq_false a b) ▸ h)
    exact (max_eq_left hab).symm
  | true =>
    have hab : a ≤ b := (Int.ble'_eq_true a b) ▸ h
    exact (max_eq_right hab).symm

theorem absInt_eq (a : Int) : absInt a = |a| := by
  simp only [absInt, Int.natAbs_k_eq, Int.natCast_natAbs]

theorem ofBounds_eq (x : Vertex.RatBounds) : ofBounds x = CommonDen.ofBounds x := by
  simp only [ofBounds, CommonDen.ofBounds, Int.mul_k_eq, rec_natBeq]; rfl

theorem add_eq (a b : CommonDen) : add a b = a.add b := by
  simp only [add, CommonDen.add, Int.add_k_eq, Int.mul_k_eq, rec_natBeq]; rfl

theorem sub_eq (a b : CommonDen) : sub a b = a.sub b := by
  simp only [sub, CommonDen.sub, Int.sub_k_eq, Int.mul_k_eq, rec_natBeq]; rfl

theorem nonnegInt_eq (x : Int) : nonnegInt x = decide (0 ≤ x) := by
  cases x with
  | ofNat n => simp [nonnegInt]
  | negSucc n => simp [nonnegInt]

theorem nonposInt_eq (x : Int) : nonposInt x = decide (x ≤ 0) := by
  cases x with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ m =>
      have h : ¬ (Int.ofNat (m + 1) ≤ 0) := by rw [Int.ofNat_eq_natCast]; omega
      exact (decide_eq_false h).symm
  | negSucc n => exact (decide_eq_true (le_of_lt (Int.negSucc_lt_zero n))).symm

private theorem mulk_eq_mul (a b : Int) : Int.mul_k a b = a * b := by rw [Int.mul_k_eq]; rfl

private theorem min4_eq {aa ab ba bb x : Int} (h1 : x ≤ aa) (h2 : x ≤ ab) (h3 : x ≤ ba)
    (h4 : x ≤ bb) (hx : x = aa ∨ x = ab ∨ x = ba ∨ x = bb) :
    min (min aa ab) (min ba bb) = x := by
  apply le_antisymm _ (le_min (le_min h1 h2) (le_min h3 h4))
  rcases hx with rfl | rfl | rfl | rfl <;> simp

private theorem max4_eq {aa ab ba bb x : Int} (h1 : aa ≤ x) (h2 : ab ≤ x) (h3 : ba ≤ x)
    (h4 : bb ≤ x) (hx : x = aa ∨ x = ab ∨ x = ba ∨ x = bb) :
    max (max aa ab) (max ba bb) = x := by
  apply le_antisymm (max_le (max_le h1 h2) (max_le h3 h4))
  rcases hx with rfl | rfl | rfl | rfl <;> simp

private theorem mk_eq_mul {a b : CommonDen} {x y : Int} {h : 0 < Nat.mul a.den b.den}
    (hx : min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)) = x)
    (hy : max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi)) = y) :
    (⟨x, y, Nat.mul a.den b.den, h⟩ : CommonDen) = a.mul b := by
  simp only [CommonDen.mul, hx, hy]; rfl

theorem mul_eq (a b : CommonDen) : mul a b = a.mul b := by
  have hg : mulGeneral a b = a.mul b := by
    simp only [mulGeneral, CommonDen.mul, Int.mul_k_eq, minInt_eq, maxInt_eq]; rfl
  unfold mul
  cases hA : Int.ble' a.lo a.hi
  · exact hg
  cases hB : Int.ble' b.lo b.hi
  · exact hg
  have h3 : a.lo ≤ a.hi := by simpa using hA
  have h4 : b.lo ≤ b.hi := by simpa using hB
  show mulOrdered a b = a.mul b
  unfold mulOrdered
  cases hal : nonnegInt a.lo
  · have hal' : a.lo < 0 := by rw [nonnegInt_eq] at hal; simpa using hal
    cases hah : nonposInt a.hi
    · have hah' : 0 < a.hi := by rw [nonposInt_eq] at hah; simpa using hah
      cases hbl : nonnegInt b.lo
      · cases hbh : nonposInt b.hi
        · exact hg
        · have hbh' : b.hi ≤ 0 := by rw [nonposInt_eq] at hbh; simpa using hbh
          simp only [mulk_eq_mul]
          exact mk_eq_mul (min4_eq (by nlinarith) (by nlinarith) le_rfl (by nlinarith) (by simp))
            (max4_eq le_rfl (by nlinarith) (by nlinarith) (by nlinarith) (by simp))
      · have hbl' : 0 ≤ b.lo := by rw [nonnegInt_eq] at hbl; simpa using hbl
        simp only [mulk_eq_mul]
        exact mk_eq_mul (min4_eq (by nlinarith) le_rfl (by nlinarith) (by nlinarith) (by simp))
          (max4_eq (by nlinarith) (by nlinarith) (by nlinarith) le_rfl (by simp))
    · have hah' : a.hi ≤ 0 := by rw [nonposInt_eq] at hah; simpa using hah
      simp only [mulk_eq_mul, boolRec_eq_ite, nonnegInt_eq, decide_eq_true_eq]
      apply mk_eq_mul
      · split_ifs with hb
        · exact min4_eq (by nlinarith) le_rfl (by nlinarith) (by nlinarith) (by simp)
        · exact min4_eq (by nlinarith) (by nlinarith) (by nlinarith) le_rfl (by simp)
      · split_ifs with hb
        · exact max4_eq (by nlinarith) (by nlinarith) le_rfl (by nlinarith) (by simp)
        · exact max4_eq le_rfl (by nlinarith) (by nlinarith) (by nlinarith) (by simp)
  · have hal' : 0 ≤ a.lo := by rw [nonnegInt_eq] at hal; simpa using hal
    simp only [mulk_eq_mul, boolRec_eq_ite, nonnegInt_eq, decide_eq_true_eq]
    apply mk_eq_mul
    · split_ifs with hb
      · exact min4_eq le_rfl (by nlinarith) (by nlinarith) (by nlinarith) (by simp)
      · exact min4_eq (by nlinarith) (by nlinarith) le_rfl (by nlinarith) (by simp)
    · split_ifs with hb
      · exact max4_eq (by nlinarith) (by nlinarith) (by nlinarith) le_rfl (by simp)
      · exact max4_eq (by nlinarith) le_rfl (by nlinarith) (by nlinarith) (by simp)

theorem abs_eq (a : CommonDen) : abs a = a.abs := by
  simp only [abs, CommonDen.abs, Int.neg_k_eq, absInt_eq, maxInt_eq]; rfl

theorem posPow_eq (a : CommonDen) (n : Nat) : posPow a n = a.posPow n := by
  simp only [posPow, CommonDen.posPow, Int.pow_k_eq, Nat.pow_eq]

theorem evenPow_eq (a : CommonDen) (n : Nat) : evenPow a n = a.evenPow n := by
  simp only [evenPow, CommonDen.evenPow, abs_eq, posPow_eq]

end CommonDen.Kernel

private theorem CommonDen.mul_zero_upper (a : CommonDen) :
    (a.mul (CommonDen.ofRat 0)).upper = 0 := by
  simp [CommonDen.mul, CommonDen.ofRat, CommonDen.upper]

theorem tailKernel_eq (b W U : CommonDen) : tailKernel b W U =
    ((((b.mul (CommonDen.ofBounds remScale)).mul (W.abs.posPow 5)).mul
      (CommonDen.ofRat (max 0 (W.abs.upper-U.lower)))).upper) := by
  unfold tailKernel
  simp only [CommonDen.Kernel.abs_eq, CommonDen.Kernel.mul_eq,
    CommonDen.Kernel.ofBounds_eq, CommonDen.Kernel.posPow_eq, Int.mul_k_eq]
  split
  · rename_i h
    have hi : W.abs.hi*(U.den : Int) ≤ U.lo*(W.abs.den : Int) :=
      (Int.ble'_eq_true _ _) ▸ h
    have hg : W.abs.upper ≤ U.lower := by
      unfold CommonDen.upper CommonDen.lower
      rw [div_le_div_iff₀ (by exact_mod_cast W.abs.den_pos)
        (by exact_mod_cast U.den_pos)]
      exact_mod_cast hi
    rw [max_eq_left (sub_nonpos.mpr hg), CommonDen.mul_zero_upper]
  · rfl

theorem nearTermsKernel_eq (B : Box) (positive : Bool) (w : RowWitness) :
    nearTermsKernel B positive w = nearTermsCommon B positive w := by
  simp only [nearTermsKernel, nearTermsCommon, CommonDen.Kernel.ofBounds_eq,
    CommonDen.Kernel.mul_eq, CommonDen.Kernel.add_eq, CommonDen.Kernel.sub_eq,
    CommonDen.Kernel.evenPow_eq, tailKernel_eq]

namespace RawScalar

private theorem intAdd_spec (a b : Int) : Int.add_k a b = a+b := by
  rw [Int.add_k_eq]
  rfl

private theorem intMul_spec (a b : Int) : Int.mul_k a b = a*b := by
  rw [Int.mul_k_eq]
  rfl

@[simp] theorem value_ofRat (a : ℚ) : (ofRat a).value = a := by
  exact Rat.num_div_den a

@[simp] theorem value_lower (a : CommonDen) : (lower a).value = a.lower := rfl

@[simp] theorem value_upper (a : CommonDen) : (upper a).value = a.upper := rfl

@[simp] theorem value_add (a b : RawScalar) : (add a b).value = a.value+b.value := by
  unfold add
  rw [rec_natBeq]
  split
  · rename_i h
    simp only [value, intAdd_spec, Int.cast_add, h, add_div]
  · have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
    have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
    simp only [value, intAdd_spec, intMul_spec, Int.cast_add, Int.cast_mul,
      Int.ofNat_eq_natCast, Nat.mul_eq, Int.cast_natCast, Nat.cast_mul]
    field_simp

@[simp] theorem value_sub (a b : RawScalar) : (sub a b).value = a.value-b.value := by
  unfold sub
  rw [rec_natBeq]
  split
  · rename_i h
    simp only [value, Int.sub_k_eq, Int.cast_sub, h, sub_div]
  · have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
    have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
    simp only [value, Int.sub_k_eq, intMul_spec, Int.cast_sub, Int.cast_mul,
      Int.ofNat_eq_natCast, Nat.mul_eq, Int.cast_natCast, Nat.cast_mul]
    field_simp

@[simp] theorem value_mul (a b : RawScalar) : (mul a b).value = a.value*b.value := by
  simp only [mul, value, intMul_spec, Int.cast_mul, Nat.mul_eq, Nat.cast_mul, div_mul_div_comm]

@[simp] theorem value_pow (a : RawScalar) (n : Nat) : (pow a n).value = a.value^n := by
  simp only [pow, value, Int.pow_k_eq, Int.cast_pow, Nat.pow_eq, Nat.cast_pow, div_pow]

theorem toQuad_scale_pos (a b c : RawScalar) : 0 < (toQuad a b c).scale :=
  Nat.mul_pos (Nat.mul_pos a.den_pos b.den_pos) c.den_pos

theorem toQuad_a (a b c : RawScalar) :
    ((toQuad a b c).a : ℚ)/(toQuad a b c).scale = a.value := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  have hc : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
  simp only [toQuad, value, intMul_spec, Int.cast_mul, Int.ofNat_eq_natCast, Nat.mul_eq,
    Int.cast_natCast, Nat.cast_mul]
  field_simp

theorem toQuad_b (a b c : RawScalar) :
    ((toQuad a b c).b : ℚ)/(toQuad a b c).scale = b.value := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  have hc : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
  simp only [toQuad, value, intMul_spec, Int.cast_mul, Int.ofNat_eq_natCast, Nat.mul_eq,
    Int.cast_natCast, Nat.cast_mul]
  field_simp

theorem toQuad_c (a b c : RawScalar) :
    ((toQuad a b c).c : ℚ)/(toQuad a b c).scale = c.value := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  have hc : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
  simp only [toQuad, value, intMul_spec, Int.cast_mul, Int.ofNat_eq_natCast, Nat.mul_eq,
    Int.cast_natCast, Nat.cast_mul]
  field_simp

end RawScalar

namespace RawQuad

theorem scaled_ok (q : Quad) (n : Nat) (hn : 0 < n) : (scaled q n).ok = q.ok := by
  unfold Quad.ok
  apply decide_eq_decide.mpr
  dsimp only [scaled]
  have hN : (0 : Int) < n := by exact_mod_cast hn
  have hle (a b : Int) : (n : Int)*a ≤ (n : Int)*b ↔ a ≤ b :=
    mul_le_mul_iff_of_pos_left hN
  have hlt (a b : Int) : (n : Int)*a < (n : Int)*b ↔ a < b :=
    mul_lt_mul_iff_of_pos_left hN
  have hc : (0 : Int) ≤ (n : Int)*q.c ↔ 0 ≤ q.c := by
    simpa only [mul_zero] using hle 0 q.c
  have ha : (0 : Int) < (n : Int)*q.a ↔ 0 < q.a := by
    simpa only [mul_zero] using hlt 0 q.a
  have hb : (n : Int)*q.b < 0 ↔ q.b < 0 := by
    simpa only [mul_zero] using hlt q.b 0
  have hbound : -2*((n : Int)*q.a) < (n : Int)*q.b ↔ -2*q.a < q.b := by
    rw [show -2*((n : Int)*q.a) = (n : Int)*(-2*q.a) by ring]
    exact hlt _ _
  have hsum : (n : Int)*q.a + (n : Int)*q.b + (n : Int)*q.c =
      (n : Int)*(q.a+q.b+q.c) := by ring
  have hsum0 : (0 : Int) ≤ (n : Int)*(q.a+q.b+q.c) ↔ 0 ≤ q.a+q.b+q.c := by
    simpa only [mul_zero] using hle 0 (q.a+q.b+q.c)
  have hdisc : 4*((n : Int)*q.a)*((n : Int)*q.c) - ((n : Int)*q.b)^2 =
      (n : Int)^2*(4*q.a*q.c-q.b^2) := by ring
  have hdisc0 : (0 : Int) ≤ (n : Int)^2*(4*q.a*q.c-q.b^2) ↔ 0 ≤ 4*q.a*q.c-q.b^2 := by
    simpa only [mul_zero] using
      (mul_le_mul_iff_of_pos_left (pow_pos hN 2) (b := 0) (c := 4*q.a*q.c-q.b^2))
  simp only [Nat.mul_pos_iff_of_pos_left hn, hc, ha, hb, hbound, hsum, hsum0, hdisc, hdisc0]

theorem ok_of_cross (q r : Quad) (hq : 0 < q.scale) (hr : 0 < r.scale)
    (ha : q.a*(r.scale : Int) = r.a*(q.scale : Int))
    (hb : q.b*(r.scale : Int) = r.b*(q.scale : Int))
    (hc : q.c*(r.scale : Int) = r.c*(q.scale : Int)) : q.ok = r.ok := by
  have hs : scaled q r.scale = scaled r q.scale := by
    cases q
    cases r
    simp_all [scaled, Int.mul_comm, Nat.mul_comm]
  calc
    q.ok = (scaled q r.scale).ok := (scaled_ok q r.scale hr).symm
    _ = (scaled r q.scale).ok := congrArg Quad.ok hs
    _ = r.ok := scaled_ok r q.scale hq

theorem ok_of_value (q r : Quad) (hq : 0 < q.scale) (hr : 0 < r.scale)
    (ha : (q.a : ℚ)/q.scale = (r.a : ℚ)/r.scale)
    (hb : (q.b : ℚ)/q.scale = (r.b : ℚ)/r.scale)
    (hc : (q.c : ℚ)/q.scale = (r.c : ℚ)/r.scale) : q.ok = r.ok := by
  have hq0 : (q.scale : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (r.scale : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  apply ok_of_cross q r hq hr
  · have h := (div_eq_div_iff hq0 hr0).mp ha
    exact_mod_cast h
  · have h := (div_eq_div_iff hq0 hr0).mp hb
    exact_mod_cast h
  · have h := (div_eq_div_iff hq0 hr0).mp hc
    exact_mod_cast h

end RawQuad

theorem Quad.kernelOK_eq (q : Quad) : q.kernelOK = q.ok := by
  apply Bool.eq_iff_iff.mpr
  simp [Quad.kernelOK, Quad.ok, Int.sub_k_eq, Int.pow_k_eq, Nat.blt_eq]
  tauto

namespace RawScalar

theorem toQuad_ofRat (a b c : ℚ) : toQuad (ofRat a) (ofRat b) (ofRat c) = clearDen a b c := by
  simp only [toQuad, ofRat, clearDen, intMul_spec, Int.ofNat_eq_natCast, Nat.mul_eq]

theorem toQuad_ok_congr (a b c d e f : RawScalar)
    (ha : a.value = d.value) (hb : b.value = e.value) (hc : c.value = f.value) :
    (toQuad a b c).ok = (toQuad d e f).ok := by
  apply RawQuad.ok_of_value _ _ (toQuad_scale_pos a b c) (toQuad_scale_pos d e f)
  · rw [toQuad_a, toQuad_a, ha]
  · rw [toQuad_b, toQuad_b, hb]
  · rw [toQuad_c, toQuad_c, hc]

theorem toQuad_ok (a b c : RawScalar) :
    (toQuad a b c).ok = (clearDen a.value b.value c.value).ok := by
  rw [← toQuad_ofRat]
  apply toQuad_ok_congr <;> simp only [value_ofRat]

end RawScalar

namespace CommonDen.Kernel

theorem pointUpper_toBounds (a : CommonDen) : (pointUpper a).toBounds = point a.upper := rfl
theorem pointLower_toBounds (a : CommonDen) : (pointLower a).toBounds = point a.lower := rfl

theorem pointGap_toBounds (a b : CommonDen) :
    (pointGap a b).toBounds = point (a.upper-b.lower) := by
  simp only [pointGap, sub_eq, CommonDen.sub_toBounds, pointUpper_toBounds, pointLower_toBounds]
  rfl

end CommonDen.Kernel

private theorem abs_le_cross (W U : CommonDen) : W.abs.upper ≤ U.lower ↔
    W.abs.hi*(U.den : Int) ≤ U.lo*(W.abs.den : Int) := by
  unfold CommonDen.upper CommonDen.lower
  rw [div_le_div_iff₀ (by exact_mod_cast W.abs.den_pos) (by exact_mod_cast U.den_pos)]
  norm_cast

theorem tailRaw_value_eq (b W U : CommonDen) : (tailRaw b W U).value = tailKernel b W U := by
  rw [tailKernel_eq]
  unfold tailRaw
  simp only [boolRec_eq_ite, CommonDen.Kernel.abs_eq, RawScalar.intMul_spec, Int.ofNat_eq_natCast,
    Int.ble'_eq_true]
  split
  · rename_i h
    have hg : W.abs.upper ≤ U.lower := (abs_le_cross W U).mpr h
    rw [max_eq_left (sub_nonpos.mpr hg), CommonDen.mul_zero_upper]
    exact RawScalar.value_ofRat 0
  · rename_i h
    have hg : 0 ≤ W.abs.upper-U.lower := sub_nonneg.mpr
      (le_of_not_ge (fun hle => h ((abs_le_cross W U).mp hle)))
    rw [max_eq_right hg]
    simp only [CommonDen.Kernel.mul_eq, CommonDen.Kernel.ofBounds_eq,
      CommonDen.Kernel.posPow_eq, RawScalar.value_upper]
    let T := (b.mul (CommonDen.ofBounds remScale)).mul (W.abs.posPow 5)
    change (T.mul (CommonDen.Kernel.pointGap W.abs U)).toBounds.hi =
      (T.mul (CommonDen.ofRat (W.abs.upper-U.lower))).toBounds.hi
    rw [CommonDen.mul_toBounds T (CommonDen.Kernel.pointGap W.abs U),
      CommonDen.mul_toBounds T (CommonDen.ofRat (W.abs.upper-U.lower)),
      CommonDen.Kernel.pointGap_toBounds, CommonDen.ofRat_toBounds]

theorem nearTermsRaw_value_eq (B : Box) (positive : Bool) (w : RowWitness) :
    (nearTermsRaw B positive w).value = nearTermsKernel B positive w := by
  simp only [nearTermsRaw, RawLowerPolynomial.value, RawScalar.value_sub,
    RawScalar.value_lower, RawScalar.value_upper, tailRaw_value_eq, nearTermsKernel]

theorem RawLowerPolynomial.quad_ok_eq (p : RawLowerPolynomial)
    (adjustment u width p0 p1 : RawScalar) :
    (p.quad adjustment u width p0 p1).ok =
    (clearDen ((p.value.squared-adjustment.value)*width.value^2)
      ((2*(p.value.squared-adjustment.value)*u.value-p.value.linearCost)*width.value -
        (p1.value-p0.value))
      ((p.value.squared-adjustment.value)*u.value^2-p.value.linearCost*u.value+
        p.value.constant-p0.value)).ok := by
  simp only [RawLowerPolynomial.quad, RawScalar.toQuad_ok, RawScalar.value_sub,
    RawScalar.value_add, RawScalar.value_mul, RawScalar.value_pow, RawScalar.value_ofRat,
    RawLowerPolynomial.value]

theorem rowQuadRaw_ok_eq (B : Box) (positive : Bool) (w : RowWitness) :
    (rowQuadRaw B positive w).ok = (rowQuadCommon B positive w).ok := by
  cases hw : w.far <;>
    simp only [rowQuadRaw, rowQuadCommon, hw, RawLowerPolynomial.quad_ok_eq,
      RawScalar.value_sub, RawScalar.value_ofRat, nearTermsRaw_value_eq, nearTermsKernel_eq,
      sub_zero]

theorem rowOKKernel_eq (B : Box) (positive : Bool) (w : RowWitness) :
    rowOKKernel B positive w = rowOKCommon B positive w := by
  simp only [rowOKKernel, rowOKCommon, rowQuadKernel, Quad.kernelOK_eq, rowQuadRaw_ok_eq,
    G3Power.Kernel.crossIntLE_rat_eq]

theorem CertTree.kernelOK_eq (t : CertTree) (B : Box) (positive : Bool) :
    t.kernelOK B positive = t.commonOK B positive := by
  induction t generalizing B with
  | cone | empty => rfl
  | row w => exact rowOKKernel_eq B positive w
  | cut j knot l r hl hr => simp only [kernelOK, commonOK, hl, hr]

theorem CertTree.commonOK_of_kernelOK {t : CertTree} {B : Box} {positive : Bool}
    (h : t.kernelOK B positive = true) : t.commonOK B positive = true :=
  (t.kernelOK_eq B positive).symm.trans h

theorem CertTree.kernelCut_ok {B : Box} {positive : Bool} {j : Fin 4} {knot : ℚ}
    {a b : CertTree} (hl : a.kernelOK (B.lowerChild j knot) positive = true)
    (hu : b.kernelOK (B.upperChild j knot) positive = true) :
    (CertTree.cut j knot a b).kernelOK B positive = true := by
  simp only [CertTree.kernelOK, hl, hu, Bool.and_self]

end

end HlawkaSchatten.BelowExponent.G3P
