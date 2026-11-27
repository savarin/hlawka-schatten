/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck

/-! Fixed-point interval arithmetic for the VC and SC reflection. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

namespace DyadicBounds

noncomputable def decode (v : ℤ) : ℝ := (v : ℝ) / (units : ℝ)

def Contains (a : DyadicBounds) (x : ℝ) : Prop := a.ok = true → decode a.lo ≤ x ∧ x ≤ decode a.hi

private theorem units_pos : 0 < units := by decide

private theorem realUnits_pos : (0 : ℝ) < units := by exact_mod_cast units_pos

private theorem intUnits_pos : (0 : ℤ) < units := by exact_mod_cast units_pos

private theorem ratUnits_pos : (0 : ℚ) < units := by exact_mod_cast units_pos

private theorem decode_zero : decode 0 = 0 := by simp [decode]

theorem decode_mono : Monotone decode := fun _ _ h => div_le_div_of_nonneg_right (by exact_mod_cast h) realUnits_pos.le

theorem decode_pos {v : ℤ} (hv : 0 < v) : 0 < decode v := div_pos (by exact_mod_cast hv) realUnits_pos

private theorem decode_add (a b : ℤ) : decode (a+b) = decode a+decode b := by simp [decode, Int.cast_add, add_div]

private theorem decode_sub (a b : ℤ) : decode (a-b) = decode a-decode b := by simp [decode, Int.cast_sub, sub_div]

private theorem decode_neg (a : ℤ) : decode (-a) = -decode a := by simp [decode, neg_div]

private theorem decode_abs (a : ℤ) : decode |a| = |decode a| := by
  rw [abs_eq_max_neg, decode_mono.map_max, decode_neg, ← abs_eq_max_neg]

theorem ofRat_mem {a : RatBounds} {x : ℝ} (h : a.Contains x) : (ofRat a).Contains x := by
  have hlo : (⌊a.lo * (units : ℚ)⌋ : ℚ) / units ≤ a.lo := (div_le_iff₀ ratUnits_pos).2 (Int.floor_le _)
  have hhi : a.hi ≤ (⌈a.hi * (units : ℚ)⌉ : ℚ) / units := (le_div_iff₀ ratUnits_pos).2 (Int.le_ceil _)
  intro _
  rw [ofRat_def]
  exact ⟨(show decode (⌊a.lo * (units : ℚ)⌋) ≤ (a.lo : ℝ) by unfold decode; exact_mod_cast hlo).trans h.1,
    h.2.trans (show (a.hi : ℝ) ≤ decode (⌈a.hi * (units : ℚ)⌉) by unfold decode; exact_mod_cast hhi)⟩

theorem point_mem (q : ℚ) : (point q).Contains (q : ℝ) := ofRat_mem (RatBounds.point_mem q)

theorem numerator_mem (n : ℤ) : (ofNumerator n).Contains (decode n) := fun _ => ⟨le_rfl, le_rfl⟩

theorem Contains.require {a : DyadicBounds} {x : ℝ} (h : a.Contains x) (b : Bool) : (a.require b).Contains x :=
  fun hok => h (Bool.and_eq_true_iff.mp hok).1

theorem Contains.add {a b : DyadicBounds} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.add b).Contains (x+y) := by
  intro hok
  obtain ⟨ha', hb'⟩ := Bool.and_eq_true_iff.mp hok
  simpa only [DyadicBounds.add_def, decode_add] using
    And.intro (add_le_add (ha ha').1 (hb hb').1) (add_le_add (ha ha').2 (hb hb').2)

theorem Contains.sub {a b : DyadicBounds} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.sub b).Contains (x-y) := by
  intro hok
  obtain ⟨ha', hb'⟩ := Bool.and_eq_true_iff.mp hok
  simpa only [DyadicBounds.sub_def, decode_sub] using
    And.intro (sub_le_sub (ha ha').1 (hb hb').2) (sub_le_sub (ha ha').2 (hb hb').1)

private theorem le_ceil_mul (a : ℤ) {b : ℤ} (hb : b ≠ 0) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  rw [neg_mul, le_neg]
  linarith only [Int.ediv_mul_le (-a) hb]

private theorem floor_product {n a b : ℤ} (h : n ≤ a*b) : decode (n / units) ≤ decode a * decode b := by
  have hc : ((n / (units : ℤ) : ℤ) : ℝ) * (units : ℝ) ≤ (a : ℝ)*b := by
    exact_mod_cast (Int.ediv_mul_le n intUnits_pos.ne').trans h
  unfold decode
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ realUnits_pos (mul_pos realUnits_pos realUnits_pos)).2
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hc realUnits_pos.le

private theorem ceil_product {n a b : ℤ} (h : a*b ≤ n) : decode a * decode b ≤ decode (ceilDiv n units) := by
  have hc : (a : ℝ)*b ≤ (ceilDiv n units : ℝ) * (units : ℝ) := by
    exact_mod_cast h.trans (le_ceil_mul n intUnits_pos.ne')
  unfold decode
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos realUnits_pos realUnits_pos) realUnits_pos).2
  rw [← mul_assoc (ceilDiv n units : ℝ)]
  exact mul_le_mul_of_nonneg_right hc realUnits_pos.le

private theorem rat_decode (v : ℤ) : (((v : ℚ) / (units : ℚ) : ℚ) : ℝ) = decode v := by
  simp [decode, Rat.cast_div]

theorem Contains.mul {a b : DyadicBounds} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  rw [mul_def]
  intro hok
  obtain ⟨ha', hb'⟩ := Bool.and_eq_true_iff.mp hok
  have haR : (RatBounds.mk a.lower a.upper).Contains x := by
    simpa only [lower, upper, RatBounds.Contains, rat_decode] using ha ha'
  have hbR : (RatBounds.mk b.lower b.upper).Contains y := by
    simpa only [lower, upper, RatBounds.Contains, rat_decode] using hb hb'
  have hh := RatBounds.mul_mem haR hbR
  simp only [RatBounds.Contains, RatBounds.mul, Rat.cast_mul, Rat.cast_min, Rat.cast_max, lower, upper, rat_decode] at hh
  have hlo : ∀ {i j}, i*j ≥ productLo a b → decode (productLo a b / units) ≤ decode i * decode j :=
    fun h => floor_product h
  have hhi : ∀ {i j}, i*j ≤ productHi a b →
      decode i * decode j ≤ decode (ceilDiv (productHi a b) units) :=
    fun h => ceil_product h
  refine ⟨?_, ?_⟩
  · apply le_trans _ hh.1
    simp only [le_min_iff]
    exact ⟨⟨hlo (by simp [productLo]), hlo (by simp [productLo])⟩,
      ⟨hlo (by simp [productLo]), hlo (by simp [productLo])⟩⟩
  · apply le_trans hh.2
    simp only [max_le_iff]
    exact ⟨⟨hhi (by simp [productHi]), hhi (by simp [productHi])⟩,
      ⟨hhi (by simp [productHi]), hhi (by simp [productHi])⟩⟩

theorem Contains.abs {a : DyadicBounds} {x : ℝ} (ha : a.Contains x) : a.abs.Contains |x| := by
  intro hok
  obtain ⟨hx, hy⟩ := ha hok
  simp only [DyadicBounds.abs_def, decode_mono.map_max, decode_zero, decode_neg, decode_abs]
  refine ⟨max_le (abs_nonneg x) (max_le (hx.trans (le_abs_self x)) ((neg_le_neg hy).trans (neg_le_abs x))), ?_⟩
  exact abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hx),
    hy.trans ((le_abs_self _).trans (le_max_right _ _))⟩

theorem Contains.square {a : DyadicBounds} {x : ℝ} (ha : a.Contains x) : a.square.Contains (x^2) := by
  have h := ha.abs.mul ha.abs
  simpa only [DyadicBounds.square, ← pow_two, sq_abs] using h

theorem Contains.reciprocal {a : DyadicBounds} {x : ℝ} (ha : a.Contains x) : a.reciprocal.Contains (1/x) := by
  rw [reciprocal_def]
  intro hok
  obtain ⟨h, hlo⟩ := Bool.and_eq_true_iff.mp hok
  have hL := decode_pos (of_decide_eq_true hlo)
  have hx := hL.trans_le (ha h).1
  have hU := hx.trans_le (ha h).2
  have hi : 0 < a.hi := by
    have hh : (0 : ℝ) < a.hi := (div_pos_iff_of_pos_right realUnits_pos).1 hU
    exact_mod_cast hh
  have hcLo : (((((units : ℤ) * units) / a.hi : ℤ) : ℝ) * (a.hi : ℝ)) ≤ (units : ℝ) * units := by
    exact_mod_cast Int.ediv_mul_le ((units : ℤ) * units) hi.ne'
  have hcHi : (units : ℝ) * units ≤ (ceilDiv ((units : ℤ) * units) a.lo : ℝ) * (a.lo : ℝ) := by
    exact_mod_cast le_ceil_mul ((units : ℤ) * units) (of_decide_eq_true hlo : 0 < a.lo).ne'
  have hlo' : decode (((units : ℤ) * units) / a.hi) ≤ 1 / decode a.hi := by
    unfold decode
    rw [one_div_div]
    exact (div_le_div_iff₀ realUnits_pos (by exact_mod_cast hi)).2 hcLo
  have hhi' : 1 / decode a.lo ≤ decode (ceilDiv ((units : ℤ) * units) a.lo) := by
    unfold decode
    rw [one_div_div]
    exact (div_le_div_iff₀ (by exact_mod_cast (of_decide_eq_true hlo : 0 < a.lo)) realUnits_pos).2 hcHi
  exact ⟨hlo'.trans (one_div_le_one_div_of_le hx (ha h).2),
    (one_div_le_one_div_of_le hL (ha h).1).trans hhi'⟩

theorem Contains.div {a b : DyadicBounds} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.div b).Contains (x/y) := by
  simpa only [DyadicBounds.div, mul_one_div] using ha.mul hb.reciprocal

theorem Contains.intersect {a b : DyadicBounds} {x : ℝ} (ha : a.Contains x) (hb : b.Contains x) :
    (a.intersect b).Contains x := by
  intro hok
  obtain ⟨ha', hb'⟩ := Bool.and_eq_true_iff.mp hok
  simp only [DyadicBounds.intersect_def, decode_mono.map_max, decode_mono.map_min]
  exact ⟨max_le (ha ha').1 (hb hb').1, le_min (ha ha').2 (hb hb').2⟩

theorem Contains.le_upper {a : DyadicBounds} {x : ℝ} {q : ℚ} (h : a.Contains x) (hc : a.upperOK q = true) :
    x ≤ (q : ℝ) := by
  rw [upperOK_def] at hc
  obtain ⟨hok, hq⟩ := Bool.and_eq_true_iff.mp hc
  exact (h hok).2.trans (by
    simpa only [upper, rat_decode] using (show (a.upper : ℝ) ≤ q by exact_mod_cast of_decide_eq_true hq))

theorem Contains.lower_le {a : DyadicBounds} {x : ℝ} {q : ℚ} (h : a.Contains x) (hc : a.lowerOK q = true) :
    (q : ℝ) ≤ x := by
  rw [lowerOK_def] at hc
  obtain ⟨hok, hq⟩ := Bool.and_eq_true_iff.mp hc
  exact (show (q : ℝ) ≤ decode a.lo from by
    simpa only [lower, rat_decode] using (show (q : ℝ) ≤ a.lower by exact_mod_cast of_decide_eq_true hq)).trans (h hok).1

end DyadicBounds

end HlawkaSchatten.BelowExponent.Vertex
