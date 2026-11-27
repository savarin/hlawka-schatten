/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.VertexBox
import all HlawkaSchatten.BelowExponent.Interpolation
import Batteries.Tactic.OpenPrivate

/-! Chord and midpoint tangent minorants for the two powers on an outer row face. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open Set
open private abs_rpow_lerp_le from HlawkaSchatten.BelowExponent.Interpolation

noncomputable section

def cornerAbsMinorant (q c lo hi : ℝ) (i : Bool) : ℝ :=
  let x := chooseCorner i lo hi
  let m := (lo+hi)/2
  if 0 ≤ c then c * (|m|^q + q*(x-m)*signedPower q m) else c*|x|^q

theorem cornerAbsMinorant_le {q c lo hi t : ℝ} (hq : 1 < q) (ht : t ∈ Icc 0 1) :
    interpolate t (cornerAbsMinorant q c lo hi false) (cornerAbsMinorant q c lo hi true) ≤
      c*|interpolate t lo hi|^q := by
  by_cases hc : 0 ≤ c
  · simp only [cornerAbsMinorant, chooseCorner, Bool.false_eq_true, ite_false, ite_true, ite_eq_left hc]
    have he :
        interpolate t (c*(|(lo+hi)/2|^q+q*(lo-(lo+hi)/2)*signedPower q ((lo+hi)/2)))
          (c*(|(lo+hi)/2|^q+q*(hi-(lo+hi)/2)*signedPower q ((lo+hi)/2))) =
        c*(|(lo+hi)/2|^q+q*(interpolate t lo hi-(lo+hi)/2)*signedPower q ((lo+hi)/2)) := by
      unfold interpolate
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (tangent_signed hq _ _) hc
  · simp only [cornerAbsMinorant, chooseCorner, Bool.false_eq_true, ite_false, ite_true, ite_eq_right hc]
    have h := mul_le_mul_of_nonpos_left (abs_rpow_lerp_le hq.le ht.1 ht.2 lo hi) (le_of_not_ge hc)
    convert h using 1
    · unfold interpolate
      ring
    · rfl

private theorem rpow_le_concave_tangent {r m y : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hm : 0 < m) (hy : 0 ≤ y) :
    y^r ≤ m^r + (r*m^(r-1))*(y-m) := by
  have hconcave := Real.concaveOn_rpow hr₀ hr₁
  have hderiv := Real.hasDerivAt_rpow_const (x := m) (p := r) (Or.inl hm.ne')
  have hm' : m ∈ Ici (0 : ℝ) := hm.le
  have hy' : y ∈ Ici (0 : ℝ) := hy
  rcases lt_trichotomy y m with hlt | rfl | hgt
  · have h := hconcave.le_slope_of_hasDerivAt hy' hm' hlt hderiv
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith only [h']
  · simp
  · have h := hconcave.slope_le_of_hasDerivAt hm' hy' hgt hderiv
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith only [h']

/-- The argument and midpoint are the magnitudes on one closed sign interval. -/
def concavePowerMinorant (r c m x : ℝ) : ℝ :=
  if c < 0 then c * (m^r + r*m^(r-1)*(x-m)) else c*x^r

private theorem concavePowerMinorant_le {r c lo hi m t : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hl : 0 ≤ lo) (hh : 0 ≤ hi) (hm : 0 < m) (ht : t ∈ Icc 0 1) :
    interpolate t (concavePowerMinorant r c m lo) (concavePowerMinorant r c m hi) ≤
      c*(interpolate t lo hi)^r := by
  by_cases hc : c < 0
  · have hx : 0 ≤ interpolate t lo hi :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hl) (mul_nonneg ht.1 hh)
    have h := mul_le_mul_of_nonpos_left (rpow_le_concave_tangent hr₀ hr₁ hm hx) hc.le
    simp only [concavePowerMinorant, ite_eq_left hc]
    convert h using 1
    unfold interpolate
    ring
  · have hconc := (Real.concaveOn_rpow hr₀ hr₁).2 (mem_Ici.mpr hl) (mem_Ici.mpr hh)
        (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    have hchord : interpolate t (lo^r) (hi^r) ≤ (interpolate t lo hi)^r := by
      simpa only [interpolate, smul_eq_mul] using hconc
    have h' := mul_le_mul_of_nonneg_left hchord (le_of_not_gt hc)
    simp only [concavePowerMinorant, ite_eq_right hc]
    convert h' using 1
    unfold interpolate
    ring

def cornerSignedMinorant (q c lo hi : ℝ) (i : Bool) : ℝ :=
  let x := chooseCorner i lo hi
  if 0 ≤ lo then concavePowerMinorant (q-1) c ((lo+hi)/2) x
  else concavePowerMinorant (q-1) (-c) (-(lo+hi)/2) (-x)

theorem signedPower_eq_neg_rpow {q x : ℝ} (hq : 1 < q) (hx : x ≤ 0) :
    signedPower q x = -((-x)^(q-1)) := by
  rcases hx.eq_or_lt with rfl | hneg
  · simp [signedPower, Real.zero_rpow (sub_pos.mpr hq).ne']
  · simp [signedPower, not_le.mpr hneg, abs_of_neg hneg]

theorem cornerSignedMinorant_le {q c lo hi t : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hwidth : lo < hi) (hs : 0 ≤ lo ∨ hi ≤ 0) (ht : t ∈ Icc 0 1) :
    interpolate t (cornerSignedMinorant q c lo hi false) (cornerSignedMinorant q c lo hi true) ≤
      c*signedPower q (interpolate t lo hi) := by
  have hr₀ : 0 ≤ q-1 := sub_nonneg.mpr hq.le
  have hr₁ : q-1 ≤ 1 := by linarith only [hq₂]
  by_cases hpos : 0 ≤ lo
  · have hx : 0 ≤ interpolate t lo hi :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hpos) (mul_nonneg ht.1 (hpos.trans hwidth.le))
    simp only [cornerSignedMinorant, ite_eq_left hpos, chooseCorner, Bool.false_eq_true, ite_false, ite_true,
      signedPower, ite_eq_left hx, abs_of_nonneg hx]
    exact concavePowerMinorant_le hr₀ hr₁ hpos (hpos.trans hwidth.le) (by linarith only [hpos, hwidth]) ht
  · have hn : hi ≤ 0 := hs.resolve_left hpos
    have hx : interpolate t lo hi ≤ 0 :=
      add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (hwidth.le.trans hn))
        (mul_nonpos_of_nonneg_of_nonpos ht.1 hn)
    simp only [cornerSignedMinorant, ite_eq_right hpos, chooseCorner, Bool.false_eq_true, ite_false, ite_true,
      signedPower_eq_neg_rpow hq hx]
    have h := concavePowerMinorant_le (m := -(lo+hi)/2) (c := -c) (t := t) hr₀ hr₁
      (neg_nonneg.mpr (hwidth.le.trans hn)) (neg_nonneg.mpr hn) (by linarith only [hwidth, hn]) ht
    have he : interpolate t (-lo) (-hi) = -(interpolate t lo hi) := by unfold interpolate; ring
    rw [he] at h
    simpa only [neg_mul, mul_neg] using h

theorem signedCoefficient_mul_le {q proposed actual lo hi x : ℝ} (hq : 1 < q)
    (hx : x ∈ Icc lo hi) (hs : 0 ≤ lo ∨ hi ≤ 0)
    (hc : if 0 ≤ lo then proposed ≤ actual else actual ≤ proposed) :
    proposed*signedPower q x ≤ actual*signedPower q x := by
  by_cases hpos : 0 ≤ lo
  · have hx' := hpos.trans hx.1
    simp only [ite_eq_left hpos] at hc
    simp only [signedPower, ite_eq_left hx', abs_of_nonneg hx']
    exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx' _)
  · have hx' := hx.2.trans (hs.resolve_left hpos)
    simp only [ite_eq_right hpos] at hc
    rw [signedPower_eq_neg_rpow hq hx']
    exact mul_le_mul_of_nonpos_right hc (neg_nonpos.mpr (Real.rpow_nonneg (neg_nonneg.mpr hx') _))

end

end HlawkaSchatten.BelowExponent.Vertex
