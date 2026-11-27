/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PDivided
import all HlawkaSchatten.BelowExponent.G1Large
import Batteries.Tactic.OpenPrivate

/-! Cancellation between the two far secants in small-height central G3 boxes. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Set
open G3S (power)
open private absPower_deriv from HlawkaSchatten.BelowExponent.G1Large

noncomputable section

private theorem q_gt : 1 < criticalQ := by linarith only [criticalQ_bracket.1]

private theorem q_lt : criticalQ < 2 := by linarith only [criticalQ_bracket.2]

def slopePower (x : ℝ) : ℝ := criticalQ * x ^ (criticalQ - 1)

private theorem power_hasDeriv_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt power (slopePower x) x := by
  change HasDerivAt (fun y : ℝ => |y| ^ criticalQ) (slopePower x) x
  simpa [slopePower, hx, abs_of_nonneg hx] using absPower_deriv q_gt x

private theorem slopePower_concave : ConcaveOn ℝ (Ici 0) slopePower := by
  exact (Real.concaveOn_rpow (by linarith only [q_gt]) (by linarith only [q_lt])).smul
    (show 0 ≤ criticalQ by linarith only [q_gt])

theorem positiveSecant_midpoint {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    (power (a + h) - power a) / h ≤ criticalQ * (a + h / 2) ^ (criticalQ - 1) := by
  let m := a + h / 2
  let G (t : ℝ) := power (m + t) - power (m - t) - (2 * slopePower m) * t
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (h / 2)) :
      HasDerivAt G (slopePower (m + t) + slopePower (m - t) - 2 * slopePower m) t := by
    have hp : 0 ≤ m + t := by dsimp [m]; linarith only [ha, hh, ht.1]
    have hm : 0 ≤ m - t := by dsimp [m]; linarith only [ha, ht.2]
    have h₁ := (power_hasDeriv_of_nonneg hp).comp t ((hasDerivAt_id t).const_add m)
    have h₂ := (power_hasDeriv_of_nonneg hm).comp t ((hasDerivAt_id t).const_sub m)
    have h₃ := (hasDerivAt_id t).const_mul (2 * slopePower m)
    convert (h₁.sub h₂).sub h₃ using 1
    · rfl
    · ring
  have hanti : AntitoneOn G (Icc 0 (h / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    intro t ht
    have ht' := interior_subset ht
    rw [(hd t ht').deriv]
    have hp : 0 ≤ m + t := by dsimp [m]; linarith only [ha, hh, ht'.1]
    have hm : 0 ≤ m - t := by dsimp [m]; linarith only [ha, ht'.2]
    have hc := slopePower_concave.2 (mem_Ici.mpr hp) (mem_Ici.mpr hm)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simp only [smul_eq_mul, show (1/2 : ℝ) * (m+t) + (1/2) * (m-t) = m by ring] at hc
    linarith only [hc]
  have hb := hanti (show 0 ∈ Icc (0 : ℝ) (h/2) from ⟨le_rfl, by positivity⟩)
    (show h/2 ∈ Icc (0 : ℝ) (h/2) from ⟨by positivity, le_rfl⟩) (by positivity)
  dsimp [G] at hb
  rw [show m + h/2 = a+h by dsimp [m]; ring, show m-h/2=a by dsimp [m]; ring] at hb
  simp only [add_zero, sub_zero, sub_self, mul_zero] at hb
  change _ ≤ slopePower m
  exact (div_le_iff₀ hh).2 (by linarith only [hb])

def farMidpoint (a h : ℝ) : ℝ :=
  (power (a + h - 2) - power (a + h)) / 2 + slopePower (a + h / 2)

theorem far_div_le_midpoint {h Z s : ℝ} (hh : 0 < h) (hs : s ≠ 0)
    (ha : 0 ≤ Z/s) :
    balancedFarIncrement criticalQ (1 - h) Z s / h ≤ power s * farMidpoint (Z/s) h := by
  rw [far_div_eq hh.ne' hs]
  exact mul_le_mul_of_nonneg_left (add_le_add_right (positiveSecant_midpoint ha hh) _)
    (Real.rpow_nonneg (abs_nonneg _) _)

private theorem slopePower_diff_le {x y C : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hC : criticalQ * (criticalQ - 1) * x ^ (criticalQ - 2) ≤ C) :
    slopePower y - slopePower x ≤ C * (y - x) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hd (w : ℝ) (hw : w ∈ Ioo x y) :
      HasDerivAt slopePower (criticalQ * (criticalQ - 1) * w ^ (criticalQ - 2)) w := by
    have hw' : 0 < w := hx.trans hw.1
    have h := (Real.hasDerivAt_rpow_const (p := criticalQ - 1) (Or.inl hw'.ne')).const_mul criticalQ
    change HasDerivAt (fun x : ℝ => criticalQ * x ^ (criticalQ - 1)) _ w
    simpa only [show criticalQ - 1 - 1 = criticalQ - 2 by ring, mul_assoc] using h
  have hc : Continuous slopePower :=
    (Real.continuous_rpow_const (by linarith only [q_gt])).const_mul _
  obtain ⟨w, hw, he⟩ := exists_hasDerivAt_eq_slope slopePower _ hxy hc.continuousOn hd
  have h := Real.rpow_le_rpow_of_nonpos hx hw.1.le (by linarith only [q_lt] : criticalQ - 2 ≤ 0)
  have hh := (mul_le_mul_of_nonneg_left h
    (mul_nonneg (by linarith only [q_gt]) (by linarith only [q_gt]))).trans hC
  rw [he] at hh
  exact (div_le_iff₀ (sub_pos.mpr hxy)).1 hh

private def pairedPower (y : ℝ) : ℝ := (power (y - 2) - power y) / 2

private theorem pairedPower_diff_le {x y Y C : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hY : y ≤ Y)
    (hY₂ : Y < 2) (hC : C ≤ criticalQ / 2 * (x ^ (criticalQ - 1) + (2 - Y) ^ (criticalQ - 1))) :
    pairedPower y - pairedPower x ≤ -C * (y - x) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  let P (w : ℝ) := ((2 - w) ^ criticalQ - w ^ criticalQ) / 2
  have heq {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 2) : pairedPower w = P w := by
    simp only [pairedPower, P, power, abs_of_nonneg hw, abs_of_nonpos (sub_nonpos.mpr hw')]
    rw [neg_sub]
  rw [heq hx.le (hxy.le.trans (hY.trans hY₂.le)), heq (hx.le.trans hxy.le) (hY.trans hY₂.le)]
  have hd (w : ℝ) (hw : w ∈ Ioo x y) :
      HasDerivAt P (-(criticalQ / 2) * ((2 - w) ^ (criticalQ - 1) + w ^ (criticalQ - 1))) w := by
    have hw₀ : 0 < w := hx.trans hw.1
    have hw₂ : 0 < 2 - w := sub_pos.mpr (hw.2.trans_le hY |>.trans hY₂)
    have h₁ := (Real.hasDerivAt_rpow_const (p := criticalQ) (Or.inl hw₂.ne')).comp w
      ((hasDerivAt_id w).const_sub 2)
    have h₂ := Real.hasDerivAt_rpow_const (p := criticalQ) (Or.inl hw₀.ne')
    convert (h₁.sub h₂).div_const 2 using 1
    · rfl
    · ring
  have hc : Continuous P := by
    unfold P
    fun_prop (disch := linarith only [q_gt])
  obtain ⟨w, hw, he⟩ := exists_hasDerivAt_eq_slope P _ hxy hc.continuousOn hd
  have hq : 0 ≤ criticalQ - 1 := by linarith only [q_gt]
  have h₁ := Real.rpow_le_rpow hx.le hw.1.le hq
  have h₂ := Real.rpow_le_rpow (sub_nonneg.mpr hY₂.le) (sub_le_sub_left (hw.2.le.trans hY) 2) hq
  have hbound := hC.trans (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂)
    (show 0 ≤ criticalQ / 2 by linarith only [q_gt]))
  have hn : -(criticalQ / 2) * ((2 - w) ^ (criticalQ - 1) + w ^ (criticalQ - 1)) ≤ -C := by
    linarith only [hbound]
  rw [he] at hn
  exact (div_le_iff₀ (sub_pos.mpr hxy)).1 hn

theorem far_midpoint_model_le {a₀ a₁ h₀ h₁ a h D L : ℝ}
    (ha₀ : a₀ ≤ a) (ha₁ : a ≤ a₁) (hh₀ : h₀ ≤ h) (hh₁ : h ≤ h₁)
    (hm : 0 < a₀ + h₀ / 2) (hy : 0 < a₀ + h₀) (hy₁ : a₁ + h₁ < 2)
    (hD : criticalQ * (criticalQ - 1) * (a₀ + h₀ / 2) ^ (criticalQ - 2) ≤ D)
    (hL : L ≤ criticalQ / 2 *
      ((a₀ + h₀) ^ (criticalQ - 1) + (2 - (a₁ + h₁)) ^ (criticalQ - 1))) :
    farMidpoint a h ≤ farMidpoint a₀ h₀ +
      max 0 (D - L) * (a₁ - a₀) + max 0 (D / 2 - L) * (h₁ - h₀) := by
  have hnear := slopePower_diff_le (y := a + h/2) hm (by linarith only [ha₀, hh₀]) hD
  have hfar := pairedPower_diff_le hy (add_le_add ha₀ hh₀) (add_le_add ha₁ hh₁) hy₁ hL
  have ha := mul_le_mul (le_max_right (0 : ℝ) (D - L)) (sub_le_sub_right ha₁ a₀)
    (sub_nonneg.mpr ha₀) (le_max_left _ _)
  have hh := mul_le_mul (le_max_right (0 : ℝ) (D / 2 - L)) (sub_le_sub_right hh₁ h₀)
    (sub_nonneg.mpr hh₀) (le_max_left _ _)
  unfold pairedPower at hfar
  unfold farMidpoint
  nlinarith only [hnear, hfar, ha, hh]

end

end HlawkaSchatten.BelowExponent.G3P
