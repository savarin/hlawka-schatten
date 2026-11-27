/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PFarTiles
public import HlawkaSchatten.BelowExponent.G3PCommonDenSound
public import HlawkaSchatten.BelowExponent.G3PCertSound
import all HlawkaSchatten.BelowExponent.G3PCertSound
import Batteries.Tactic.OpenPrivate

/-! Transfer normalized height and ratio bounds to the signed physical central row. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)
open private clearDen_eval from HlawkaSchatten.BelowExponent.G3PCertSound

noncomputable section

private theorem unitBox_center (H A : RatBounds) : center (unitBox H A) = A := by
  cases A with
  | mk l r =>
    simp [unitBox, center, lBounds, bounds, kBounds, G3S.kMin, G3S.kMax, G3S.ratio,
      RatBounds.mul, RatBounds.add, RatBounds.point, point]

theorem FarTiles.sound {T : FarTiles} {H A : RatBounds} {cap : ℚ} (hc : T.ok H A cap = true)
    {h Z s : ℝ} (hh : 0 < h) (hs : s ≠ 0) (hH : H.Contains h) (hA : A.Contains (Z/s)) :
    balancedFarIncrement criticalQ (1-h) Z s / h ≤ G3S.power s * (cap : ℝ) := by
  induction T generalizing H A with
  | leaf f =>
    obtain ⟨hf, hcap⟩ := Bool.and_eq_true_iff.mp hc
    have hU : (bounds (unitBox H A) 2).Contains (1 : ℝ) := by
      change ((1 : ℚ) : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ ((1 : ℚ) : ℝ)
      norm_num
    have hZ : (center (unitBox H A)).Contains (Z/s) := by rwa [unitBox_center]
    have h := far_factor_sound (b := true) hf hh (show (bounds (unitBox H A) 0).Contains h from hH)
      hZ hU (by norm_num)
    have hf' : (f.value (unitBox H A) true : ℝ) ≤ cap := by exact_mod_cast of_decide_eq_true hcap
    change balancedFarIncrement criticalQ (1 - _) _ 1 / _ ≤ _ at h
    rw [far_div_eq hh.ne' one_ne_zero] at h
    simp only [div_one, G3S.power, abs_one, Real.one_rpow, one_mul, mul_one] at h
    rw [far_div_eq hh.ne' hs]
    exact mul_le_mul_of_nonneg_left (h.trans hf') (Real.rpow_nonneg (abs_nonneg _) _)
  | height m l r hl hr =>
    obtain ⟨p,q⟩ := Bool.and_eq_true_iff.mp hc
    rcases le_total h (m : ℝ) with h₀ | h₁
    · exact hl p ⟨hH.1,h₀⟩ hA
    · exact hr q ⟨h₁,hH.2⟩ hA
  | ratio m l r hl hr =>
    obtain ⟨p,q⟩ := Bool.and_eq_true_iff.mp hc
    rcases le_total (Z/s) (m : ℝ) with h₀ | h₁
    · exact hl p hH ⟨hA.1,h₀⟩
    · exact hr q hH ⟨h₁,hA.2⟩

theorem TiledRow.soundOnRatio {w : TiledRow} {B : Box} {A : RatBounds}
    (b : Bool) (hw : w.okOnRatio B b A = true)
    {h σ u z : ℝ} (hx : B.Mem ![h,σ,u,z]) (hh : 0 < h) (hz : |z| ≤ 8) (hu : 0 < u)
    (hratio : A.Contains (balancedFarCenter (h*(σ/(2-σ))) (h*(σ/(2-σ))) 1 z / signed b u)) :
    0 ≤ g3FacetGap h σ 1 (signed b u) z := by
  simp only [TiledRow.okOnRatio, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hw
  obtain ⟨domain, capPos, wl, wh, jw, left, right, cover, quad⟩ := hw
  obtain ⟨h0, _, h2, s0, s1, _, l1, u0, uw, u1⟩ := domain
  have hH : (bounds B 0).Contains h := hx 0
  have hS : (bounds B 1).Contains σ := hx 1
  have hU : (bounds B 2).Contains u := hx 2
  have hZ : (bounds B 3).Contains z := hx 3
  have hh₁ : h ≤ 1 := hH.2.trans (by
    change (B.hi 0 : ℝ) ≤ 1
    exact_mod_cast h2.trans (by norm_num : (9:ℚ)/17 ≤ 1))
  have hσ := (show (0 : ℝ) < B.lo 1 by exact_mod_cast s0).trans_le hS.1
  have hσ₁ : σ ≤ 1/5 := hS.2.trans (by
    change (B.hi 1 : ℝ) ≤ 1/5
    simpa using (Rat.cast_le (K := ℝ)).2 s1)
  have hu₁ : u ≤ 1 := hU.2.trans (by exact_mod_cast u1)
  have hK := k_mem hS s1
  have hL := RatBounds.mul_mem hH hK
  have hl : 0 < h * (σ/(2-σ)) := mul_pos hh (div_pos hσ (by linarith only [hσ₁]))
  have hl₁ : ((lBounds B).hi : ℝ) ≤ 1 := by exact_mod_cast l1
  have hM : (muBounds B w.row).Contains (g3Weight h σ) := G3S.weight_bounds hH.1 hH.2
    hS.1 hS.2 h0 s0.le (units_nonneg _) (units_nonneg _) wl wh
  have hJ := jensen_sound jw hl hL.2 hl₁ hZ
  have hs : signed b u ≠ 0 := by cases b <;> simp [signed, hu.ne']
  have hfar := FarTiles.sound cover hh hs hH hratio
  simp only [G3S.power, signed_abs b hu.le] at hfar
  have hnear := near_sound (w := w.row) b hh hh₁ hσ hσ₁ hu.le hu₁ hz hH hU hZ hK hM hJ hfar
  let θ := (u - B.lo 2) / ((B.hi 2 : ℝ) - B.lo 2)
  have width : 0 < (B.hi 2 : ℝ) - B.lo 2 := sub_pos.mpr (by exact_mod_cast uw)
  have t₀ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hU.1) width.le
  have t₁ : θ ≤ 1 := (div_le_one₀ width).2 (sub_le_sub_right hU.2 _)
  have line : u = (B.lo 2 : ℝ) + θ * ((B.hi 2 : ℝ) - B.lo 2) := by
    dsimp only [θ]
    rw [div_mul_cancel₀ _ width.ne']
    ring
  have l := G3Power.tightUpper_sound (units_nonneg _) left
  have r := G3Power.tightUpper_sound (units_nonneg _) right
  rw [abs_of_nonneg (show (0:ℝ) ≤ B.lo 2 by exact_mod_cast u0)] at l
  rw [abs_of_nonneg (show (0:ℝ) ≤ B.hi 2 by exact_mod_cast u0.trans uw.le)] at r
  have chord := rpow_le_upperChord
    ((by norm_num : (1:ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le)
    (show (0:ℝ) ≤ B.lo 2 by exact_mod_cast u0)
    (show (0:ℝ) ≤ B.hi 2 by exact_mod_cast u0.trans uw.le) hu.le t₀ t₁
    (show u ≤ (1-θ) * (B.lo 2 : ℝ) + θ * (B.hi 2 : ℝ) by linarith only [line]) l r
  have μ := (g3_weight_pos_lt_third hh.le hh₁ hσ hσ₁).1.le
  have F : (0 : ℝ) ≤ w.cap := by exact_mod_cast capPos
  have pos := (mul_nonneg μ F).trans (mul_le_mul_of_nonneg_right hM.2 F)
  have cost := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM.2 F)
    (Real.rpow_nonneg hu.le _)).trans (mul_le_mul_of_nonneg_left chord pos)
  have hq := Quad.eval_nonneg quad t₀ t₁
  rw [TiledRow.quad, nearTermsCommon_eq, clearDen_eval] at hq
  push_cast at hq
  let A := nearTerms B b w.row
  change 0 ≤ (A.squared:ℝ) * _ ^ 2 * θ^2 + _ * θ + _ at hq
  have hpoly : 0 ≤ (A.squared:ℝ)*u^2 - (A.linearCost:ℝ)*u + (A.constant:ℝ) -
      ((muBounds B w.row).hi:ℝ) * w.cap * ((1-θ)*(units w.left:ℝ) + θ*(units w.right:ℝ)) := by
    rw [line]
    linarith only [hq]
  have answer : 0 ≤ g3FacetGap h σ 1 (signed b u) z / h := by
    change _ - g3Weight h σ * (u ^ criticalQ * (w.cap:ℝ)) ≤ _ at hnear
    change _ ≤ _ at cost
    linarith only [hpoly, hnear, cost]
  simpa only [zero_mul] using (le_div_iff₀ hh).1 answer

theorem TiledRow.sound {w : TiledRow} {B : Box} (b : Bool) (hw : w.ok B b = true)
    {h σ u z : ℝ} (hx : B.Mem ![h,σ,u,z]) (hh : 0 < h) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 (signed b u) z := by
  obtain ⟨hu0, row⟩ := Bool.and_eq_true_iff.mp hw
  have hd := row
  simp only [TiledRow.okOnRatio, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hd
  obtain ⟨_, _, _, _, hσ, _, hL, _, _, _⟩ := hd.1
  have hH : (bounds B 0).Contains h := hx 0
  have hS : (bounds B 1).Contains σ := hx 1
  have hU : (bounds B 2).Contains u := hx 2
  have hZ : (bounds B 3).Contains z := hx 3
  have hl := RatBounds.mul_mem hH (k_mem hS hσ)
  have hu : (0 : ℝ) < B.lo 2 := by exact_mod_cast of_decide_eq_true hu0
  exact soundOnRatio b row hx hh hz (hu.trans_le hU.1)
    (ratio_mem b (center_mem hl (hl.2.trans (by exact_mod_cast hL)) hZ) hU hu)

theorem TiledCert.sound {B : Box} {t : TiledCert} (b : Bool) (ht : t.ok B b = true)
    {h σ u z : ℝ} (hx : B.Mem ![h,σ,u,z]) (hh : 0 < h) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/5)
    (hCap : h ≤ 1/(2-σ/(2-σ))) (hu : 0 ≤ u) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 (signed b u) z := by
  induction t generalizing B with
  | original t => exact certTree_sound b (CertTree.ok_of_commonOK ht) hx hh hσ hσ₁ hCap hu hz
  | row w => exact w.sound b ht hx hh hz
  | cut j m l r hl hr =>
    obtain ⟨p,q⟩ := Bool.and_eq_true_iff.mp ht
    rcases le_total (![h,σ,u,z] j) (m : ℝ) with h₀ | h₁
    · exact hl p (Box.mem_lower hx h₀)
    · exact hr q (Box.mem_upper hx h₁)

end

end HlawkaSchatten.BelowExponent.G3P
