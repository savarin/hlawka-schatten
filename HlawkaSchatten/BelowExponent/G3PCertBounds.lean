/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertData
public import HlawkaSchatten.BelowExponent.G3PDivided
public import HlawkaSchatten.BelowExponent.G3SSound
import HlawkaSchatten.BelowExponent.G3PMidpoint
import all HlawkaSchatten.BelowExponent.G1
import Batteries.Tactic.OpenPrivate

/-! Soundness of endpoint intervals and the divided Jensen and far-pair comparisons. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Set
open Vertex (RatBounds)
open private absPower_convex from HlawkaSchatten.BelowExponent.G1

noncomputable section

theorem units_nonneg (n : Nat) : 0 ≤ units n := by unfold units; positivity

theorem point_has (q : ℚ) : (point q).Contains (q : ℝ) := RatBounds.point_mem q

theorem abs_mem {B : RatBounds} {x : ℝ} (h : B.Contains x) :
    (absBounds B).Contains |x| := by
  change (B.lo : ℝ) ≤ x ∧ x ≤ B.hi at h
  unfold absBounds RatBounds.Contains
  simp only [Rat.cast_max, Rat.cast_zero, Rat.cast_neg, Rat.cast_abs]
  constructor
  · exact max_le (abs_nonneg x) (max_le (h.1.trans (le_abs_self x))
      ((neg_le_neg h.2).trans (neg_le_abs x)))
  · apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left |(B.lo : ℝ)| |(B.hi : ℝ)|)).trans
        ((neg_abs_le _).trans h.1),
      h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

theorem pos_pow_mem {B : RatBounds} {x : ℝ} (h : B.Contains x) (h₀ : (0 : ℝ) ≤ B.lo)
    (n : ℕ) : (posPow B n).Contains (x ^ n) := by
  simpa only [posPow, RatBounds.Contains, Rat.cast_pow] using
    And.intro (pow_le_pow_left₀ h₀ h.1 n) (pow_le_pow_left₀ (h₀.trans h.1) h.2 n)

theorem abs_pos_lo (B : RatBounds) : (0 : ℝ) ≤ (absBounds B).lo := by
  simp [absBounds, Rat.cast_max, Rat.cast_neg]

theorem square_mem {B : RatBounds} {x : ℝ} (h : B.Contains x) :
    (evenPow B 2).Contains (x ^ 2) := by
  simpa only [evenPow, sq_abs] using pos_pow_mem (abs_mem h) (abs_pos_lo B) 2

theorem fourth_mem {B : RatBounds} {x : ℝ} (h : B.Contains x) :
    (evenPow B 4).Contains (x ^ 4) := by
  have hf : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_mul, sq_abs]
  simpa only [evenPow, hf] using pos_pow_mem (abs_mem h) (abs_pos_lo B) 4

theorem recip_mem {B : RatBounds} {x : ℝ} (h : B.Contains x) (h₀ : (0 : ℝ) < B.lo) :
    (recip B).Contains (1 / x) := by
  simpa only [recip, RatBounds.Contains, Rat.cast_div, Rat.cast_one] using
    And.intro (one_div_le_one_div_of_le (h₀.trans_le h.1) h.2) (one_div_le_one_div_of_le h₀ h.1)

theorem k_mem {B : Box} {σ : ℝ}
    (hσ : (bounds B 1).Contains σ) (hB : B.hi 1 ≤ 1 / 5) :
    (kBounds B).Contains (σ / (2 - σ)) := by
  have hhi : (B.hi 1 : ℝ) ≤ 1 / 5 := by simpa using (Rat.cast_le (K := ℝ)).2 hB
  change (B.lo 1 : ℝ) ≤ σ ∧ σ ≤ (B.hi 1 : ℝ) at hσ
  simpa only [kBounds, G3S.kMin, G3S.kMax, G3S.ratio, RatBounds.Contains, Rat.cast_div,
    Rat.cast_sub, Rat.cast_ofNat] using
    And.intro (G3S.ratio_mono hσ.1 (hσ.2.trans hhi)) (G3S.ratio_mono hσ.2 hhi)

theorem center_mem {B : Box} {l z : ℝ} (hl : (lBounds B).Contains l) (hl₁ : l ≤ 1)
    (hz : (bounds B 3).Contains z) :
    (center B).Contains (balancedFarCenter l l 1 z) := by
  have hb (r : ℚ) :
      ((point r).add ((point (1 - r)).mul (lBounds B))).Contains ((r : ℝ) + (1 - r) * l) := by
    exact RatBounds.add_mem (point_has r)
      (RatBounds.mul_mem (by simpa only [Rat.cast_sub, Rat.cast_one] using point_has (1 - r)) hl)
  have hlo := (hb (B.lo 3)).1
  have hhi := (hb (B.hi 3)).2
  change (B.lo 3 : ℝ) ≤ z ∧ z ≤ (B.hi 3 : ℝ) at hz
  have w₀ := mul_le_mul_of_nonneg_left hz.1 (sub_nonneg.mpr hl₁)
  have w₁ := mul_le_mul_of_nonneg_left hz.2 (sub_nonneg.mpr hl₁)
  change ((center B).lo : ℝ) ≤ balancedFarCenter l l 1 z ∧
    balancedFarCenter l l 1 z ≤ ((center B).hi : ℝ)
  unfold balancedFarCenter
  exact ⟨hlo.trans (by linarith only [w₀]), (by linarith only [w₁] :
    (1 - l) * z + l * 1 ≤ (B.hi 3 : ℝ) + (1 - (B.hi 3 : ℝ)) * l).trans hhi⟩

theorem signRat_sq (b : Bool) : ((signRat b : ℚ) : ℝ) ^ 2 = 1 := by
  cases b <;> norm_num [signRat]

theorem signed_eq_mul (b : Bool) (u : ℝ) : signed b u = (signRat b : ℝ) * u := by
  cases b <;> simp [signRat, signed]

theorem signed_abs (b : Bool) {u : ℝ} (hu : 0 ≤ u) : |signed b u| = u := by
  cases b <;> simp [signed, abs_of_nonneg hu]

theorem ratio_mem {B : Box} {Z u : ℝ} (b : Bool) (hZ : (center B).Contains Z)
    (hu : (bounds B 2).Contains u) (hlo : 0 < (B.lo 2 : ℝ)) :
    (signedRatio B b).Contains (Z / signed b u) := by
  have h := RatBounds.mul_mem (RatBounds.mul_mem (point_has (signRat b)) hZ) (recip_mem hu hlo)
  cases b <;> simpa [signedRatio, signRat, signed, div_eq_mul_inv] using h

private theorem qOne : 1 ≤ criticalQ :=
  (by norm_num : (1 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le

private theorem jensen_nonneg {l z : ℝ} (hl : 0 < l) (hl₁ : l ≤ 1) :
    0 ≤ g3DividedJensen l z := by
  apply div_nonneg _ hl.le
  have h := (absPower_convex qOne).2 (mem_univ z) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hl₁) hl.le (sub_add_cancel 1 l)
  simp only [smul_eq_mul, abs_one, Real.one_rpow, mul_one] at h
  unfold balancedJensenGap balancedFarCenter
  simp only [abs_one, Real.one_rpow, mul_one, sub_nonneg]
  exact h

theorem jensen_sound {B : Box} {w : JensenWitness} {l z : ℝ}
    (hOK : w.ok B = true) (hl : 0 < l) (hL : l ≤ ((lBounds B).hi : ℝ))
    (hL₁ : ((lBounds B).hi : ℝ) ≤ 1) (hz : (bounds B 3).Contains z) :
    (w.value B : ℝ) ≤ g3DividedJensen l z := by
  let L := ((lBounds B).hi : ℝ)
  let z₀ := (B.lo 3 : ℝ)
  let z₁ := (B.hi 3 : ℝ)
  let r := (jensenBase B : ℝ)
  have hL₀ : 0 < L := hl.trans_le hL
  cases w with
  | zero => simpa [JensenWitness.value] using jensen_nonneg (z := z) hl (hL.trans hL₁)
  | direct a b =>
    simp only [JensenWitness.ok, Bool.and_eq_true] at hOK
    have hr : r = min (max 1 z₀) z₁ := by simp [r, jensenBase, z₀, z₁, Rat.cast_min, Rat.cast_max]
    have hj : g3DividedJensen L r ≤ g3DividedJensen L z := by
      have hz₀ : z₀ ≤ z := hz.1
      have hz₁ : z ≤ z₁ := hz.2
      by_cases hleft : z₁ ≤ 1
      · rw [hr, min_eq_right (hleft.trans (le_max_left _ _))]
        exact g3DividedJensen_left hL₀ hL₁ (hz₁.trans hleft) hleft hz₁
      by_cases hright : 1 ≤ z₀
      · rw [hr, max_eq_right hright, min_eq_left (hz₀.trans hz₁)]
        exact g3DividedJensen_right hL₀ hL₁ hright (hright.trans hz₀) hz₀
      · rw [hr, max_eq_left (le_of_not_ge hright), min_eq_left (le_of_not_ge hleft)]
        have hzero : g3DividedJensen L 1 = 0 := by
          have hcenter : balancedFarCenter L L 1 1 = 1 := by unfold balancedFarCenter; ring
          simp [g3DividedJensen, balancedJensenGap, hcenter]
        rw [hzero]
        exact jensen_nonneg hL₀ hL₁
    have hbase : (units a : ℝ) ≤ |r| ^ criticalQ := G3Power.tightLower_sound hOK.1
    have hshift := G3Power.tightUpper_sound (units_nonneg b) hOK.2
    have heq : (jensenShift B : ℝ) = balancedFarCenter L L 1 r := by
      unfold jensenShift balancedFarCenter
      push_cast
      dsimp only [L, r]
      ring
    rw [heq] at hshift
    have hreal : ((JensenWitness.direct a b).value B : ℝ) ≤ g3DividedJensen L r := by
      unfold JensenWitness.value g3DividedJensen balancedJensenGap
      push_cast
      simp only [abs_one, Real.one_rpow, mul_one]
      change _ / L ≤ _ / L
      exact (div_le_div_iff_of_pos_right hL₀).2
        (by linarith only [mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hL₁), hshift])
    exact hreal.trans (hj.trans (g3DividedJensen_depth hl hL))

theorem factor_nonneg (B : Box) (b : Bool) (ff : FarFactor) : 0 ≤ ff.value B b := by
  cases ff <;> simp [FarFactor.value, midpointValue]

private theorem pred_bounds {x : ℝ} (hx : 0 ≤ x) :
    (if x ≤ 1 then x ^ (179 / 306 : ℝ) else x ^ (389 / 665 : ℝ)) ≤ x ^ (criticalQ - 1) ∧
    x ^ (criticalQ - 1) ≤ (if x ≤ 1 then x ^ (389 / 665 : ℝ) else x ^ (179 / 306 : ℝ)) :=
  rpow_exponent_bounds hx (by norm_num : (0 : ℝ) ≤ 389 / 665)
    (show (389/665 : ℝ) ≤ criticalQ - 1 by linarith only [criticalQ_bracket.1])
    (show criticalQ - 1 ≤ (179/306 : ℝ) by linarith only [criticalQ_bracket.2])

private theorem pred_lower_sound {x y : ℚ} (hx : 0 ≤ x) (h : predLower x y = true) :
    (y : ℝ) ≤ (x : ℝ) ^ (criticalQ - 1) := by
  have hx' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hB := pred_bounds hx'
  by_cases h₁ : x ≤ 1
  · rw [predLower, ite_eq_left h₁] at h
    have h₁' : (x : ℝ) ≤ 1 := by exact_mod_cast h₁
    simp only [ite_eq_left h₁'] at hB
    have hp := G3Power.crossLE_lower (by decide) h
    norm_num [abs_of_nonneg hx'] at hp
    exact (le_abs_self _).trans (hp.trans hB.1)
  · rw [predLower, ite_eq_right h₁] at h
    have h₁' : ¬ (x : ℝ) ≤ 1 := fun hn => h₁ (by exact_mod_cast hn)
    simp only [ite_eq_right h₁'] at hB
    have hp := G3Power.crossLE_lower (by decide) h
    norm_num [abs_of_nonneg hx'] at hp
    exact (le_abs_self _).trans (hp.trans hB.1)

private theorem pred_upper_sound {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : predUpper x y = true) : (x : ℝ) ^ (criticalQ - 1) ≤ (y : ℝ) := by
  have hx' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hy' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hB := pred_bounds hx'
  by_cases h₁ : x ≤ 1
  · rw [predUpper, ite_eq_left h₁] at h
    have h₁' : (x : ℝ) ≤ 1 := by exact_mod_cast h₁
    simp only [ite_eq_left h₁'] at hB
    have hp := G3Power.crossLE_upper (by decide) h
    norm_num [abs_of_nonneg hx', abs_of_nonneg hy'] at hp
    exact hB.2.trans hp
  · rw [predUpper, ite_eq_right h₁] at h
    have h₁' : ¬ (x : ℝ) ≤ 1 := fun hn => h₁ (by exact_mod_cast hn)
    simp only [ite_eq_right h₁'] at hB
    have hp := G3Power.crossLE_upper (by decide) h
    norm_num [abs_of_nonneg hx', abs_of_nonneg hy'] at hp
    exact hB.2.trans hp

private theorem midpoint_sound {B : Box} {b : Bool} {w : MidpointWitness} {h Z u : ℝ}
    (hc : midpointOK B b w = true) (hh : 0 < h)
    (hH : (bounds B 0).Contains h) (hZ : (center B).Contains Z) (hU : (bounds B 2).Contains u) :
    balancedFarIncrement criticalQ (1 - h) Z (signed b u) / h ≤
      (midpointValue B b w : ℝ) * u ^ criticalQ := by
  simp only [midpointOK, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hc
  obtain ⟨hu, ha, hy, hm, hY, wP₁, wP₀, wM, wD, wL, wR⟩ := hc
  let A := signedRatio B b
  let y0 := (A.lo : ℝ) + (B.lo 0 : ℝ)
  let y1 := (A.hi : ℝ) + (B.hi 0 : ℝ)
  let m0 := (A.lo : ℝ) + (B.lo 0 : ℝ) / 2
  have hu' : (0 : ℝ) < (B.lo 2 : ℝ) := by exact_mod_cast hu
  have hu₀ := hu'.trans_le hU.1
  have hAs := ratio_mem b hZ hU hu'
  have hA : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast ha
  have hy₀ : 0 < y0 := by dsimp [y0, A]; exact_mod_cast hy
  have hm₀ : 0 < m0 := by
    dsimp [m0, A]
    simpa only [Rat.cast_zero, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 hm
  have hy₁ : y1 < 2 := by dsimp [y1, A]; exact_mod_cast hY
  have hY₀ : 0 ≤ 2 - ((signedRatio B b).hi + B.hi 0) := by linarith only [hY]
  have hPL := G3Power.tightUpper_sound (units_nonneg _) wP₁
  have hPR := G3Power.tightLower_sound wP₀
  have hmid := pred_upper_sound hm.le (units_nonneg _) wM
  have hcurve := G3Power.tightCurve_sound hm (units_nonneg _) wD
  have hyl := pred_lower_sound hy.le wL
  have hyr := pred_lower_sound hY₀ wR
  push_cast at hPL hPR hmid hcurve hyl hyr
  have hQL : (qBounds.lo : ℝ) ≤ criticalQ := by
    simpa [qBounds] using criticalQ_bracket.1.le
  have hQH : criticalQ ≤ (qBounds.hi : ℝ) := by
    simpa [qBounds] using criticalQ_bracket.2.le
  have hQ₀ : 0 ≤ criticalQ := by linarith only [criticalQ_bracket.1]
  have hQ₁ : 1 ≤ criticalQ := by linarith only [criticalQ_bracket.1]
  have hQL₀ : (0 : ℝ) ≤ (qBounds.lo : ℝ) := by norm_num [qBounds]
  have wu (n : Nat) : (0 : ℝ) ≤ (units n : ℝ) := by exact_mod_cast units_nonneg n
  have hfM : slopePower m0 ≤ (qBounds.hi : ℝ) * (units w.midUpper : ℝ) := by
    exact mul_le_mul hQH hmid (Real.rpow_nonneg hm₀.le _) (hQ₀.trans hQH)
  have hD : criticalQ * (criticalQ - 1) * m0 ^ (criticalQ - 2) ≤ (slopeGain w : ℝ) := by
    unfold slopeGain
    push_cast
    apply mul_le_mul _ hcurve (Real.rpow_nonneg hm₀.le _)
      (mul_nonneg (hQ₀.trans hQH) (sub_nonneg.mpr (hQ₁.trans hQH)))
    exact mul_le_mul hQH (sub_le_sub_right hQH 1) (sub_nonneg.mpr hQ₁) (hQ₀.trans hQH)
  have hL : (slopeLoss w : ℝ) ≤ criticalQ / 2 *
      (y0 ^ (criticalQ - 1) + (2 - y1) ^ (criticalQ - 1)) := by
    unfold slopeLoss
    push_cast
    exact mul_le_mul (div_le_div_of_nonneg_right hQL (by norm_num)) (add_le_add hyl hyr)
      (add_nonneg (wu _) (wu _)) (by positivity)
  have hs : signed b u ≠ 0 := by cases b <;> simp [signed, hu₀.ne']
  have hlower := far_div_le_midpoint hh hs (hA.trans hAs.1)
  have hmodel := far_midpoint_model_le hAs.1 hAs.2 hH.1 hH.2 hm₀ hy₀ hy₁ hD hL
  have hbase : farMidpoint (A.lo : ℝ) (B.lo 0 : ℝ) ≤
      ((units w.pairHigh : ℝ) - (units w.pairLow : ℝ)) / 2 +
        (qBounds.hi : ℝ) * (units w.midUpper : ℝ) := by
    unfold farMidpoint G3S.power
    linarith only [hPL, hPR, hfM]
  have hval : farMidpoint (Z / signed b u) h ≤ (midpointValue B b w : ℝ) := by
    unfold midpointValue
    simp only [Rat.cast_max, Rat.cast_add, Rat.cast_zero, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_div, Rat.cast_ofNat]
    exact le_max_of_le_right (hmodel.trans (add_le_add_left (add_le_add_left hbase _) _))
  simpa only [G3S.power, signed_abs b hu₀.le, mul_comm] using
    hlower.trans (mul_le_mul_of_nonneg_left hval (Real.rpow_nonneg (abs_nonneg (signed b u)) _))

theorem far_factor_sound {B : Box} {b : Bool} {ff : FarFactor} {h Z u : ℝ}
    (hOK : ff.ok B b = true) (hh : 0 < h) (hH : (bounds B 0).Contains h)
    (hZ : (center B).Contains Z) (hU : (bounds B 2).Contains u) (hu : 0 ≤ u) :
    balancedFarIncrement criticalQ (1 - h) Z (signed b u) / h ≤
      (ff.value B b : ℝ) * u ^ criticalQ := by
  cases ff with
  | universal =>
    simpa only [FarFactor.value, Rat.cast_ofNat, signed_abs b hu] using
      (g3FarIncrement_div_le_power (Z := Z) (s := signed b u) hh)
  | secant a c d e =>
    simp only [FarFactor.ok, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hOK
    obtain ⟨hu₀, hpair₁, hpair₀, hfar₁, hfar₀⟩ := hOK
    have hu₀r : 0 < (B.lo 2 : ℝ) := by exact_mod_cast hu₀
    have hu' := hu₀r.trans_le hU.1
    have hs : signed b u ≠ 0 := by cases b <;> simp [signed, hu'.ne']
    have hA := ratio_mem b hZ hU hu₀r
    have hhi : 0 < (B.hi 0 : ℝ) := hh.trans_le hH.2
    have hfar := far_div_le_secants hh hH.1 hH.2 hs hA.1 hA.2
    have h₁ := G3Power.tightUpper_sound (units_nonneg a) hpair₁
    have h₂ := G3Power.tightLower_sound hpair₀
    have h₃ := G3Power.tightUpper_sound (units_nonneg d) hfar₁
    have h₄ := G3Power.tightLower_sound hfar₀
    push_cast at h₁ h₂ h₃
    have hcoeff : farCoeff (B.lo 0) (B.hi 0) (signedRatio B b).lo (signedRatio B b).hi ≤
        ((FarFactor.secant a c d e).value B b : ℝ) := by
      unfold farCoeff G3S.farSecant FarFactor.value G3S.power
      simp only [Rat.cast_add, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
      apply le_max_of_le_right
      have h₅ : (|(signedRatio B b).hi + (B.hi 0 : ℝ)| ^ criticalQ -
          |((signedRatio B b).hi : ℝ)| ^ criticalQ) / (B.hi 0 : ℝ) ≤
          ((units d : ℝ) - (units e : ℝ)) / (B.hi 0 : ℝ) :=
        (div_le_div_iff_of_pos_right hhi).2 (by linarith only [h₃, h₄])
      linarith only [h₁, h₂, h₅]
    simpa only [G3S.power, signed_abs b hu, mul_comm] using
      hfar.trans (mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg (abs_nonneg (signed b u)) _))
  | midpoint w => exact midpoint_sound hOK hh hH hZ hU

theorem curve_sound {B : Box} {n : Nat} {Z : ℝ}
    (h₀ : 0 < (absBounds (center B)).lo)
    (hOK : G3Power.tightCurve (absBounds (center B)).lo (units n) = true)
    (hZ : (center B).Contains Z) :
    Z ≠ 0 ∧ |Z| ^ (criticalQ - 2) ≤ (units n : ℝ) := by
  have h := (abs_mem hZ).1
  have hp : (0 : ℝ) < ((absBounds (center B)).lo : ℝ) := by exact_mod_cast h₀
  have hZ₀ := hp.trans_le h
  have he : criticalQ - 2 ≤ 0 := by linarith only [criticalQ_bracket.2]
  exact ⟨abs_pos.mp hZ₀, (Real.rpow_le_rpow_of_nonpos hp h he).trans
    (G3Power.tightCurve_sound h₀ (units_nonneg _) hOK)⟩

end

end HlawkaSchatten.BelowExponent.G3P
