/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Far
public import Mathlib.Analysis.InnerProductSpace.NormPow
import all HlawkaSchatten.BelowExponent.G1
import all HlawkaSchatten.BelowExponent.G1Far

/-! The bounded-z, large-|s| facet chart on the written G1 slabs. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

open private evenGap_nonneg absPower_convex from HlawkaSchatten.BelowExponent.G1
open private criticalQ_lo criticalQ_hi slab_ranges evenGap_scale from HlawkaSchatten.BelowExponent.G1Far

private theorem absPower_deriv {q : ℝ} (hq : 1 < q) (x : ℝ) :
    HasDerivAt (fun y : ℝ => |y| ^ q)
      (q * (if 0 ≤ x then |x| ^ (q - 1) else -|x| ^ (q - 1))) x := by
  have h := hasDerivAt_abs_rpow x hq
  by_cases hx : x = 0
  · subst x
    simpa [Real.zero_rpow (sub_ne_zero.mpr hq.ne')] using h
  · have hp : 0 < |x| := abs_pos.mpr hx
    have heq : |x| ^ (q - 1) = |x| ^ (q - 2) * |x| := by
      calc
        _ = |x| ^ ((q - 2) + 1) := by ring_nf
        _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]
    convert h using 1
    rw [heq]
    by_cases hx₀ : 0 ≤ x
    · rw [ite_eq_left hx₀, abs_of_nonneg hx₀]
      ring
    · rw [ite_eq_right hx₀, abs_of_neg (lt_of_not_ge hx₀)]
      ring

private theorem evenGap_at_one_antitone {q : ℝ} (hq : 1 < q) (hq₂ : q ≤ 2) :
    AntitoneOn (fun x => balancedEvenGap q x 1) (Ici 0) := by
  let D (x : ℝ) := if 0 ≤ x then |x| ^ (q - 1) else -|x| ^ (q - 1)
  have hd (x : ℝ) : HasDerivAt (fun x => balancedEvenGap q x 1)
      ((q * D (x + 1) + q * D (x - 1)) / 2 - q * D x) x := by
    have h₁ := (absPower_deriv hq (x + 1)).comp x ((hasDerivAt_id x).add_const 1)
    have h₂ := (absPower_deriv hq (x - 1)).comp x ((hasDerivAt_id x).sub_const 1)
    have hd' := ((h₁.add h₂).div_const 2).sub (absPower_deriv hq x)
    convert! hd' using 1
    simp [D]
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  have hx₀ : 0 ≤ x := interior_subset hx
  rw [(hd x).deriv]
  have hD : D (x + 1) + D (x - 1) ≤ 2 * D x := by
    have hp : 0 ≤ q - 1 := by linarith
    have hp₁ : q - 1 ≤ 1 := by linarith
    rw [show D (x + 1) = (x + 1) ^ (q - 1) by simp [D, abs_of_nonneg, show 0 ≤ x + 1 by linarith],
      show D x = x ^ (q - 1) by simp [D, hx₀, abs_of_nonneg]]
    by_cases hx₁ : 1 ≤ x
    · have hm : 0 ≤ x - 1 := sub_nonneg.mpr hx₁
      rw [show D (x - 1) = (x - 1) ^ (q - 1) by simp [D, hm, abs_of_nonneg]]
      have hc := (Real.concaveOn_rpow hp hp₁).2 (mem_Ici.mpr (show 0 ≤ x + 1 by linarith))
        (mem_Ici.mpr hm) (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
        (by norm_num : (1/2 : ℝ) + 1/2 = 1)
      simp only [smul_eq_mul, show (1/2 : ℝ) * (x + 1) + 1/2 * (x - 1) = x by ring] at hc
      linarith only [hc]
    · have hm : x - 1 < 0 := by linarith
      rw [show D (x - 1) = -(1 - x) ^ (q - 1) by
        simp [D, hm, hm.not_ge, abs_of_neg, neg_sub]]
      have hAdd := Real.rpow_add_le_add_rpow (p := q - 1)
        (show 0 ≤ 1 - x by linarith) (by positivity : 0 ≤ 2 * x) hp hp₁
      rw [show 1 - x + 2 * x = x + 1 by ring,
        Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hx₀] at hAdd
      have h₂ : (2 : ℝ) ^ (q - 1) ≤ 2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hp₁
      have hmul := mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hx₀ (q - 1))
      linarith only [hAdd, hmul]
  have hmul := mul_le_mul_of_nonneg_left hD (show 0 ≤ q by linarith)
  linarith only [hmul]

private theorem evenGap_neg_center (q p s : ℝ) :
    balancedEvenGap q (-p) s = balancedEvenGap q p s := by
  unfold balancedEvenGap
  rw [show -p + s = -(p - s) by ring, show -p - s = -(p + s) by ring]
  simp only [abs_neg]
  ring

private theorem evenGap_neg_shift (q p s : ℝ) :
    balancedEvenGap q p (-s) = balancedEvenGap q p s := by
  unfold balancedEvenGap
  rw [show p + -s = p - s by ring, show p - -s = p + s by ring]
  ring

private theorem evenGap_factor {q p s : ℝ} (hs : s ≠ 0) :
    balancedEvenGap q p s = |s| ^ q * balancedEvenGap q (|p| / |s|) 1 := by
  have hp : balancedEvenGap q |p| s = balancedEvenGap q p s := by
    rcases le_or_gt 0 p with hp | hp
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg hp, evenGap_neg_center]
  have hs' : balancedEvenGap q |p| |s| = balancedEvenGap q |p| s := by
    rcases le_or_gt 0 s with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, evenGap_neg_shift]
  have h := evenGap_scale (q := q) (abs_nonneg s) (|p| / |s|) 1
  have heq : |s| * (|p| / |s|) = |p| := by field_simp [(abs_pos.mpr hs).ne']
  rw [mul_one, heq, hs', hp] at h
  exact h

private theorem evenGap_shrink {q p s u R : ℝ} (hq : 1 < q) (hq₂ : q ≤ 2)
    (hR : R ≤ 1) (hR₀ : 0 ≤ R) (hu : |u| ≤ R * |s|) :
    balancedEvenGap q p u ≤ R ^ q * balancedEvenGap q p s := by
  rcases eq_or_ne u 0 with rfl | hu₀
  · have h := evenGap_nonneg hq.le p s
    unfold balancedEvenGap at ⊢
    simp only [add_zero, sub_zero]
    have hr := Real.rpow_nonneg hR₀ q
    unfold balancedEvenGap at h
    rw [show (|p| ^ q + |p| ^ q) / 2 - |p| ^ q = 0 by ring]
    exact mul_nonneg hr h
  have hs : s ≠ 0 := by
    intro h
    simp [h, (abs_pos.mpr hu₀).not_ge] at hu
  have hus : |u| ≤ |s| := hu.trans (by simpa using mul_le_mul_of_nonneg_right hR (abs_nonneg s))
  have hr := div_le_div_of_nonneg_left (abs_nonneg p) (abs_pos.mpr hu₀) hus
  have ha := evenGap_at_one_antitone hq hq₂
    (show |p| / |s| ∈ Ici 0 from div_nonneg (abs_nonneg p) (abs_nonneg s))
    (show |p| / |u| ∈ Ici 0 from div_nonneg (abs_nonneg p) (abs_nonneg u)) hr
  rw [evenGap_factor hu₀, evenGap_factor hs, ← mul_assoc, ← Real.mul_rpow hR₀ (abs_nonneg s)]
  exact mul_le_mul (Real.rpow_le_rpow (abs_nonneg u) hu (by linarith)) ha
    (evenGap_nonneg hq.le _ _) (Real.rpow_nonneg (mul_nonneg hR₀ (abs_nonneg s)) q)

private theorem evenGap_large_lower {p s : ℝ} (hps : |p| ≤ |s|) :
    (1/2) * |s| ^ criticalQ ≤ balancedEvenGap criticalQ p s := by
  have hq : 1 < criticalQ := (by norm_num : (1 : ℝ) < 1054/665).trans_le criticalQ_lo
  rcases eq_or_ne s 0 with rfl | hs
  · simpa [Real.zero_rpow (show criticalQ ≠ 0 by linarith)] using evenGap_nonneg hq.le p 0
  have ha := evenGap_at_one_antitone hq (criticalQ_hi.trans (by norm_num))
    (show |p| / |s| ∈ Ici 0 from div_nonneg (abs_nonneg p) (abs_nonneg s))
    (show (1 : ℝ) ∈ Ici 0 by norm_num)
    ((div_le_one (abs_pos.mpr hs)).mpr hps)
  have h1 : balancedEvenGap criticalQ 1 1 = 1/2 := by
    unfold balancedEvenGap
    norm_num only [one_add_one_eq_two, sub_self, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_zero, abs_one, Real.one_rpow, Real.zero_rpow (show criticalQ ≠ 0 by linarith), two_rpow_criticalQ]
  rw [evenGap_factor hs, mul_comm (1/2 : ℝ), ← h1]
  exact mul_le_mul_of_nonneg_left ha (Real.rpow_nonneg (abs_nonneg s) _)

private theorem far_increment_large_bound {e : ℝ} (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2)
    (Z s : ℝ) :
    balancedFarIncrement criticalQ e Z s ≤ (1 - (3/4)*e^2) * |s|^criticalQ := by
  have hq₀ : 0 ≤ criticalQ := by linarith [criticalQ_lo]
  have hq₂ : criticalQ ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hqL : 3/2 ≤ criticalQ := by linarith [criticalQ_lo]
  have he : |e| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  have hE : e^2 ≤ 1 := by nlinarith [mul_nonneg he₀ (sub_nonneg.mpr he₁)]
  have hTang := rpow_one_add_le_one_add_mul_self
    (s := -(e^2)) (by linarith : -1 ≤ -(e^2))
    (by positivity : 0 ≤ criticalQ / 2) (by linarith : criticalQ / 2 ≤ 1)
  have hV : (1 - e^2) ^ (criticalQ/2) ≤ 1 - (3/4)*e^2 := by
    rw [sub_eq_add_neg]
    refine hTang.trans ?_
    have hcmp := mul_le_mul_of_nonneg_right (show (3/4 : ℝ) ≤ criticalQ / 2 by linarith)
      (sq_nonneg e)
    linarith
  exact (balancedFarIncrement_le_power hq₀ hq₂ he Z s).trans
    (mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg (abs_nonneg s) _))

private theorem large_chart_coefficients {l e : ℝ} (hl : 0 ≤ l) (hlU : l ≤ 74/4096)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) :
    ∃ K F : ℝ, (e + 9*l)^criticalQ ≤ K ∧ 0 ≤ 1-K ∧
      1 - (3/4)*e^2 ≤ F ∧ 0 ≤ F ∧
      (199/500)*(1-K) - (204/1000)*F ≥ 1/512 := by
  have hq₀ : 0 ≤ criticalQ := by linarith [criticalQ_lo]
  have hqL : 3/2 ≤ criticalQ := by linarith [criticalQ_lo]
  have hR : 0 ≤ e + 9*l := by positivity
  by_cases he : e ≤ 2/5
  · refine ⟨43/100, 1, ?_, by norm_num, ?_, by norm_num, by norm_num⟩
    · have hcross : (563/1000:ℝ)^(3/2:ℝ) ≤ 43/100 := by
        simpa only [Nat.cast_ofNat] using
          (natRat_rpow_le_iff (a := 563) (c := 43) (m := 3) (n := 2)
            (by decide : 0 < (1000:ℕ)) (by decide : 0 < (100:ℕ)) (by decide)).2 (by decide)
      exact (Real.rpow_le_rpow hR (by linarith : e+9*l ≤ 563/1000) hq₀).trans
        ((Real.rpow_le_rpow_of_exponent_ge (by norm_num : 0 < (563/1000:ℝ))
          (by norm_num) hqL).trans hcross)
    · nlinarith only [sq_nonneg e]
  · refine ⟨27/50, 22/25, ?_, by norm_num, ?_, by norm_num, by norm_num⟩
    · have hcross : (663/1000:ℝ)^(3/2:ℝ) ≤ 27/50 := by
        simpa only [Nat.cast_ofNat] using
          (natRat_rpow_le_iff (a := 663) (c := 27) (m := 3) (n := 2)
            (by decide : 0 < (1000:ℕ)) (by decide : 0 < (50:ℕ)) (by decide)).2 (by decide)
      exact (Real.rpow_le_rpow hR (by linarith : e+9*l ≤ 663/1000) hq₀).trans
        ((Real.rpow_le_rpow_of_exponent_ge (by norm_num : 0 < (663/1000:ℝ))
          (by norm_num) hqL).trans hcross)
    · nlinarith only [sq_nonneg (e - 2/5), lt_of_not_ge he]

private theorem g1_large_gap {μ l e p s z : ℝ}
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 204/1000) (hl₀ : 0 ≤ l) (hl₁ : l ≤ 74/4096)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hz : |z| ≤ 8*|p|) (hs : |p| ≤ |s|) :
    (1/512) * |s|^criticalQ ≤ balancedFacetGap criticalQ μ l e p s z := by
  let q := criticalQ
  let R := e + 9*l
  let A := balancedEvenGap q p s
  have hq : 1 < q := (by norm_num : (1 : ℝ) < 1054/665).trans_le criticalQ_lo
  have hq₂ : q ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hμ : 0 ≤ 1-μ := by linarith
  have hR₀ : 0 ≤ R := by dsimp [R]; positivity
  have hR : R ≤ 1 := by dsimp [R]; linarith
  have hD : |z-p| ≤ 9*|s| := by
    have ht := abs_add_le z (-p)
    rw [abs_neg, ← sub_eq_add_neg] at ht
    linarith only [ht, hz, hs]
  have hNear : |balancedNearShift l e l p s z| ≤ R * |s| := by
    rw [balancedNearShift_facet]
    calc
      _ ≤ e*|s| + l*|z-p| := by
        simpa only [abs_mul, abs_of_nonneg he₀, abs_of_nonneg hl₀] using
          abs_add_le (e*s) (l*(z-p))
      _ ≤ e*|s| + l*(9*|s|) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hD hl₀) _
      _ = _ := by dsimp [R]; ring
  obtain ⟨K, F, hK, hK₀, hF, hF₀, hC⟩ := large_chart_coefficients hl₀ hl₁ he₀ he₁
  have hA : 0 ≤ A := evenGap_nonneg hq.le p s
  have hA₁ : (1/2) * |s|^q ≤ A := evenGap_large_lower hs
  have hS := Real.rpow_nonneg (abs_nonneg s) q
  have hNearCost := mul_le_mul_of_nonneg_left
    ((evenGap_shrink hq hq₂ hR hR₀ hNear).trans (mul_le_mul_of_nonneg_right hK hA)) hμ
  have hH := mul_le_mul_of_nonneg_left
    ((far_increment_large_bound he₀ he₁ (balancedFarCenter l l p z) s).trans
      (mul_le_mul_of_nonneg_right hF hS)) hμ₀
  have hJ : 0 ≤ balancedJensenGap q l p z := by
    have h := (absPower_convex hq.le).2 (mem_univ z) (mem_univ p)
      (by linarith : 0 ≤ 1-l) hl₀ (by ring : 1-l+l=1)
    simp only [smul_eq_mul] at h
    exact sub_nonneg.mpr h
  have hBase : 199/250 ≤ 1-μ := by linarith
  have hCrit := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hBase hK₀) hA
  have hCM := mul_le_mul_of_nonneg_left hA₁ (mul_nonneg (by norm_num : (0:ℝ) ≤ 199/250) hK₀)
  have hFar := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ₁ hF₀) hS
  have hMargin := mul_le_mul_of_nonneg_right hC hS
  unfold balancedFacetGap
  change (1/512) * |s|^q ≤ μ * balancedJensenGap q l p z +
    (1-μ*(1-l)) * A - (1-μ) * balancedEvenGap q p (balancedNearShift l e l p s z) -
    μ * balancedFarIncrement q e (balancedFarCenter l l p z) s
  nlinarith only [hNearCost, hH, hCrit, hCM, hFar, hMargin, mul_nonneg hμ₀ hJ,
    mul_nonneg (mul_nonneg hμ₀ hl₀) hA]

/-- For every written G1 slab, the bounded-z facet gap has a common positive
margin in the large-|s| chart. -/
theorem g1_slab_bounded_z_large_s_gap (i : Fin 13) {l e p s z : ℝ}
    (hl₀ : g1SlabLeft i ≤ l) (hl₁ : l ≤ g1SlabRight i)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hz : |z| ≤ 8*|p|) (hs : |p| ≤ |s|) :
    (1/512) * |s|^criticalQ ≤ balancedFacetGap criticalQ (g1SlabWeight i) l e p s z := by
  obtain ⟨hL, _, hU, hμ, hμU⟩ := slab_ranges i
  exact g1_large_gap hμ.le hμU (hL.le.trans hl₀) (hl₁.trans hU) he₀ he₁ hz hs

end HlawkaSchatten.BelowExponent
