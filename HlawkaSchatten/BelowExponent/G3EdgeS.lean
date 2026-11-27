/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3
import all HlawkaSchatten.BelowExponent.G1Large
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The transverse chart at small G3 ratios, including the zero-ratio limit. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set Filter
open scoped Topology
open private absPower_deriv from HlawkaSchatten.BelowExponent.G1Large

private theorem edge_exponent : (19 / 12 : ℝ) ≤ criticalQ ∧ criticalQ ≤ 8 / 5 :=
  ⟨by linarith only [criticalQ_bracket.1], by linarith only [criticalQ_bracket.2]⟩

private theorem edge_q_one : 1 < criticalQ := by linarith only [edge_exponent.1]

private noncomputable def power (x : ℝ) : ℝ := |x| ^ criticalQ

private noncomputable def powerSlope (x : ℝ) : ℝ :=
  criticalQ * (if 0 ≤ x then |x| ^ (criticalQ - 1) else -|x| ^ (criticalQ - 1))

private theorem power_derivative (x : ℝ) : HasDerivAt power (powerSlope x) x :=
  absPower_deriv edge_q_one x

private theorem powerSlope_zero : powerSlope 0 = 0 := by
  simp [powerSlope, Real.zero_rpow (sub_ne_zero.mpr edge_q_one.ne')]

private theorem powerSlope_neg (x : ℝ) : powerSlope (-x) = -powerSlope x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [powerSlope, h.not_ge, neg_nonneg.mpr h.le, abs_neg]
  · simp [powerSlope_zero]
  · simp [powerSlope, h.le, (neg_neg_of_pos h).not_ge, abs_neg]

private theorem two_power_pred : (2 : ℝ) ^ (criticalQ - 2) = 3 / 4 := by
  rw [Real.rpow_sub (by norm_num : 0 < (2 : ℝ)), two_rpow_criticalQ, Real.rpow_two]
  norm_num

private theorem powerSlope_secant_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 2) (hxy : x ≤ y) :
    (2 / 3 : ℝ) * (y - x) ≤ powerSlope y - powerSlope x := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · simp
  let f (w : ℝ) := criticalQ * w ^ (criticalQ - 1)
  let df (w : ℝ) := (criticalQ * (criticalQ - 1)) * w ^ (criticalQ - 2)
  have hcont : Continuous f :=
    (Real.continuous_rpow_const (sub_nonneg.mpr edge_q_one.le)).const_mul _
  have hdiff (w : ℝ) (hw : w ∈ Ioo x y) : HasDerivAt f (df w) w := by
    have hw₀ := hx.trans_lt hw.1
    have h := (Real.hasDerivAt_rpow_const (p := criticalQ - 1) (Or.inl hw₀.ne')).const_mul criticalQ
    simpa only [f, df, mul_assoc, show criticalQ - 1 - 1 = criticalQ - 2 by ring] using h
  obtain ⟨w, hw, he⟩ := exists_hasDerivAt_eq_slope f df hxy hcont.continuousOn hdiff
  have hpos := hx.trans_lt hw.1
  have hpow := Real.rpow_le_rpow_of_nonpos hpos (hw.2.le.trans hy)
    (show criticalQ - 2 ≤ 0 by linarith only [edge_exponent.2])
  rw [two_power_pred] at hpow
  have hq : (0 : ℝ) ≤ criticalQ * (criticalQ - 1) := by
    exact mul_nonneg (zero_le_one.trans edge_q_one.le) (sub_nonneg.mpr edge_q_one.le)
  have hc : (133 / 144 : ℝ) ≤ criticalQ * (criticalQ - 1) := by
    calc
      _ = (19 / 12 : ℝ) * (19 / 12 - 1) := by norm_num
      _ ≤ _ := mul_le_mul edge_exponent.1 (sub_le_sub_right edge_exponent.1 1)
        (by norm_num) (zero_le_one.trans edge_q_one.le)
  have hbound : (2 / 3 : ℝ) ≤ df w := calc
    _ ≤ (133 / 144 : ℝ) * (3 / 4) := by norm_num
    _ ≤ _ := mul_le_mul hc hpow (by norm_num) hq
  rw [he] at hbound
  have hf := (le_div_iff₀ (sub_pos.mpr hxy)).1 hbound
  simpa [f, powerSlope, hx, hx.trans hxy.le, abs_of_nonneg] using hf

private theorem powerSlope_secant {x y : ℝ} (hx : -2 ≤ x) (hy : y ≤ 2) (hxy : x ≤ y) :
    (2 / 3 : ℝ) * (y - x) ≤ powerSlope y - powerSlope x := by
  by_cases h : 0 ≤ x
  · exact powerSlope_secant_nonneg h hy hxy
  by_cases hy₀ : y ≤ 0
  · have hn := powerSlope_secant_nonneg (neg_nonneg.mpr hy₀) (neg_le.mpr hx) (neg_le_neg hxy)
    rw [powerSlope_neg, powerSlope_neg] at hn
    linarith only [hn]
  · have hleft := powerSlope_secant_nonneg (x := 0) (y := -x) le_rfl (neg_le.mpr hx)
      (neg_nonneg.mpr (le_of_not_ge h))
    have hright := powerSlope_secant_nonneg (x := 0) (y := y) le_rfl hy (le_of_not_ge hy₀)
    rw [powerSlope_neg, powerSlope_zero] at hleft
    rw [powerSlope_zero] at hright
    linarith only [hleft, hright]

private theorem powerSlope_abs_le {x : ℝ} (hx : |x| ≤ 10) : |powerSlope x| ≤ 32 / 5 := by
  have hp : (10 : ℝ) ^ (3 / 5 : ℝ) ≤ 4 := by
    exact (rpow_natFraction_le_iff (x := 10) (y := 4) (m := 3) (n := 5)
      (by norm_num) (by norm_num) (by decide)).mpr (by norm_num)
  have ha := Real.rpow_le_rpow (abs_nonneg x) hx (sub_nonneg.mpr edge_q_one.le)
  have hb := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10)
    (show criticalQ - 1 ≤ 3 / 5 by linarith only [edge_exponent.2])
  have hpow := (ha.trans hb).trans hp
  have he : |powerSlope x| = criticalQ * |x| ^ (criticalQ - 1) := by
    rw [powerSlope, abs_mul, abs_of_pos (zero_lt_one.trans edge_q_one)]
    split <;> simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rw [he]
  exact (mul_le_mul edge_exponent.2 hpow (Real.rpow_nonneg (abs_nonneg x) _)
    (by norm_num : (0 : ℝ) ≤ 8 / 5)).trans_eq (by norm_num)

private theorem power_abs_sub_le {x y : ℝ} (hx : -10 ≤ x) (hy : y ≤ 10) (hxy : x ≤ y) :
    |power y - power x| ≤ (32 / 5 : ℝ) * (y - x) := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · simp
  have hd : Differentiable ℝ power := fun w => (power_derivative w).differentiableAt
  have hcont := hd.continuous
  obtain ⟨w, hw, he⟩ := exists_hasDerivAt_eq_slope power powerSlope hxy hcont.continuousOn
    (fun w _ => power_derivative w)
  have h := powerSlope_abs_le (abs_le.mpr ⟨hx.trans hw.1.le, hw.2.le.trans hy⟩)
  rw [he, abs_div, abs_of_pos (sub_pos.mpr hxy)] at h
  exact (div_le_iff₀ (sub_pos.mpr hxy)).1 h

private noncomputable def pairMean (p w : ℝ) : ℝ := (power (p + w) + power (p - w)) / 2

private theorem pairMean_deriv (p w : ℝ) :
    HasDerivAt (pairMean p) ((powerSlope (p + w) - powerSlope (p - w)) / 2) w := by
  have h₁ := (power_derivative (p + w)).comp w ((hasDerivAt_id w).const_add p)
  have h₂ := (power_derivative (p - w)).comp w ((hasDerivAt_id w).const_sub p)
  change HasDerivAt (fun x : ℝ => (power (p + x) + power (p - x)) / 2) _ w
  simpa only [Function.comp_def, Pi.add_apply, id_eq, mul_one, mul_neg_one, ← sub_eq_add_neg] using
    (h₁.add h₂).div_const 2

private theorem pairMean_sub_lower {p v : ℝ} (hp : |p| ≤ 1) (hv : 49 / 100 ≤ v) (hv₁ : v ≤ 1) :
    (2 / 3 : ℝ) * (49 / 100) * (1 - v) ≤ pairMean p 1 - pairMean p v := by
  rcases eq_or_lt_of_le hv₁ with rfl | hv₁
  · simp
  have hd : Differentiable ℝ (pairMean p) := fun w => (pairMean_deriv p w).differentiableAt
  have hcont := hd.continuous
  obtain ⟨w, hw, he⟩ := exists_hasDerivAt_eq_slope (pairMean p)
    (fun w => (powerSlope (p + w) - powerSlope (p - w)) / 2) hv₁ hcont.continuousOn
      (fun w _ => pairMean_deriv p w)
  have hlo := (abs_le.mp hp).1
  have hhi := (abs_le.mp hp).2
  have h := powerSlope_secant (x := p - w) (y := p + w)
    (by linarith only [hlo, hw.2]) (by linarith only [hhi, hw.2]) (by linarith only [hv, hw.1])
  have hd : (2 / 3 : ℝ) * (49 / 100) ≤ (powerSlope (p + w) - powerSlope (p - w)) / 2 := by
    linarith only [h, hv, hw.1]
  rw [he] at hd
  exact (le_div_iff₀ (sub_pos.mpr hv₁)).1 hd

private theorem edge_weight_bounds {h σ : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 7 / 10000) : 0 ≤ g3Weight h σ ∧ g3Weight h σ ≤ 1 / 50 := by
  have hp : (7 / 10000 : ℝ) ^ (12 / 25 : ℝ) ≤ 1 / 32 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (natRat_rpow_le_iff (a := 7) (b := 10000) (c := 1) (d := 32) (m := 12) (n := 25)
        (by decide) (by decide) (by decide)).mpr (by decide +kernel)
  have hs := (Real.rpow_le_rpow hσ₀ hσ₁ (by norm_num : (0 : ℝ) ≤ 12 / 25)).trans hp
  have he : 0 ≤ 1 + h / 16 := by linarith only [hh₀]
  have hu : 1 + h / 16 ≤ (17 / 16 : ℝ) := by linarith only [hh₁]
  unfold g3Weight
  rw [ite_eq_left (show σ < 3 / 20 by linarith only [hσ₁]), one_mul]
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) he) (Real.rpow_nonneg hσ₀ _), ?_⟩
  calc
    _ ≤ (3 / 5 : ℝ) * (17 / 16) * (1 / 32) := by
      gcongr
    _ ≤ _ := by norm_num

/-- Uniform gap on the S chart for the actual common G3 weight. The endpoints
`h = 0` and `σ = 0` belong to the undivided inequality. -/
theorem g3_transverse_edge_margin {h σ p z : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1 / (2 - σ / (2 - σ)))
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 7 / 10000) (hp : |p| ≤ 1) (hz : |z| ≤ 8) :
    (83 / 2500 : ℝ) * h ≤ g3FacetGap h σ p 1 z := by
  let k := σ / (2 - σ)
  let μ := g3Weight h σ
  let a := 1 + k * (p - z)
  let v := 1 - h * a
  let U := z + h * a
  have hσ : 0 < 2 - σ := by linarith only [hσ₁]
  have hk₀ : 0 ≤ k := div_nonneg hσ₀ hσ.le
  have hk : k ≤ 7 / 19993 := (div_le_iff₀ hσ).2 (by linarith only [hσ₁])
  have hh : h ≤ 501 / 1000 := calc
    _ ≤ _ := hh₁
    _ ≤ _ := (div_le_iff₀ (by linarith only [hk] : 0 < 2 - k)).2 (by linarith only [hk])
  have hμ : 0 ≤ μ ∧ μ ≤ 1 / 50 := edge_weight_bounds hh₀ (hh.trans (by norm_num)) hσ₀ hσ₁
  have hpd := abs_le.mp hp
  have hzd := abs_le.mp hz
  have hl : (-9 : ℝ) ≤ p - z := by linarith only [hpd.1, hzd.2]
  have hu : p - z ≤ 9 := by linarith only [hpd.2, hzd.1]
  have ha₀ : 249 / 250 ≤ a := by
    dsimp [a]
    linarith only [mul_le_mul_of_nonneg_left hl hk₀, hk]
  have ha₁ : a ≤ 251 / 250 := by
    dsimp [a]
    linarith only [mul_le_mul_of_nonneg_left hu hk₀, hk]
  have ha : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 249 / 250).trans ha₀
  have hha : 0 ≤ h * a := mul_nonneg hh₀ ha
  have hha' : h * a ≤ (501 / 1000 : ℝ) * (251 / 250) :=
    mul_le_mul hh ha₁ ha (by norm_num)
  have hv : 49 / 100 ≤ v := by dsimp [v]; linarith only [hha']
  have hv₁ : v ≤ 1 := by dsimp [v]; linarith only [hha]
  have hnear : (8 / 25 : ℝ) * h ≤ pairMean p 1 - pairMean p v := calc
    _ ≤ ((2 / 3 : ℝ) * (49 / 100) * a) * h :=
      mul_le_mul_of_nonneg_right (by linarith only [ha₀]) hh₀
    _ = (2 / 3 : ℝ) * (49 / 100) * (1 - v) := by dsimp [v]; ring
    _ ≤ _ := pairMean_sub_lower hp hv hv₁
  have hzU : z ≤ U := by dsimp [U]; linarith only [hha]
  have hU : U ≤ 10 := by dsimp [U]; linarith only [hzd.2, hha']
  have hfar : power U - power z ≤ 7 * h := calc
    _ ≤ (32 / 5 : ℝ) * (U - z) :=
      (le_abs_self _).trans (power_abs_sub_le (by linarith only [hzd.1]) hU hzU)
    _ = ((32 / 5 : ℝ) * a) * h := by dsimp [U]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [ha₁]) hh₀
  have hfarPair : power (U - 2) - power U ≤ 14 := by
    have ha := power_abs_sub_le (x := U - 2) (y := U)
      (by linarith only [hzU, hzd.1]) hU (by linarith)
    linarith only [(abs_le.mp ha).1]
  have hzPow : power z ≤ 27 := calc
    _ ≤ (8 : ℝ) ^ criticalQ := Real.rpow_le_rpow (abs_nonneg z) hz (zero_le_one.trans edge_q_one.le)
    _ = _ := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num [Real.rpow_ofNat],
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        two_rpow_criticalQ, Real.rpow_ofNat]
      norm_num
  have hB : 0 ≤ pairMean p 1 :=
    div_nonneg (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)) (by norm_num)
  have hkC : -(1 / 50 : ℝ) ≤ k * (pairMean p 1 - power z) := by
    have hc : (-27 : ℝ) ≤ pairMean p 1 - power z := by linarith only [hzPow, hB]
    linarith only [mul_le_mul_of_nonneg_left hc hk₀, hk]
  have hcost : -(14 + 1 / 50 : ℝ) * h ≤
      h * k * (pairMean p 1 - power z) - (power U - power z) - h / 2 * (power (U - 2) - power U) := by
    linarith only [mul_le_mul_of_nonneg_left hkC hh₀, hfar,
      mul_le_mul_of_nonneg_left hfarPair (show 0 ≤ h / 2 by positivity)]
  have hU₀ : balancedFarCenter (h * k) (h * k) p z - (1 + (1 - h)) * 1 = U - 2 := by
    dsimp [balancedFarCenter, U, a]; ring
  have hU₁ : balancedFarCenter (h * k) (h * k) p z + (1 - (1 - h)) * 1 = U := by
    dsimp [balancedFarCenter, U, a]; ring
  have hvEq : balancedNearShift (h * k) (1 - h) (h * k) p 1 z = v := by
    dsimp [balancedNearShift, v, a]; ring
  have hgap : g3FacetGap h σ p 1 z = (1 - μ) * (pairMean p 1 - pairMean p v) +
      μ * (h * k * (pairMean p 1 - power z) - (power U - power z) -
        h / 2 * (power (U - 2) - power U)) := by
    change balancedFacetGap criticalQ μ (h * k) (1 - h) p 1 z = _
    unfold balancedFacetGap balancedJensenGap balancedFarIncrement
    rw [hvEq, hU₀, hU₁]
    unfold balancedEvenGap pairMean power
    ring
  calc
    _ ≤ (1 - μ) * ((8 / 25 : ℝ) * h) + μ * (-(14 + 1 / 50 : ℝ) * h) := by
      nlinarith only [mul_le_mul_of_nonneg_right hμ.2 hh₀]
    _ ≤ _ := hgap.symm ▸ add_le_add (mul_le_mul_of_nonneg_left hnear (by linarith only [hμ.2]))
      (mul_le_mul_of_nonneg_left hcost hμ.1)

theorem g3_transverse_edge_chart {h σ p z : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 7 / 10000)
    (hh : 0 < h) (hh₁ : h ≤ 1 / (2 - σ / (2 - σ))) (hp : |p| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ p 1 z :=
  (mul_nonneg (by norm_num) hh.le).trans (g3_transverse_edge_margin hh.le hh₁ hσ.le hσ₁ hp hz)

private theorem gap_zero_ratio (h p z : ℝ) :
    g3FacetGap h 0 p 1 z = balancedEvenGap criticalQ p 1 - balancedEvenGap criticalQ p (1 - h) := by
  simp [g3FacetGap, g3Weight, Real.zero_rpow (show (12 / 25 : ℝ) ≠ 0 by norm_num),
    balancedFacetGap, balancedNearShift]

/-- At fixed height the scaled gap has a zero-ratio limit independent of the third row coordinate. -/
theorem g3_transverse_ratio_limit (h p z : ℝ) :
    Tendsto (fun σ => g3FacetGap h σ p 1 z / h) (𝓝 0)
      (𝓝 ((balancedEvenGap criticalQ p 1 - balancedEvenGap criticalQ p (1 - h)) / h)) := by
  let G (σ : ℝ) := balancedFacetGap criticalQ ((3 / 5) * (1 + h / 16) * σ ^ (12 / 25 : ℝ))
    (h * (σ / (2 - σ))) (1 - h) p 1 z
  have hc : ContinuousAt G 0 := by
    dsimp only [G, balancedFacetGap, balancedJensenGap, balancedEvenGap, balancedNearShift,
      balancedFarIncrement, balancedFarCenter]
    fun_prop (disch := first
      | exact Or.inr (zero_le_one.trans edge_q_one.le)
      | exact Or.inr (by norm_num)
      | norm_num)
  have he : (fun σ => g3FacetGap h σ p 1 z) =ᶠ[𝓝 0] G := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 3 / 20 by norm_num)] with σ hs
    change σ < 3 / 20 at hs
    dsimp only [G, g3FacetGap, g3Weight]
    rw [ite_eq_left hs, one_mul]
  have hd := (hc.congr_of_eventuallyEq he).div_const h
  change Tendsto (fun σ => g3FacetGap h σ p 1 z / h) (𝓝 0) (𝓝 (g3FacetGap h 0 p 1 z / h)) at hd
  rwa [gap_zero_ratio] at hd

private theorem sign_gap_zero_ratio (h z : ℝ) :
    g3FacetGap h 0 0 1 z = 1 - power (1 - h) := by
  simp [gap_zero_ratio, balancedEvenGap, power]
  rw [abs_sub_comm h 1]
  ring

/-- At zero ratio, the sign row has scaled gap at least `4/3` throughout the limiting height range. -/
theorem g3_transverse_sign_margin_zero_ratio {h : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1 / 2) (z : ℝ) :
    (4 / 3 : ℝ) * h ≤ g3FacetGap h 0 0 1 z := by
  have hh : 0 ≤ 1 - h := by linarith only [hh₁]
  have hHalf : (1 / 2 : ℝ) ^ criticalQ ≤ 1 / 3 := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2),
      Real.one_rpow, two_rpow_criticalQ]
  have hc := rpow_le_upperChord (q := criticalQ) (a := 1) (b := 1 / 2) (y := 1 - h) (u := 2 * h)
    (upperA := 1) (upperB := 1 / 3) edge_q_one.le (by norm_num) (by norm_num) hh
    (by linarith only [hh₀]) (by linarith only [hh₁]) (by ring_nf; rfl)
    (by rw [Real.one_rpow]) hHalf
  rw [sign_gap_zero_ratio, power, abs_of_nonneg hh]
  linarith only [hc]

/-- The normalized sign-row gap tends to the exact exponent as the height tends to zero. -/
theorem g3_transverse_sign_limit_zero_height (z : ℝ) :
    Tendsto (fun h => g3FacetGap h 0 0 1 z / h) (𝓝[>] 0) (𝓝 criticalQ) := by
  let f (h : ℝ) := 1 - power (1 - h)
  have hP : HasDerivAt power criticalQ ((fun h : ℝ => 1 - h) 0) := by
    simpa [powerSlope] using power_derivative 1
  have hd : HasDerivAt f criticalQ 0 := by
    have hc := hP.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub 1)
    change HasDerivAt (fun h => 1 - power (1 - h)) criticalQ 0
    simpa only [Function.comp_def, id_eq, mul_neg_one, neg_neg] using hc.const_sub 1
  have h0 : f 0 = 0 := by simp [f, power]
  simpa only [zero_add, h0, sub_zero, smul_eq_mul, ← div_eq_inv_mul, sign_gap_zero_ratio, f] using
    hd.tendsto_slope_zero_right

end HlawkaSchatten.BelowExponent
