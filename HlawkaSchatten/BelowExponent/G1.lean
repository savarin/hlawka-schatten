/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Exponents
public import HlawkaSchatten.BelowExponent.Scalar
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Quantitative G1 estimates in the far row chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

private theorem criticalQ_lower : 19 / 12 ≤ criticalQ :=
  le_trans (by norm_num) criticalQ_bracket.1.le

private theorem criticalQ_upper : criticalQ ≤ 2 :=
  le_trans criticalQ_bracket.2.le (by norm_num)

private theorem absPower_convex {q : ℝ} (hq : 1 ≤ q) :
    ConvexOn ℝ univ (fun x : ℝ => |x| ^ q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hAbs : |a * x + b * y| ≤ a * |x| + b * |y| := by
    simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x) (b * y)
  refine (Real.rpow_le_rpow (abs_nonneg _) hAbs (zero_le_one.trans hq)).trans ?_
  simpa only [smul_eq_mul] using (convexOn_rpow hq).2
    (mem_Ici.mpr (abs_nonneg x)) (mem_Ici.mpr (abs_nonneg y)) ha hb hab

private theorem evenGap_convex {q : ℝ} (hq : 1 ≤ q) (p : ℝ) :
    ConvexOn ℝ univ (balancedEvenGap q p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hP := (absPower_convex hq).2 (mem_univ (p+x)) (mem_univ (p+y)) ha hb hab
  have hM := (absPower_convex hq).2 (mem_univ (p-x)) (mem_univ (p-y)) ha hb hab
  simp only [smul_eq_mul] at hP hM ⊢
  rw [show a * (p+x) + b * (p+y) = p + (a*x+b*y) by
    calc
      _ = (a+b)*p + (a*x+b*y) := by ring
      _ = _ := by rw [hab, one_mul]] at hP
  rw [show a * (p-x) + b * (p-y) = p - (a*x+b*y) by
    calc
      _ = (a+b)*p - (a*x+b*y) := by ring
      _ = _ := by rw [hab, one_mul]] at hM
  unfold balancedEvenGap
  nlinarith only [hP, hM, congrArg (fun k : ℝ => k * |p| ^ q) hab]

private theorem evenGap_lower_power {q : ℝ} (hq : 1 ≤ q) (p s : ℝ) :
    |s| ^ q - |p| ^ q ≤ balancedEvenGap q p s := by
  have h := (absPower_convex hq).2 (mem_univ (p+s)) (mem_univ (s-p))
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  simp only [smul_eq_mul, show (1/2 : ℝ) * (p+s) + 1/2 * (s-p) = s by ring,
    abs_sub_comm s p] at h
  unfold balancedEvenGap
  linarith

private theorem evenGap_upper_power {q : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q ≤ 2) (p s : ℝ) :
    balancedEvenGap q p s ≤ |s| ^ q := by
  have h := balancedFarIncrement_le_power hq₀ hq₂ (e := 0) (by norm_num) p s
  simp only [balancedFarIncrement, zero_pow two_ne_zero, sub_zero,
    add_zero, one_mul, Real.one_rpow] at h
  unfold balancedEvenGap
  linarith

private theorem adjustedPower_convex_monotone {q : ℝ} (hq₀ : 3/2 ≤ q) (hq₂ : q ≤ 2) :
    ConvexOn ℝ (Icc 0 1) (fun x : ℝ => x ^ q - x ^ 2 / 4) ∧
      MonotoneOn (fun x : ℝ => x ^ q - x ^ 2 / 4) (Icc 0 1) := by
  let g (x : ℝ) := x ^ q - x ^ 2 / 4
  let g₁ (x : ℝ) := q * x ^ (q-1) - x / 2
  let g₂ (x : ℝ) := q * (q-1) * x ^ (q-2) - 1/2
  have hg : Continuous g := (Real.continuous_rpow_const (by linarith)).sub
    ((continuous_id.pow 2).div_const 4)
  have hd (x : ℝ) (hx : x ∈ interior (Icc (0:ℝ) 1)) : HasDerivAt g (g₁ x) x := by
    rw [interior_Icc] at hx
    have h := (Real.hasDerivAt_rpow_const (x := x) (p := q) (Or.inl hx.1.ne')).sub
      (((hasDerivAt_id x).pow 2).div_const 4)
    simp only [id_eq, Nat.reduceSub, pow_one, mul_one, Nat.cast_ofNat] at h
    rw [show q * x ^ (q - 1) - 2*x/4 = g₁ x by dsimp [g₁]; ring] at h
    exact h
  have hd₂ (x : ℝ) (hx : x ∈ interior (Icc (0:ℝ) 1)) : HasDerivAt g₁ (g₂ x) x := by
    rw [interior_Icc] at hx
    have h := ((Real.hasDerivAt_rpow_const (x := x) (p := q-1) (Or.inl hx.1.ne')).const_mul q).sub
      ((hasDerivAt_id x).div_const 2)
    rw [show q * ((q-1) * x ^ (q-1-1)) - 1/2 = g₂ x by
      dsimp [g₂]
      rw [show q - 1 - 1 = q - 2 by ring]
      ring] at h
    exact h
  constructor
  · refine convexOn_of_hasDerivWithinAt2_nonneg (f := g) (f' := g₁) (f'' := g₂)
      (convex_Icc _ _) hg.continuousOn (fun x hx => (hd x hx).hasDerivWithinAt)
      (fun x hx => (hd₂ x hx).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hpow : 1 ≤ x ^ (q-2) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos hx.1 hx.2.le (sub_nonpos.mpr hq₂)
    have hc : 1/2 ≤ q * (q-1) := by nlinarith only [sq_nonneg (q-3/2), hq₀]
    dsimp [g₂]
    have hm := mul_le_mul_of_nonneg_left hpow ((by norm_num : (0:ℝ) ≤ 1/2).trans hc)
    linarith
  · refine monotoneOn_of_deriv_nonneg (f := g) (convex_Icc _ _) hg.continuousOn
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hd x hx).deriv]
    rw [interior_Icc] at hx
    have hpow := Real.self_le_rpow_of_le_one hx.1.le hx.2.le (show q-1 ≤ 1 by linarith)
    have hprod := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ q by linarith)
      (Real.rpow_nonneg hx.1.le (q-1))
    dsimp [g₁]
    linarith [hx.1]

private theorem evenGap_lower_quarter_sq {q p s : ℝ} (hq₀ : 3/2 ≤ q) (hq₂ : q ≤ 2)
    (hps : |p+s| ≤ 1) (hms : |p-s| ≤ 1) : s ^ 2 / 4 ≤ balancedEvenGap q p s := by
  obtain ⟨hConv, hMono⟩ := adjustedPower_convex_monotone hq₀ hq₂
  have hTriangle : |p| ≤ (|p+s| + |p-s|)/2 := by
    have h := abs_add_le (p+s) (p-s)
    rw [show p+s+(p-s) = 2*p by ring, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    linarith
  have hMid : (|p+s| + |p-s|)/2 ∈ Icc (0:ℝ) 1 := ⟨by positivity, by linarith⟩
  have hmono := hMono ⟨abs_nonneg p, hTriangle.trans hMid.2⟩ hMid hTriangle
  have hconv := hConv.2 (show |p+s| ∈ Icc (0:ℝ) 1 from ⟨abs_nonneg _, hps⟩)
    (show |p-s| ∈ Icc (0:ℝ) 1 from ⟨abs_nonneg _, hms⟩)
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  simp only [smul_eq_mul, show (1/2 : ℝ) * |p+s| + 1/2 * |p-s| =
    (|p+s| + |p-s|)/2 by ring] at hconv
  have h := hmono.trans hconv
  simp only [sq_abs] at h
  unfold balancedEvenGap
  nlinarith only [h]

private theorem evenGap_nonneg {q : ℝ} (hq : 1 ≤ q) (p s : ℝ) :
    0 ≤ balancedEvenGap q p s := by
  have h := (absPower_convex hq).2 (mem_univ (p+s)) (mem_univ (p-s))
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  simp only [smul_eq_mul, show (1/2 : ℝ) * (p+s) + 1/2 * (p-s) = p by ring] at h
  unfold balancedEvenGap
  linarith

private theorem half_pow_q : (1/2 : ℝ) ^ criticalQ = 1/3 := by
  rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 2),
    Real.one_rpow, two_rpow_criticalQ]

private theorem half_pow_pred : (1/2 : ℝ) ^ (criticalQ - 1) = 2/3 := by
  rw [Real.rpow_sub (by norm_num : (0:ℝ) < 1/2), Real.rpow_one, half_pow_q]
  norm_num

private theorem upper_length_pow_pred : (1/2048 : ℝ) ^ (criticalQ - 1) = (2/3 : ℝ)^11 := by
  rw [show (1/2048 : ℝ) = (1/2 : ℝ)^11 by norm_num,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/2) 11,
    mul_comm ((11:ℕ):ℝ), Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2),
    half_pow_pred, Real.rpow_natCast]

private theorem first_farCenter_lower {l p : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1/2048)
    (hp : |p| ≤ 1/8) : 1023/1024 ≤ balancedFarCenter l l p 1 := by
  obtain ⟨hpl, _⟩ := abs_le.mp hp
  have h := (mul_le_mul_of_nonneg_left (show 1-p ≤ 9/8 by linarith) hl₀).trans
    (mul_le_mul_of_nonneg_right hl₁ (by norm_num : (0:ℝ) ≤ 9/8))
  unfold balancedFarCenter
  nlinarith only [h]

private theorem far_absorption_first_normalized {l e p s : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1/2048)
    (he : |e| ≤ 1) (hp : |p| ≤ 1/8) :
    balancedFarIncrement criticalQ e (balancedFarCenter l l p 1) s ≤
      8 * balancedEvenGap criticalQ p s := by
  let q := criticalQ
  let Z := balancedFarCenter l l p 1
  have hqlo : 3/2 ≤ q := le_trans (by norm_num) criticalQ_lower
  have hqhi : q ≤ 2 := criticalQ_upper
  have hq₁ : 1 ≤ q := by linarith
  have hq₀ : 0 ≤ q := by linarith
  have hem := abs_le.mp he
  have hvar : 0 ≤ 1 - e^2 := by
    nlinarith only [mul_nonneg (show 0 ≤ 1+e by linarith [hem.1]) (sub_nonneg.mpr hem.2)]
  have hvar₁ : 1 - e^2 ≤ 1 := by nlinarith only [sq_nonneg e]
  by_cases hs : 1/2 ≤ |s|
  · have hpPow := Real.rpow_le_rpow (abs_nonneg p) (show |p| ≤ (1/2) * |s| by linarith) hq₀
    change |p| ^ criticalQ ≤ ((1/2) * |s|) ^ criticalQ at hpPow
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) (abs_nonneg s), half_pow_q] at hpPow
    have hA := evenGap_lower_power hq₁ p s
    have hs₀ : 0 ≤ |s| ^ criticalQ := Real.rpow_nonneg (abs_nonneg s) _
    have hF := (balancedFarIncrement_le_power hq₀ hqhi he Z s).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_one hvar hvar₁ (by linarith : 0 ≤ q/2)) hs₀)
    simp only [one_mul] at hF
    change balancedFarIncrement q e Z s ≤ _
    change |p|^q ≤ (1/3) * |s|^q at hpPow
    change 0 ≤ |s|^q at hs₀
    linarith only [hF, hA, hpPow, hs₀]
  · have hs' : |s| ≤ 1/2 := le_of_not_ge hs
    have hps : |p+s| ≤ 1 := (abs_add_le p s).trans (by linarith)
    have hms : |p-s| ≤ 1 := by
      rw [sub_eq_add_neg]
      exact (abs_add_le p (-s)).trans (by rw [abs_neg]; linarith)
    have hA := evenGap_lower_quarter_sq hqlo hqhi hps hms
    have hZ : 1/2 ≤ Z := le_trans (by norm_num) (first_farCenter_lower hl₀ hl₁ hp)
    have hZ₀ : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
    have hPow : |Z| ^ (q-2) ≤ 2 := calc
      _ ≤ (1/2 : ℝ) ^ (q-2) := Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by rwa [abs_of_pos hZ₀]) (sub_nonpos.mpr hqhi)
      _ ≤ (1/2 : ℝ) ^ (-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_ge
        (by norm_num) (by norm_num) (by linarith)
      _ = _ := by rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have hPow₀ : 0 ≤ |Z| ^ (q-2) := Real.rpow_nonneg (abs_nonneg Z) _
    have hP := mul_le_mul hvar₁ hPow hPow₀ (by norm_num : (0:ℝ) ≤ 1)
    have hc := mul_le_mul (show q/2 ≤ 1 by linarith) hP
      (mul_nonneg hvar hPow₀) (by norm_num : (0:ℝ) ≤ 1)
    simp only [one_mul] at hc
    have hf := (balancedFarIncrement_le_quadratic hq₀ hqhi he hZ₀.ne' s).trans
      (mul_le_mul_of_nonneg_right (by simpa only [mul_assoc] using hc) (sq_nonneg s))
    change balancedFarIncrement q e Z s ≤ _
    linarith only [hf, hA]

private noncomputable def firstFarJensenSlope : ℝ := (19/12) * (1023/1024)
private noncomputable def firstFarDriftCoefficient : ℝ := (3/2) * (2/3)^11 * (9/8)

private theorem first_far_jensen {l p : ℝ} (hl₀ : 0 < l) (hl₁ : l ≤ 1/2048)
    (hp : |p| ≤ 1/8) :
    l * (firstFarJensenSlope * (1-p) - 1) ≤ balancedJensenGap criticalQ l p 1 := by
  let Z := balancedFarCenter l l p 1
  have hlZ : 1023/1024 ≤ Z := first_farCenter_lower hl₀.le hl₁ hp
  have hZ₀ : 0 < Z := lt_of_lt_of_le (by norm_num) hlZ
  have hW : 0 < 1-p := by linarith [(abs_le.mp hp).2]
  have hdiff : 1 - Z = l * (1-p) := by dsimp [Z, balancedFarCenter]; ring
  have hZ₁ : Z < 1 := sub_pos.mp (hdiff ▸ mul_pos hl₀ hW)
  have hq : 1 ≤ criticalQ := le_trans (by norm_num) criticalQ_lower
  have hT := (convexOn_rpow hq).le_slope_of_hasDerivAt (mem_Ici.mpr hZ₀.le)
    (mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 1)) hZ₁
    (Real.hasDerivAt_rpow_const (p := criticalQ) (Or.inl hZ₀.ne'))
  simp only [slope_def_field, Real.one_rpow] at hT
  have hslope := (le_div_iff₀ (sub_pos.mpr hZ₁)).1 hT
  have hZPow := Real.self_le_rpow_of_le_one hZ₀.le hZ₁.le
    (show criticalQ-1 ≤ 1 by linarith [criticalQ_upper])
  have hpCoef : firstFarJensenSlope ≤ criticalQ * Z ^ (criticalQ-1) :=
    mul_le_mul criticalQ_lower (hlZ.trans hZPow) (by norm_num) (by linarith)
  have hcoef := mul_le_mul_of_nonneg_right hpCoef (sub_nonneg.mpr hZ₁.le)
  rw [hdiff] at hslope hcoef
  unfold balancedJensenGap
  change l * (firstFarJensenSlope * (1-p) - 1) ≤
    (1-l) * |(1:ℝ)| ^ criticalQ + l * |p| ^ criticalQ - |Z| ^ criticalQ
  rw [abs_one, Real.one_rpow, abs_of_pos hZ₀]
  nlinarith only [hslope, hcoef, mul_nonneg hl₀.le (Real.rpow_nonneg (abs_nonneg p) criticalQ)]

private theorem rpow_critical_split {x : ℝ} (hx : 0 < x) :
    x ^ criticalQ = x * x ^ (criticalQ - 1) := by
  rw [Real.rpow_sub hx, Real.rpow_one, mul_div_cancel₀ _ hx.ne']

private theorem first_far_near_split {l e p s : ℝ} (hl₀ : 0 < l) (hl₁ : l ≤ 1/2048)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hp : |p| ≤ 1/8) :
    balancedEvenGap criticalQ p (balancedNearShift l e l p s 1) ≤
      e * balancedEvenGap criticalQ p s + firstFarDriftCoefficient * l * (1-p) := by
  let q := criticalQ
  let d := 1-e
  let w := 1-p
  let v := l*w/d
  have hq : 1 ≤ q := le_trans (by norm_num) criticalQ_lower
  have hdL : 1/2 ≤ d := by dsimp [d]; linarith
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdL
  have hw : 0 < w := by dsimp [w]; linarith [(abs_le.mp hp).2]
  have hwU : w ≤ 9/8 := by dsimp [w]; linarith [(abs_le.mp hp).1]
  have hlw : 0 < l*w := mul_pos hl₀ hw
  have hv : 0 ≤ v := div_nonneg hlw.le hd.le
  have hpD := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1/2) hdL
    (show 0 ≤ q-1 by linarith)
  change (1/2:ℝ) ^ (criticalQ-1) ≤ d ^ (criticalQ-1) at hpD
  rw [half_pow_pred] at hpD
  have hdp := Real.rpow_pos_of_pos hd (criticalQ-1)
  have hL := Real.rpow_le_rpow hl₀.le hl₁ (show 0 ≤ criticalQ-1 by linarith [criticalQ_lower])
  rw [upper_length_pow_pred] at hL
  have hlPow : l ^ criticalQ ≤ (2/3:ℝ)^11 * l := by
    rw [rpow_critical_split hl₀, mul_comm ((2/3:ℝ)^11)]
    exact mul_le_mul_of_nonneg_left hL hl₀.le
  have hW := (Real.rpow_le_rpow hw.le hwU (show 0 ≤ criticalQ-1 by linarith [criticalQ_lower])).trans
    (Real.rpow_le_self_of_one_le (by norm_num) (show criticalQ-1 ≤ 1 by linarith [criticalQ_upper]))
  have hwPow : w ^ criticalQ ≤ (9/8) * w := by
    rw [rpow_critical_split hw, mul_comm (9/8 : ℝ)]
    exact mul_le_mul_of_nonneg_left hW hw.le
  have hD : d * |v| ^ criticalQ ≤ (3/2) * (l*w) ^ criticalQ := calc
    _ = (l*w) ^ criticalQ / d ^ (criticalQ-1) := by
      rw [abs_of_nonneg hv, show v = l*w/d by rfl, Real.div_rpow hlw.le hd.le,
        rpow_critical_split hd]
      field_simp [hd.ne', hdp.ne']
    _ ≤ _ := (div_le_iff₀ hdp).2 (by
      have h : 1 ≤ (3/2) * d ^ (criticalQ-1) := by linarith
      have := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hlw.le criticalQ)
      linarith)
  have hPower : (3/2) * (l*w) ^ criticalQ ≤ firstFarDriftCoefficient * l * w := calc
    _ = (3/2) * (l ^ criticalQ * w ^ criticalQ) := by rw [Real.mul_rpow hl₀.le hw.le]
    _ ≤ (3/2) * (((2/3:ℝ)^11 * l) * ((9/8) * w)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hlPow hwPow (Real.rpow_nonneg hw.le _) (by positivity)) (by norm_num)
    _ = _ := by unfold firstFarDriftCoefficient; ring
  have hDrift := (mul_le_mul_of_nonneg_left
    (evenGap_upper_power (zero_le_one.trans hq) criticalQ_upper p v) hd.le).trans
    (hD.trans hPower)
  have hConv := (evenGap_convex hq p).2 (mem_univ s) (mem_univ v)
    he₀ hd.le (by dsimp [d]; ring)
  simp only [smul_eq_mul] at hConv
  have heq : e*s + d*v = balancedNearShift l e l p s 1 := by
    rw [balancedNearShift_facet, show v = l*w/d by rfl, mul_div_cancel₀ _ hd.ne']
  rw [heq] at hConv
  linarith only [hConv, hDrift]

private theorem first_far_margin_normalized {l e p s : ℝ}
    (hl₀ : 0 < l) (hl₁ : l ≤ 1/2048) (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hp : |p| ≤ 1/8) :
    ((47/1000 : ℝ)/32) * l ≤ balancedFacetGap criticalQ (47/1000) l e p s 1 := by
  let μ : ℝ := 47/1000
  let A := balancedEvenGap criticalQ p s
  let J := balancedJensenGap criticalQ l p 1
  let D := firstFarDriftCoefficient * l * (1-p)
  let c := μ * firstFarJensenSlope - (1-μ) * firstFarDriftCoefficient
  have hm : 0 ≤ μ := by norm_num [μ]
  have hb : 0 ≤ 1-μ := by norm_num [μ]
  have hpw : 7/8 ≤ 1-p := by linarith [(abs_le.mp hp).2]
  have hc : 0 ≤ c := by norm_num [c, μ, firstFarJensenSlope, firstFarDriftCoefficient]
  have hcmp : μ/32 ≤ c * (7/8) - μ := by
    norm_num [c, μ, firstFarJensenSlope, firstFarDriftCoefficient]
  have hlin : μ/32 ≤ c * (1-p) - μ :=
    hcmp.trans (sub_le_sub_right (mul_le_mul_of_nonneg_left hpw hc) μ)
  have he : |e| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hq : 1 ≤ criticalQ := le_trans (by norm_num) criticalQ_lower
  have hA : 0 ≤ A := evenGap_nonneg hq p s
  have hcoef : 0 ≤ 1 - μ*(1-l) - (1-μ)*e - μ*8 := by
    dsimp [μ]
    nlinarith only [hl₀.le, he₁]
  have hNear := mul_le_mul_of_nonneg_left (first_far_near_split (s := s) hl₀ hl₁ he₀ he₁ hp) hb
  have hFar := mul_le_mul_of_nonneg_left
    (far_absorption_first_normalized (s := s) hl₀.le hl₁ he hp) hm
  have hJ := mul_le_mul_of_nonneg_left (first_far_jensen hl₀ hl₁ hp) hm
  change (μ/32)*l ≤ balancedFacetGap criticalQ μ l e p s 1
  calc
    _ = l*(μ/32) := by ring
    _ ≤ l*(c*(1-p)-μ) := mul_le_mul_of_nonneg_left hlin hl₀.le
    _ = μ*(l*(firstFarJensenSlope*(1-p)-1)) - (1-μ)*D := by dsimp [c, D]; ring
    _ ≤ μ*J - (1-μ)*D := sub_le_sub_right hJ _
    _ ≤ balancedFacetGap criticalQ μ l e p s 1 := by
      unfold balancedFacetGap
      dsimp [D, J, A]
      nlinarith only [hNear, hFar, mul_nonneg hcoef hA]

private theorem balancedFacetGap_scale (q μ l e a p s z : ℝ) :
    balancedFacetGap q μ l e (a*p) (a*s) (a*z) =
      |a|^q * balancedFacetGap q μ l e p s z := by
  have hrow : balancedRow (a*p) (a*s) (a*z) = a • balancedRow p s z := by
    funext j
    fin_cases j <;> simp [balancedRow, Pi.smul_apply] <;> ring
  have hf (x : ℝ) : |a*x|^q = |a|^q*|x|^q := by
    rw [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg x)]
  rw [← balanced_facet_gap_eq q μ l e (a*p) (a*s) (a*z),
    ← balanced_facet_gap_eq q μ l e p s z, hrow]
  simp only [rowEval_smul, Pi.smul_apply, smul_eq_mul, hf]
  simp_rw [mul_left_comm _ (|a|^q), ← Finset.mul_sum]
  exact (mul_sub _ _ _).symm

private theorem first_far_margin {l e p s z : ℝ}
    (hl₀ : 0 < l) (hl₁ : l ≤ 1/2048) (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2)
    (hfar : 8 * |p| ≤ |z|) :
    ((47/1000 : ℝ)/32) * l * |z| ^ criticalQ ≤ balancedFacetGap criticalQ (47/1000) l e p s z := by
  by_cases hz : z = 0
  · have hp : p = 0 := by
      rw [hz, abs_zero] at hfar
      exact abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg p))
    subst z
    subst p
    have he : |e| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hq : 1 ≤ criticalQ := le_trans (by norm_num) criticalQ_lower
    have h := balancedFacetGap_transverse_bound hq criticalQ_upper
      (μ := 47/1000) (l := l) (by norm_num) (by norm_num) he s
    have hcoef : 0 ≤ (1 - 3*(47/1000:ℝ)) * (1 - |e|) + (47/1000:ℝ)*l :=
      add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr he)) (mul_nonneg (by norm_num) hl₀.le)
    simp only [abs_zero, Real.zero_rpow (show criticalQ ≠ 0 by linarith), mul_zero]
    exact (mul_nonneg hcoef (Real.rpow_nonneg (abs_nonneg s) _)).trans h
  have hp : |p/z| ≤ 1/8 := by
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hz)).2 (by linarith)
  have h := mul_le_mul_of_nonneg_right
    (first_far_margin_normalized (s := s/z) hl₀ hl₁ he₀ he₁ hp)
    (Real.rpow_nonneg (abs_nonneg z) criticalQ)
  rw [mul_comm (balancedFacetGap criticalQ (47/1000) l e (p/z) (s/z) 1),
    ← balancedFacetGap_scale, mul_div_cancel₀ _ hz, mul_div_cancel₀ _ hz, mul_one] at h
  exact h

/-- Subtract an affine length margin from the third input coefficient. -/
private noncomputable def farMarginGamma (μ a l : ℝ) : Row :=
  fun j => balancedGamma μ l j - if j = 2 then a*l else 0

private theorem weightedRow_farMargin_iff (q μ a l e p s z : ℝ) :
    WeightedRow q (balancedProfile l e l) (balancedPi μ e) (farMarginGamma μ a l)
      (balancedRow p s z) ↔ a*l*|z|^q ≤ balancedFacetGap q μ l e p s z := by
  have hGamma : (∑ j, farMarginGamma μ a l j * |balancedRow p s z j| ^ q) =
      (∑ j, balancedGamma μ l j * |balancedRow p s z j| ^ q) - a*l*|z|^q := by
    simp (config := {decide := true}) [farMarginGamma, balancedRow, Fin.sum_univ_three]
    ring
  unfold WeightedRow
  rw [hGamma, ← balanced_facet_gap_eq q μ l e p s z]
  constructor <;> intro h <;> linarith only [h]

/-- On the first written G1 slab and the whole far-row chart, the upper-facet
gap is bounded below by the explicit affine length margin. The proof
interpolates the two certified endpoint rows with the same profile weights. -/
theorem g1_first_slab_far_gap {l e p s z : ℝ}
    (hl₀ : 1/4096 ≤ l) (hl₁ : l ≤ 2/4096) (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2)
    (hfar : 8 * |p| ≤ |z|) :
    ((47/1000 : ℝ)/32) * l * |z| ^ criticalQ ≤ balancedFacetGap criticalQ (47/1000) l e p s z := by
  let μ : ℝ := 47/1000
  let a := μ/32
  let u := 4096*l - 1
  have hu₀ : 0 ≤ u := by dsimp [u]; linarith
  have hu₁ : u ≤ 1 := by dsimp [u]; linarith
  have hq : 1 ≤ criticalQ := le_trans (by norm_num) criticalQ_lower
  have hπ := (isSimplex_balancedPi (μ := μ) (by norm_num [μ]) (by norm_num [μ])
    (show |e| ≤ 1 from abs_le.mpr ⟨by linarith, by linarith⟩)).1
  have hleft := (weightedRow_farMargin_iff criticalQ μ a (1/4096) e p s z).2
    (first_far_margin (by norm_num) (by norm_num) he₀ he₁ hfar)
  have hright := (weightedRow_farMargin_iff criticalQ μ a (2/4096) e p s z).2
    (first_far_margin (by norm_num) (by norm_num) he₀ he₁ hfar)
  have hprofile : balancedProfile l e l = profileLerp u
      (balancedProfile (1/4096) e (1/4096)) (balancedProfile (2/4096) e (2/4096)) := by
    funext j
    fin_cases j <;> simp [balancedProfile, splitProfile, profileLerp, u] <;> ring
  have hgamma : farMarginGamma μ a l =
      rowLerp u (farMarginGamma μ a (1/4096)) (farMarginGamma μ a (2/4096)) := by
    funext j
    fin_cases j <;> simp (config := {decide := true})
      [farMarginGamma, balancedGamma, rowLerp, u] <;> ring
  apply (weightedRow_farMargin_iff criticalQ μ a l e p s z).1
  rw [hprofile, hgamma]
  exact weightedRow_profileLerp hq hu₀ hu₁ hπ hleft hright

end HlawkaSchatten.BelowExponent
