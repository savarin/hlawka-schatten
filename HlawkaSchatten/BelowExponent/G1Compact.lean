/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Large
public import Mathlib.Analysis.Analytic.Binomial
import all HlawkaSchatten.BelowExponent.G1Large
import all HlawkaSchatten.BelowExponent.G1Far

/-! Scalar bounds for the compact bounded-z G1 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set Filter Topology

open private evenGap_neg_shift from HlawkaSchatten.BelowExponent.G1Large
open private criticalQ_lo criticalQ_hi from HlawkaSchatten.BelowExponent.G1Far

private noncomputable def g1Curvature : ℝ := criticalQ * (criticalQ - 1) / 2

private theorem choose_two (q : ℝ) : Ring.choose q 2 = q * (q - 1) / 2 := by
  rw [Ring.choose_eq_smul]
  simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub]
  ring

private theorem choose_nonneg_of_lt {x : ℝ} {k : ℕ} (h : (k : ℝ) - 1 < x) :
    0 ≤ Ring.choose x k := by
  rw [Ring.choose_eq_smul, smul_eq_mul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  exact mul_nonneg (by positivity) (ascPochhammer_pos _ _ (by linarith)).le

private theorem choose_even_nonneg {q : ℝ} (hq : 1 ≤ q) (hq₂ : q < 2) {n : ℕ}
    (hn : Even n) (hn₂ : 2 ≤ n) : 0 ≤ Ring.choose q n := by
  let k := n - 2
  have hk : Even k := (Nat.even_sub hn₂).2 (iff_of_true hn (by decide))
  have h := Ring.choose_smul_choose q hn₂
  change (n.choose 2) • Ring.choose q n = Ring.choose q 2 * Ring.choose (q - 2) k at h
  have hki : Even (k : ℤ) := by
    obtain ⟨j, hj⟩ := hk
    exact ⟨(j : ℤ), by exact_mod_cast hj⟩
  have hc : 0 ≤ Ring.choose (q - 2) k := by
    rw [show q - 2 = -(2 - q) by ring, Ring.choose_neg,
      show Int.negOnePow (k : ℤ) = 1 from Int.negOnePow_even _ hki, one_smul]
    exact choose_nonneg_of_lt (by linarith)
  rw [nsmul_eq_mul, choose_two] at h
  have hprod : 0 ≤ (n.choose 2 : ℝ) * Ring.choose q n := h ▸
    mul_nonneg (div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hq)) (by norm_num)) hc
  have hc' : (0 : ℝ) < (n.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hn₂
  exact nonneg_of_mul_nonneg_right hprod hc'

private noncomputable def evenCoefficient (q : ℝ) (n : ℕ) : ℝ :=
  if Even n then Ring.choose q n else 0

private theorem binomial_hasSum {q t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => Ring.choose q n * t^n) ((1+t)^q) := by
  have ht' : t ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, eDist_eq_eNorm_sub, ← ofReal_norm, Real.norm_eq_abs] using ht
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := q)).hasSum_sub ht'
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars, mul_comm] using h

private theorem evenGap_hasSum_tail {q t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => evenCoefficient q (n + 4) * t^(n+4))
      (balancedEvenGap q 1 t - (q*(q-1)/2)*t^2) := by
  let f (n : ℕ) := evenCoefficient q n * t^n
  have h₁ := binomial_hasSum (q := q) ht
  have h₂ := binomial_hasSum (q := q) (by simpa only [abs_neg] using ht : |-t| < 1)
  have h := (h₁.add h₂).mul_left (1/2 : ℝ)
  have hsum : HasSum f ((|1+t|^q + |1-t|^q)/2) := by
    rw [abs_of_pos (by linarith [(abs_lt.mp ht).1]), abs_of_pos (by linarith [(abs_lt.mp ht).2]),
      sub_eq_add_neg, div_eq_inv_mul, show (2:ℝ)⁻¹ = 1/2 by norm_num]
    refine h.congr_fun fun n => ?_
    rcases Nat.even_or_odd n with hn | hn
    · simp only [f, evenCoefficient, ite_eq_left hn, hn.neg_pow]
      ring
    · simp only [f, evenCoefficient, ite_eq_right (Nat.not_even_iff_odd.mpr hn), hn.neg_pow]
      ring
  have htail := (hasSum_nat_add_iff' 4).mpr hsum
  have hpre : ∑ n ∈ Finset.range 4, f n = 1 + (q*(q-1)/2)*t^2 := by
    simp [Finset.sum_range_succ, f, evenCoefficient, choose_two, (by decide : ¬Even (3 : ℕ))]
  rw [hpre] at htail
  convert! htail using 1
  unfold balancedEvenGap
  rw [abs_one, Real.one_rpow]
  ring

private theorem evenGap_tail_nonneg (n : ℕ) :
    0 ≤ evenCoefficient criticalQ (n+4) := by
  unfold evenCoefficient
  split
  · exact choose_even_nonneg (by linarith [criticalQ_lo]) (by linarith [criticalQ_hi])
      (by assumption) (by omega)
  · rfl

private theorem evenGap_remainder_continuous :
    Continuous (fun t => balancedEvenGap criticalQ 1 t - g1Curvature*t^2) := by
  have hq : 0 ≤ criticalQ := by linarith [criticalQ_lo]
  unfold balancedEvenGap
  fun_prop (disch := assumption)

private theorem evenGap_remainder_one :
    balancedEvenGap criticalQ 1 1 - g1Curvature*1^2 = 1/2 - g1Curvature := by
  have hq : criticalQ ≠ 0 := by linarith [criticalQ_lo]
  norm_num [balancedEvenGap, Real.zero_rpow hq, two_rpow_criticalQ]

private theorem g1_evenGap_abs_bounds {t : ℝ} (ht : |t| ≤ 1) :
    g1Curvature*t^2 ≤ balancedEvenGap criticalQ 1 t ∧
      balancedEvenGap criticalQ 1 t ≤ g1Curvature*t^2 + (1/2-g1Curvature)*t^4 := by
  wlog ht₀ : 0 ≤ t
  · have h := this (t := -t) (by simpa only [abs_neg] using ht) (by linarith)
    simpa only [evenGap_neg_shift, even_two.neg_pow, (by decide : Even (4:ℕ)).neg_pow] using h
  have ht₁ : t ≤ 1 := by simpa only [abs_of_nonneg ht₀] using ht
  by_cases h : t = 1
  · subst t
    have hc : g1Curvature ≤ 1/2 := by
      dsimp [g1Curvature]
      have hq : 1 ≤ criticalQ := by linarith [criticalQ_lo]
      have h := mul_le_mul criticalQ_hi (show criticalQ-1 ≤ 3/5 by linarith [criticalQ_hi])
        (sub_nonneg.mpr hq) (by norm_num)
      linarith
    constructor <;> linarith only [hc, evenGap_remainder_one, show (1 : ℝ)^4 = 1 by norm_num]
  have ht' : |t| < 1 := lt_of_le_of_ne ht (by rwa [abs_of_nonneg ht₀])
  let F (x : ℝ) := balancedEvenGap criticalQ 1 x - g1Curvature*x^2
  have hd (x : ℝ) (hx : |x| < 1) :
      HasSum (fun n : ℕ => evenCoefficient criticalQ (n+4) * x^(n+4)) (F x) :=
    evenGap_hasSum_tail hx
  have hlow : 0 ≤ F t :=
    hasSum_le (fun n => mul_nonneg (evenGap_tail_nonneg n) (pow_nonneg ht₀ _)) hasSum_zero (hd t ht')
  have hcmp (x : ℝ) (htx : t ≤ x) (hx : x < 1) : x^4 * F t ≤ t^4 * F x := by
    have hx₀ := ht₀.trans htx
    refine hasSum_le (fun n => ?_) ((hd t ht').mul_left _)
      ((hd x (by rwa [abs_of_nonneg hx₀])).mul_left _)
    have hpow := pow_le_pow_left₀ ht₀ htx n
    convert mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (evenGap_tail_nonneg n) (mul_nonneg (pow_nonneg ht₀ 4) (pow_nonneg hx₀ 4))) using 1 <;>
      rw [pow_add] <;> ring
  have hF : Continuous F := evenGap_remainder_continuous
  have hleft : Tendsto (fun x : ℝ => x^4 * F t) (𝓝[<] 1) (𝓝 ((1:ℝ)^4*F t)) :=
    (((continuous_id.pow 4).mul continuous_const).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun x : ℝ => t^4 * F x) (𝓝[<] 1) (𝓝 (t^4*F 1)) :=
    ((continuous_const.mul hF).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hup := le_of_tendsto_of_tendsto hleft hright <| by
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (lt_mem_nhds (lt_of_le_of_ne ht₁ h))] with x hx htx
    exact hcmp x htx.le hx
  change (1:ℝ)^4 * F t ≤ t^4 * F 1 at hup
  simp only [one_pow, one_mul, show F 1 = 1/2-g1Curvature from evenGap_remainder_one] at hup
  constructor <;> dsimp [F] at hlow hup ⊢ <;> linarith only [hlow, hup]

private theorem compact_jensen_lower {l z : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1)
    (hz : |z| ≤ 8) :
    g1Curvature * (8 : ℝ)^(criticalQ-2) * l*(1-l)*(z-1)^2 ≤
      balancedJensenGap criticalQ l 1 z := by
  let q := criticalQ
  let c := g1Curvature * (8:ℝ)^(q-2)
  let f (x : ℝ) := x^q-c*x^2
  let df (x : ℝ) := q*x^(q-1)-2*c*x
  let ddf (x : ℝ) := q*(q-1)*x^(q-2)-2*c
  have hq : 1 ≤ q := by dsimp [q]; linarith [criticalQ_lo]
  have hq₂ : q ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hf : Continuous f := (Real.continuous_rpow_const (by linarith)).sub
    (continuous_const.mul (continuous_id.pow 2))
  have hd (x : ℝ) (hx : x ∈ interior (Icc (0:ℝ) 8)) : HasDerivAt f (df x) x := by
    rw [interior_Icc] at hx
    have h := (Real.hasDerivAt_rpow_const (x := x) (p := q) (Or.inl hx.1.ne')).sub
      (((hasDerivAt_id x).pow 2).const_mul c)
    convert! h using 1
    simp [df]
    ring
  have hd₂ (x : ℝ) (hx : x ∈ interior (Icc (0:ℝ) 8)) : HasDerivAt df (ddf x) x := by
    rw [interior_Icc] at hx
    have h := ((Real.hasDerivAt_rpow_const (x := x) (p := q-1) (Or.inl hx.1.ne')).const_mul q).sub
      ((hasDerivAt_id x).const_mul (2*c))
    convert! h using 1
    simp [ddf, show q-1-1 = q-2 by ring]
    ring
  have hpow (x : ℝ) (hx : x ∈ interior (Icc (0:ℝ) 8)) :
      (8 : ℝ)^(q-2) ≤ x^(q-2) := by
    rw [interior_Icc] at hx
    exact Real.rpow_le_rpow_of_nonpos hx.1 hx.2.le (sub_nonpos.mpr hq₂)
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 8) f := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f := f) (f' := df) (f'' := ddf)
      (convex_Icc _ _) hf.continuousOn (fun x hx => (hd x hx).hasDerivWithinAt)
      (fun x hx => (hd₂ x hx).hasDerivWithinAt) ?_
    intro x hx
    have hmul := mul_le_mul_of_nonneg_left (hpow x hx) (mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hq))
    change q*(q-1)*(8 : ℝ)^(q-2) ≤ q*(q-1)*x^(q-2) at hmul
    change 0 ≤ q*(q-1)*x^(q-2) - 2*c
    have hc : 2*c = q*(q-1)*(8 : ℝ)^(q-2) := by dsimp [c, g1Curvature, q]; ring
    rw [hc]
    exact sub_nonneg.mpr hmul
  have hmono : MonotoneOn f (Icc (0:ℝ) 8) := by
    refine monotoneOn_of_deriv_nonneg (f := f) (convex_Icc _ _) hf.continuousOn
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hd x hx).deriv]
    have hpx := hpow x hx
    rw [interior_Icc] at hx
    have hx₀ : 0 < x := hx.1
    have hbc : (q-1) * (8 : ℝ)^(q-2) ≤ x^(q-2) := calc
      _ ≤ 1*(8 : ℝ)^(q-2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hpx
    have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbc (by linarith : 0 ≤ q)) hx₀.le
    change 0 ≤ q*x^(q-1)-2*c*x
    rw [show q-1=(q-2)+1 by ring, Real.rpow_add_one hx₀.ne']
    dsimp [c, g1Curvature, q] at hs ⊢
    nlinarith only [hs]
  have hM := mul_nonneg (sub_nonneg.mpr hl₁) (abs_nonneg z)
  have hAbs : |(1-l)*z+l*1| ≤ (1-l)*|z|+l := by
    simpa only [mul_one, abs_mul, abs_of_nonneg (sub_nonneg.mpr hl₁), abs_of_nonneg hl₀] using
      abs_add_le ((1-l)*z) l
  have hAvg : (1-l)*|z|+l ∈ Icc (0:ℝ) 8 :=
    ⟨add_nonneg hM hl₀, by nlinarith only [hl₀, mul_nonneg (sub_nonneg.mpr hl₁) (sub_nonneg.mpr hz)]⟩
  have h := hmono ⟨abs_nonneg _, hAbs.trans hAvg.2⟩ hAvg hAbs
  have hj := hconv.2 (show |z| ∈ Icc (0:ℝ) 8 from ⟨abs_nonneg z, hz⟩)
    (show (1 : ℝ) ∈ Icc (0:ℝ) 8 by norm_num)
    (sub_nonneg.mpr hl₁) hl₀ (by ring : 1-l+l=1)
  simp only [smul_eq_mul, mul_one] at hj
  have hg := h.trans hj
  simp only [mul_one, f, sq_abs, Real.one_rpow, one_pow] at hg
  change c*l*(1-l)*(z-1)^2 ≤ balancedJensenGap q l 1 z
  unfold balancedJensenGap balancedFarCenter
  simp only [mul_one, abs_one, Real.one_rpow]
  linarith only [hg, show (1-l)*(c*z^2) + l*c - c*((1-l)*z+l)^2 =
    c*l*(1-l)*(z-1)^2 by ring]

private theorem variance_tangent {w X : ℝ} (hw : 0 < w) (hX : 0 ≤ X) :
    X^(criticalQ/2) ≤ (1-criticalQ/2)*w^criticalQ +
      (criticalQ/2)*(w^criticalQ/w^2)*X := by
  let h := criticalQ/2
  have hh₀ : 0 ≤ h := by dsimp [h]; linarith [criticalQ_lo]
  have hh₁ : h ≤ 1 := by dsimp [h]; linarith [criticalQ_hi]
  have hs : 0 < w^2 := sq_pos_of_pos hw
  have hbase : 0 ≤ X/(w^2) := div_nonneg hX hs.le
  have ht := rpow_one_add_le_one_add_mul_self (s := X/w^2-1) (by linarith : -1 ≤ X/w^2-1) hh₀ hh₁
  rw [show 1+(X/w^2-1)=X/w^2 by ring] at ht
  have ht' := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hs.le h)
  rw [← Real.mul_rpow hs.le hbase, show w^2*(X/w^2)=X by field_simp [hw.ne']] at ht'
  have hwq : (w^2)^h = w^criticalQ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    congr 1
    dsimp [h]
    ring
  rw [hwq] at ht'
  change X^h ≤ (1-h)*w^criticalQ + h*(w^criticalQ/w^2)*X
  linarith only [ht', show w^criticalQ*(1+h*(X/w^2-1)) =
    (1-h)*w^criticalQ+h*(w^criticalQ/w^2)*X by ring]

private theorem g1Curvature_nonneg : 0 ≤ g1Curvature := by
  unfold g1Curvature
  positivity [show 0 ≤ criticalQ by linarith [criticalQ_lo],
    show 0 ≤ criticalQ - 1 by linarith [criticalQ_lo]]

private theorem g1Curvature_le_half : g1Curvature ≤ 1/2 := by
  have h := mul_le_mul criticalQ_hi (show criticalQ - 1 ≤ 3/5 by linarith [criticalQ_hi])
    (show 0 ≤ criticalQ - 1 by linarith [criticalQ_lo]) (by norm_num)
  unfold g1Curvature
  linarith

private theorem compact_compensated_lower {μ l e E V T C k s z : ℝ}
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1)
    (he₀ : 0 ≤ e) (heE : e ≤ E) (he₁ : e ≤ 1/2) (hV : 1-e^2 ≤ V)
    (hR : E+9*l ≤ 1) (hs : |s| ≤ 1) (hz : |z| ≤ 8)
    (hT : g1Curvature + (1/2-g1Curvature)*(E+9*l)^2 ≤ T)
    (ha : 0 < (1-μ*(1-l))*g1Curvature - (1-μ)*T*E^2 - C)
    (hk : (1-μ)*T + ((1-μ)*T*E)^2 /
      ((1-μ*(1-l))*g1Curvature - (1-μ)*T*E^2 - C) ≤ k) :
    μ*((1-l)*|z|^criticalQ+l) - k*l^2*(z-1)^2 + C*s^2 -
        μ*((balancedFarCenter l l 1 z)^2+V*s^2)^(criticalQ/2)
      ≤ balancedFacetGap criticalQ μ l e 1 s z := by
  let q := criticalQ
  let U := e*s+l*(z-1)
  let c := 1-μ*(1-l)
  let b := 1-μ
  let B := b*T
  let a := c*g1Curvature - B*E^2 - C
  let Z := balancedFarCenter l l 1 z
  have hq₀ : 0 ≤ q := by dsimp [q]; linarith [criticalQ_lo]
  have hq₂ : q ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hE₀ := he₀.trans heE
  have hR₀ : 0 ≤ E+9*l := by positivity
  have he : |e| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  have hc : 0 ≤ c := by
    have h := mul_le_mul_of_nonneg_right hμ₁ (sub_nonneg.mpr hl₁)
    dsimp [c]
    linarith
  have hB : 0 ≤ B := by
    have hT₀ : 0 ≤ T := (add_nonneg g1Curvature_nonneg
      (mul_nonneg (sub_nonneg.mpr g1Curvature_le_half) (sq_nonneg _))).trans hT
    exact mul_nonneg (sub_nonneg.mpr hμ₁) hT₀
  have hz₁ : |z-1| ≤ 9 := by
    have h := abs_add_le z (-1)
    rw [← sub_eq_add_neg, abs_neg, abs_one] at h
    linarith
  have hUabs : |U| ≤ E*|s|+l*|z-1| := by
    have h := abs_add_le (e*s) (l*(z-1))
    simp only [abs_mul, abs_of_nonneg he₀, abs_of_nonneg hl₀] at h
    exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_right heE (abs_nonneg s)) _)
  have hU : |U| ≤ E+9*l := hUabs.trans (by
    linarith only [mul_le_mul_of_nonneg_left hs hE₀, mul_le_mul_of_nonneg_left hz₁ hl₀])
  have hU₂ : U^2 ≤ (E+9*l)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg U) hU 2
  have hNear : balancedEvenGap q 1 U ≤ T*U^2 := by
    have h := (g1_evenGap_abs_bounds (hU.trans hR)).2
    have ht := mul_le_mul_of_nonneg_right hT (sq_nonneg U)
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hU₂ (sub_nonneg.mpr g1Curvature_le_half)) (sq_nonneg U)
    linarith only [h, ht, hcoef, show U^4 = U^2*U^2 by ring]
  have hUcost : B*U^2 ≤ B*(E^2*s^2+2*E*l*|s| * |z-1|+l^2*(z-1)^2) := by
    have h := pow_le_pow_left₀ (abs_nonneg U) hUabs 2
    simp only [sq_abs] at h
    refine mul_le_mul_of_nonneg_left (h.trans_eq ?_) hB
    rw [add_sq, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have hYoung : 2*B*E*l*|s| * |z-1| ≤ a*s^2+(B*E)^2/a*l^2*(z-1)^2 := by
    have ha' : 0 < a := ha
    apply (mul_le_mul_iff_right₀ ha').1
    have h := sq_nonneg (a*|s|-B*E*l*|z-1|)
    rw [show a*(a*s^2+(B*E)^2/a*l^2*(z-1)^2) =
      a^2*s^2+(B*E)^2*l^2*(z-1)^2 by field_simp [ha'.ne']]
    simp only [sub_sq, mul_pow, sq_abs] at h
    nlinarith only [h]
  have hNearTotal := mul_le_mul_of_nonneg_left hNear (sub_nonneg.mpr hμ₁)
  have hNearBound : b*balancedEvenGap q 1 U ≤ B*E^2*s^2+a*s^2+k*l^2*(z-1)^2 := by
    have hK : B+(B*E)^2/a ≤ k := hk
    have hK' := mul_le_mul_of_nonneg_right hK (mul_nonneg (sq_nonneg l) (sq_nonneg (z-1)))
    change b*balancedEvenGap q 1 U ≤ _
    change b*balancedEvenGap q 1 U ≤ b*(T*U^2) at hNearTotal
    have hEQ : b*(T*U^2) = B*U^2 := by dsimp [B]; ring
    rw [hEQ] at hNearTotal
    linarith only [hNearTotal, hUcost, hYoung, hK']
  have hInput := mul_le_mul_of_nonneg_left (g1_evenGap_abs_bounds hs).1 hc
  have hFar : balancedFarIncrement q e Z s ≤ (Z^2+V*s^2)^(q/2)-|Z|^q := by
    have h := balancedFarIncrement_le_variance hq₀ hq₂ he Z s
    have hV₀ := mul_le_mul_of_nonneg_right hV (sq_nonneg s)
    have hbase : 0 ≤ Z^2+(1-e^2)*s^2 := by
      have hE : 0 ≤ 1-e^2 := by
        have hsq := pow_le_pow_left₀ he₀ (he₁.trans (by norm_num : (1/2:ℝ) ≤ 1)) 2
        linarith
      positivity
    exact h.trans (sub_le_sub_right (Real.rpow_le_rpow hbase (by linarith) (by positivity)) _)
  have hFar' := mul_le_mul_of_nonneg_left hFar hμ₀
  unfold balancedFacetGap balancedJensenGap
  rw [balancedNearShift_facet, abs_one, Real.one_rpow, mul_one]
  change μ*((1-l)*|z|^q+l) - k*l^2*(z-1)^2 + C*s^2 - μ*(Z^2+V*s^2)^(q/2) ≤
    μ*((1-l)*|z|^q+l-|Z|^q) + c*balancedEvenGap q 1 s - b*balancedEvenGap q 1 U -
      μ*balancedFarIncrement q e Z s
  linarith only [hInput, hNearBound, hFar',
    show a*s^2 = c*g1Curvature*s^2-B*E^2*s^2-C*s^2 by dsimp [a]; ring]

private theorem eight_critical_pred : (8 : ℝ)^(criticalQ-2) = 27/64 := by
  have h₈ : (8 : ℝ)^criticalQ = 27 := by
    rw [show (8 : ℝ) = (2:ℝ)^(3:ℝ) by rw [Real.rpow_ofNat]; norm_num,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)), mul_comm (3:ℝ),
      Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)), two_rpow_criticalQ, Real.rpow_ofNat]
    norm_num
  rw [Real.rpow_sub (by norm_num : 0 < (8:ℝ)), h₈, Real.rpow_two]
  norm_num

private theorem compact_gap_of_certificates {μ l e V C k w α β s z : ℝ}
    (hμ : 0 < μ) (hl : 0 ≤ l) (hl₁ : l ≤ 1) (hV : 0 ≤ V) (hw : 0 < w)
    (hz : |z| ≤ 8) (hα : (criticalQ/2)*(w^criticalQ/w^2) ≤ α)
    (hβ : (1-criticalQ/2)*w^criticalQ ≤ β) (hC : μ*α*V ≤ C)
    (hflank : k*l/μ ≤ g1Curvature*(1-l)*(27/64))
    (hclose : |balancedFarCenter l l 1 z| ≤ w →
      k*l^2/μ*(z-1)^2+β+α*(balancedFarCenter l l 1 z)^2 ≤ l+(1-l)*|z|^criticalQ)
    (hlower : μ*((1-l)*|z|^criticalQ+l) - k*l^2*(z-1)^2 + C*s^2 -
      μ*((balancedFarCenter l l 1 z)^2+V*s^2)^(criticalQ/2) ≤
        balancedFacetGap criticalQ μ l e 1 s z) :
    0 ≤ balancedFacetGap criticalQ μ l e 1 s z := by
  let q := criticalQ
  let Z := balancedFarCenter l l 1 z
  have hbase : 0 ≤ Z^2+V*s^2 := by positivity
  have hq : 0 ≤ q/2 := by dsimp [q]; linarith [criticalQ_lo]
  have hq₂ : q ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hCs := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  refine le_trans ?_ hlower
  by_cases hZ : |Z| ≤ w
  · have h := variance_tangent hw hbase
    have hU := (h.trans (add_le_add hβ (mul_le_mul_of_nonneg_right hα hbase)))
    have hμU := mul_le_mul_of_nonneg_left hU hμ.le
    have hN := mul_le_mul_of_nonneg_left (hclose hZ) hμ.le
    have hEq : μ*(k*l^2/μ*(z-1)^2) = k*l^2*(z-1)^2 := by field_simp [hμ.ne']
    linarith only [hμU, hN, hCs, hEq]
  · have hZW : w ≤ |Z| := le_of_not_ge hZ
    have hZp := hw.trans_le hZW
    have hT := variance_tangent hZp hbase
    rw [sq_abs] at hT
    have hRatio : |Z|^q/Z^2 ≤ w^q/w^2 := by
      rw [← sq_abs Z, ← Real.rpow_two, ← Real.rpow_sub hZp, ← Real.rpow_two w,
        ← Real.rpow_sub hw]
      exact Real.rpow_le_rpow_of_nonpos hw hZW (sub_nonpos.mpr hq₂)
    have hZA := (mul_le_mul_of_nonneg_left hRatio hq).trans hα
    have hEq : (1-q/2)*|Z|^q + (q/2)*(|Z|^q/Z^2)*(Z^2+V*s^2) =
        |Z|^q + (q/2)*(|Z|^q/Z^2)*(V*s^2) := by
      have hz₀ : Z ≠ 0 := abs_pos.mp hZp
      field_simp [hz₀]
      simp [q]
      ring
    change (Z^2+V*s^2)^(q/2) ≤ _ at hT
    rw [hEq] at hT
    have hHZ := mul_le_mul_of_nonneg_left
      (hT.trans (add_le_add_right (mul_le_mul_of_nonneg_right hZA
        (mul_nonneg hV (sq_nonneg s))) _)) hμ.le
    have hJ := compact_jensen_lower hl hl₁ hz
    rw [eight_critical_pred, balancedJensenGap] at hJ
    simp only [abs_one, Real.one_rpow, mul_one] at hJ
    have hK := mul_le_mul_of_nonneg_left hflank
      (mul_nonneg (mul_nonneg hμ.le hl) (sq_nonneg (z-1)))
    have hK' : k*l^2*(z-1)^2 ≤ μ*(g1Curvature*(27/64)*l*(1-l)*(z-1)^2) := by
      have hEq : μ*l*(z-1)^2*(k*l/μ) = k*l^2*(z-1)^2 := by
        field_simp [hμ.ne']
      rw [hEq] at hK
      linarith only [hK]
    have hJ' := mul_le_mul_of_nonneg_left hJ hμ.le
    linarith only [hHZ, hCs, hK', hJ']

end HlawkaSchatten.BelowExponent
