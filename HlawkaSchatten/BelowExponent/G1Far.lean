/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1
public import HlawkaSchatten.BelowExponent.Bulk
public import Batteries.Tactic.OpenPrivate
import all HlawkaSchatten.BelowExponent.G1

/-! Far-row estimates for the thirteen slabs of the balanced-edge certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

-- Reuse the audited first-slab lemmas without changing its source.
open private evenGap_convex evenGap_nonneg evenGap_lower_power evenGap_lower_quarter_sq
  evenGap_upper_power half_pow_q half_pow_pred rpow_critical_split balancedFacetGap_scale
  weightedRow_farMargin_iff farMarginGamma from HlawkaSchatten.BelowExponent.G1

/-- The fourteen edge-mass breakpoints in units of `1 / 4096`. -/
def g1LengthNumerator : Fin 14 → ℕ := ![1, 2, 4, 8, 16, 24, 32, 40, 48, 56, 60, 64, 68, 74]

/-- The fixed weight for each of the thirteen slabs in units of `1 / 1000`. -/
def g1WeightNumerator : Fin 13 → ℕ := ![47, 62, 83, 108, 136, 149, 163, 174, 183, 191, 197, 200, 204]

noncomputable def g1SlabLeft (i : Fin 13) : ℝ := (g1LengthNumerator i.castSucc : ℝ) / 4096
noncomputable def g1SlabRight (i : Fin 13) : ℝ := (g1LengthNumerator i.succ : ℝ) / 4096
noncomputable def g1SlabWeight (i : Fin 13) : ℝ := (g1WeightNumerator i : ℝ) / 1000

private theorem criticalQ_lo : (1054:ℝ)/665 ≤ criticalQ := criticalQ_bracket.1.le

private theorem criticalQ_hi : criticalQ ≤ 8/5 :=
  criticalQ_bracket.2.le.trans (by norm_num)

private theorem criticalQ_one : 1 ≤ criticalQ := (by norm_num : (1:ℝ) ≤ 1054/665).trans criticalQ_lo

private theorem table_ranges : ∀ i : Fin 13,
    0 < g1LengthNumerator i.castSucc ∧
      g1LengthNumerator i.castSucc < g1LengthNumerator i.succ ∧
      g1LengthNumerator i.succ ≤ 74 ∧
      0 < g1WeightNumerator i ∧ g1WeightNumerator i ≤ 204 := by decide

private theorem slab_ranges (i : Fin 13) :
    0 < g1SlabLeft i ∧ g1SlabLeft i < g1SlabRight i ∧ g1SlabRight i ≤ 74/4096 ∧
      0 < g1SlabWeight i ∧ g1SlabWeight i ≤ 204/1000 := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := table_ranges i
  unfold g1SlabLeft g1SlabRight g1SlabWeight
  exact ⟨div_pos (by exact_mod_cast h₀) (by norm_num),
    div_lt_div_of_pos_right (by exact_mod_cast h₁) (by norm_num),
    div_le_div_of_nonneg_right (by exact_mod_cast h₂) (by norm_num),
    div_pos (by exact_mod_cast h₃) (by norm_num),
    div_le_div_of_nonneg_right (by exact_mod_cast h₄) (by norm_num)⟩

private theorem table_drift_check : ∀ i : Fin 13,
    g1LengthNumerator i.succ ^ 389 * (75 * (1000 - g1WeightNumerator i)) ^ 665 ≤
      (28 * g1WeightNumerator i) ^ 665 * 4096 ^ 389 := by
  decide +kernel

private theorem drift_constant_simplify {μ : ℝ} (hμ : μ ≠ 0) (hb : 1-μ ≠ 0) :
    (3/2)*(1-μ)/μ * (28*μ/(75*(1-μ))) = 14/25 := by
  field_simp [hμ, hb]
  norm_num

private theorem slab_drift_upper (i : Fin 13) {l : ℝ} (hl : 0 < l) (hlU : l ≤ g1SlabRight i) :
    (3/2) * (1-g1SlabWeight i) / g1SlabWeight i * l^(criticalQ-1) ≤ 14/25 := by
  let μ := g1SlabWeight i
  obtain ⟨hL₀, hL₁, hL₂, hμ, hμU⟩ := slab_ranges i
  have hμ₁ : 0 < 1-μ := by dsimp [μ]; linarith
  have hden : 0 < 75 * (1000 - g1WeightNumerator i) := by
    have := (table_ranges i).2.2.2.2
    omega
  have h := (natRat_rpow_le_iff (a := g1LengthNumerator i.succ)
    (c := 28 * g1WeightNumerator i) (m := 389) (n := 665)
    (by decide : 0 < (4096:ℕ)) hden (by decide : 0 < (665:ℕ))).2 (table_drift_check i)
  have hcast : (g1SlabRight i) ^ (389/665:ℝ) ≤ 28*μ/(75*(1-μ)) := by
    have hw : g1WeightNumerator i ≤ 1000 := by have := (table_ranges i).2.2.2.2; omega
    push_cast [Nat.cast_sub hw] at h
    have heq : 28 * (g1WeightNumerator i : ℝ) / (75 * (1000 - (g1WeightNumerator i : ℝ))) =
        28*μ/(75*(1-μ)) := by
      dsimp [μ, g1SlabWeight]
      have hp : (g1WeightNumerator i : ℝ) < 1000 := by
        have := (table_ranges i).2.2.2.2
        exact_mod_cast (show g1WeightNumerator i < 1000 by omega)
      field_simp
    simpa only [heq, g1SlabRight] using h
  have hL₃ : g1SlabRight i ≤ 1 := hL₂.trans (by norm_num)
  have hpow : l^(criticalQ-1) ≤ 28*μ/(75*(1-μ)) :=
    (Real.rpow_le_rpow hl.le hlU (sub_nonneg.mpr criticalQ_one)).trans
      ((Real.rpow_le_rpow_of_exponent_ge (hL₀.trans hL₁) hL₃
        (by linarith [criticalQ_lo] : (389:ℝ)/665 ≤ criticalQ-1)).trans hcast)
  change (3/2)*(1-μ)/μ * l^(criticalQ-1) ≤ 14/25
  calc
    _ ≤ (3/2)*(1-μ)/μ * (28*μ/(75*(1-μ))) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := drift_constant_simplify (show μ ≠ 0 from hμ.ne') hμ₁.ne'

private theorem rpow_crit_upper_two : criticalQ ≤ 2 := criticalQ_hi.trans (by norm_num)

private theorem evenGap_scale {q a : ℝ} (ha : 0 ≤ a) (p s : ℝ) :
    balancedEvenGap q (a*p) (a*s) = a^q * balancedEvenGap q p s := by
  unfold balancedEvenGap
  rw [show a*p + a*s = a*(p+s) by ring, show a*p-a*s=a*(p-s) by ring]
  simp only [abs_mul, abs_of_nonneg ha, Real.mul_rpow ha (abs_nonneg _)]
  ring

private theorem evenGap_lower_three_eighth_sq {p s : ℝ}
    (hps : |p+s| ≤ 3/8) (hms : |p-s| ≤ 3/8) :
    (3/8) * s^2 ≤ balancedEvenGap criticalQ p s := by
  let a : ℝ := 8/3
  have ha : 0 < a := by norm_num [a]
  have hplus : |a*p+a*s| ≤ 1 := by
    rw [show a*p+a*s=a*(p+s) by ring, abs_mul, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hps ha.le).trans (by norm_num [a])
  have hminus : |a*p-a*s| ≤ 1 := by
    rw [show a*p-a*s=a*(p-s) by ring, abs_mul, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hms ha.le).trans (by norm_num [a])
  have h := evenGap_lower_quarter_sq (q := criticalQ)
    (by linarith [criticalQ_lo]) rpow_crit_upper_two hplus hminus
  rw [evenGap_scale ha.le] at h
  have hcross : (3/2:ℝ) ≤ (8/3:ℝ) ^ (12/29:ℝ) := by
    norm_num at *
    exact (le_natRat_rpow_iff (a := 8) (c := 3) (m := 12) (n := 29)
      (by decide : 0 < (3:ℕ)) (by decide : 0 < (2:ℕ)) (by decide)).2 (by decide +kernel)
  have hExp : (12:ℝ)/29 ≤ 2-criticalQ := by
    linarith [criticalQ_bracket.2]
  have hP : (3/2:ℝ) ≤ a ^ (2-criticalQ) :=
    hcross.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num [a]) hExp)
  rw [Real.rpow_sub ha, Real.rpow_two] at hP
  have hA := (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).1 hP
  have hmul := mul_le_mul_of_nonneg_right hA (show 0 ≤ s^2/4 by positivity)
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos ha criticalQ)).mp
  calc
    _ = ((3/2)*a^criticalQ)*(s^2/4) := by ring
    _ ≤ a^2*(s^2/4) := hmul
    _ = (a*s)^2/4 := by ring
    _ ≤ _ := h

private theorem far_center_lower {l p : ℝ} (hl : 0 ≤ l) (hlU : l ≤ 74/4096)
    (hp : |p| ≤ 1/8) : (16051:ℝ)/16384 ≤ balancedFarCenter l l p 1 := by
  have h := (mul_le_mul_of_nonneg_left (show 1-p ≤ 9/8 by
    linarith [(abs_le.mp hp).1]) hl).trans
    (mul_le_mul_of_nonneg_right hlU (by norm_num : (0:ℝ) ≤ 9/8))
  unfold balancedFarCenter
  nlinarith only [h]

private theorem far_absorption {l e p s : ℝ} (hl : 0 ≤ l) (hlU : l ≤ 74/4096)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hp : |p| ≤ 1/8) :
    balancedFarIncrement criticalQ e (balancedFarCenter l l p 1) s ≤
      (20/9) * (1-e^2) * balancedEvenGap criticalQ p s := by
  let q := criticalQ
  let Z := balancedFarCenter l l p 1
  have hq₁ : 1 ≤ q := criticalQ_one
  have hq₀ : 0 ≤ q := zero_le_one.trans hq₁
  have hq₂ : q ≤ 2 := rpow_crit_upper_two
  have he : |e| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  have hvarL : 3/4 ≤ 1-e^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr he₁) (show 0 ≤ 1/2+e by linarith)]
  have hvar₀ : 0 ≤ 1-e^2 := (by norm_num : (0:ℝ) ≤ 3/4).trans hvarL
  have hvarU : 1-e^2 ≤ 1 := by nlinarith only [sq_nonneg e]
  have hmul : 0 ≤ (20/9) * (1-e^2) := mul_nonneg (by norm_num) hvar₀
  change balancedFarIncrement q e Z s ≤ (20/9) * (1-e^2) * balancedEvenGap q p s
  by_cases hs : 1/4 ≤ |s|
  · have hpPow := Real.rpow_le_rpow (abs_nonneg p) (show |p| ≤ (1/2)*|s| by linarith) hq₀
    change |p|^criticalQ ≤ ((1/2)*|s|)^criticalQ at hpPow
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) (abs_nonneg s), half_pow_q] at hpPow
    have hA := evenGap_lower_power hq₁ p s
    have hs₀ : 0 ≤ |s|^q := Real.rpow_nonneg (abs_nonneg s) _
    have hA₀ := evenGap_nonneg hq₁ p s
    have hF := (balancedFarIncrement_le_power hq₀ hq₂ he Z s).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_one hvar₀ hvarU (by linarith : 0 ≤ q/2)) hs₀)
    simp only [one_mul] at hF
    have hF' : balancedFarIncrement q e Z s ≤ (3/2) * balancedEvenGap q p s := by
      change |p|^q ≤ (1/3)*|s|^q at hpPow
      linarith only [hF, hA, hpPow]
    exact hF'.trans (mul_le_mul_of_nonneg_right (by linarith) hA₀)
  · have hs' : |s| ≤ 1/4 := le_of_not_ge hs
    have hps : |p+s| ≤ 3/8 := (abs_add_le p s).trans (by linarith)
    have hms : |p-s| ≤ 3/8 := by
      rw [sub_eq_add_neg]
      exact (abs_add_le p (-s)).trans (by rw [abs_neg]; linarith)
    have hA := evenGap_lower_three_eighth_sq hps hms
    have hZ : 24/25 ≤ Z := (by norm_num : (24:ℝ)/25 ≤ 16051/16384).trans
      (far_center_lower hl hlU hp)
    have hZ₀ : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
    have hPow : |Z| ^ (q-2) ≤ 25/24 := calc
      _ ≤ (24/25:ℝ)^(q-2) := Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by rwa [abs_of_pos hZ₀]) (sub_nonpos.mpr hq₂)
      _ ≤ (24/25:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_ge
        (by norm_num) (by norm_num) (by linarith)
      _ = _ := by rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have hcoef : q/2 * |Z|^(q-2) ≤ 5/6 := by
      have hqU : q/2 ≤ 4/5 := by linarith [criticalQ_hi]
      have h := mul_le_mul hqU hPow (Real.rpow_nonneg (abs_nonneg Z) _) (by norm_num : (0:ℝ) ≤ 4/5)
      norm_num at h ⊢
      exact h
    calc
      _ ≤ q/2 * (1-e^2) * |Z|^(q-2) * s^2 :=
        balancedFarIncrement_le_quadratic hq₀ hq₂ he hZ₀.ne' s
      _ = (q/2*|Z|^(q-2)) * ((1-e^2)*s^2) := by ring
      _ ≤ (5/6)*((1-e^2)*s^2) := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hvar₀ (sq_nonneg s))
      _ = ((20/9)*(1-e^2))*((3/8)*s^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hA hmul

private theorem far_jensen_linear {l p : ℝ} (hl : 0 < l) (hlU : l ≤ 74/4096)
    (hp : |p| ≤ 1/8) :
    |p|^criticalQ - 1 + (313/200)*(1-p) ≤ balancedJensenGap criticalQ l p 1 / l := by
  let Z := balancedFarCenter l l p 1
  have hZL : 16051/16384 ≤ Z := far_center_lower hl.le hlU hp
  have hZ₀ : 0 < Z := lt_of_lt_of_le (by norm_num) hZL
  have hw : 0 < 1-p := by linarith [(abs_le.mp hp).2]
  have hdiff : 1-Z = l*(1-p) := by dsimp [Z, balancedFarCenter]; ring
  have hZ₁ : Z < 1 := sub_pos.mp (hdiff ▸ mul_pos hl hw)
  have hcross : (79/80:ℝ) ≤ (16051/16384:ℝ) ^ (3/5:ℝ) :=
    (le_natRat_rpow_iff (a := 16051) (c := 79) (m := 3) (n := 5)
      (by decide : 0 < (16384:ℕ)) (by decide : 0 < (80:ℕ)) (by decide)).2 (by decide)
  have hZpow : (79/80:ℝ) ≤ Z^(criticalQ-1) := hcross.trans
    ((Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show criticalQ-1 ≤ 3/5 by linarith [criticalQ_hi])).trans
      (Real.rpow_le_rpow (by norm_num) hZL (by linarith [criticalQ_one])))
  have hslope : (313/200:ℝ) ≤ criticalQ * Z^(criticalQ-1) := calc
    _ ≤ (1054/665:ℝ)*(79/80) := by norm_num
    _ ≤ _ := mul_le_mul criticalQ_lo hZpow (by norm_num) (by linarith [criticalQ_one])
  have hT := (convexOn_rpow criticalQ_one).le_slope_of_hasDerivAt (mem_Ici.mpr hZ₀.le)
    (mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 1)) hZ₁
    (Real.hasDerivAt_rpow_const (p := criticalQ) (Or.inl hZ₀.ne'))
  simp only [slope_def_field, Real.one_rpow] at hT
  have h := mul_le_mul_of_nonneg_right (hslope.trans hT) (sub_nonneg.mpr hZ₁.le)
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hZ₁.ne'), hdiff] at h
  apply (le_div_iff₀ hl).2
  unfold balancedJensenGap
  change (|p|^criticalQ - 1 + (313/200)*(1-p))*l ≤
    (1-l)*|(1:ℝ)|^criticalQ + l*|p|^criticalQ - |Z|^criticalQ
  rw [abs_one, Real.one_rpow, abs_of_pos hZ₀]
  nlinarith only [h]

private theorem evenGap_quadratic {p : ℝ} (hp : p ≠ 0) (s : ℝ) :
    balancedEvenGap criticalQ p s ≤ (criticalQ/2)*|p|^(criticalQ-2)*s^2 := by
  have h := balancedFarIncrement_le_quadratic (zero_le_one.trans criticalQ_one)
    rpow_crit_upper_two (e := 0) (by norm_num) hp s
  simp only [balancedFarIncrement, zero_pow two_ne_zero, sub_zero, add_zero, one_mul, mul_one] at h
  unfold balancedEvenGap
  linarith

private theorem critical_quadratic_le_power {x u : ℝ} (hu : |u| ≤ x) :
    x^(criticalQ-2)*u^2 ≤ |u|^criticalQ := by
  by_cases huz : u = 0
  · subst u
    simp only [zero_pow two_ne_zero, mul_zero]
    exact Real.rpow_nonneg (abs_nonneg (0:ℝ)) _
  have habs : 0 < |u| := abs_pos.mpr huz
  calc
    _ ≤ |u|^(criticalQ-2)*u^2 := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos habs hu (sub_nonpos.mpr rpow_crit_upper_two)) (sq_nonneg u)
    _ = _ := by
      rw [Real.rpow_sub habs, Real.rpow_two, sq_abs, div_mul_cancel₀ _ (pow_ne_zero _ huz)]

private theorem evenGap_interchange (p v : ℝ) :
    balancedEvenGap criticalQ p v =
      balancedEvenGap criticalQ v p + |v|^criticalQ - |p|^criticalQ := by
  unfold balancedEvenGap
  rw [add_comm v p, abs_sub_comm v p]
  ring

private theorem evenGap_drift_small {p v : ℝ} (hv : 0 < v) (hpv : |p| ≤ v) :
    balancedEvenGap criticalQ p v ≤ v^criticalQ - (1-criticalQ/2)*|p|^criticalQ := by
  have h : balancedEvenGap criticalQ v p ≤ (criticalQ/2)*|p|^criticalQ := calc
    _ ≤ (criticalQ/2)*|v|^(criticalQ-2)*p^2 := evenGap_quadratic hv.ne' p
    _ = (criticalQ/2)*(v^(criticalQ-2)*p^2) := by rw [abs_of_pos hv, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (critical_quadratic_le_power hpv) (by linarith [criticalQ_one])
  rw [evenGap_interchange, abs_of_pos hv]
  nlinarith only [h]

private theorem evenGap_drift_large {p v : ℝ} (hv : 0 < v) (hpv : v ≤ |p|) :
    balancedEvenGap criticalQ p v ≤ (4/5)*v^criticalQ := by
  have hap : 0 < |p| := hv.trans_le hpv
  have hp : p ≠ 0 := abs_pos.mp hap
  calc
    _ ≤ (criticalQ/2)*|p|^(criticalQ-2)*v^2 := evenGap_quadratic hp v
    _ = (criticalQ/2)*(|p|^(criticalQ-2)*v^2) := by ring
    _ ≤ (criticalQ/2)*v^criticalQ := by
      have h := critical_quadratic_le_power (show |v| ≤ |p| by rwa [abs_of_pos hv])
      rw [abs_of_pos hv] at h
      exact mul_le_mul_of_nonneg_left h (by linarith [criticalQ_one])
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [criticalQ_hi]) (Real.rpow_nonneg hv.le _)

private theorem near_split_uniform {l e p s : ℝ} (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) :
    balancedEvenGap criticalQ p (balancedNearShift l e l p s 1) ≤
      e * balancedEvenGap criticalQ p s + balancedEvenGap criticalQ p (2*l*(1-p))/2 := by
  let a : Fin 3 → ℝ := ![e, 1/2, 1/2-e]
  let x : Fin 3 → ℝ := ![s, 2*l*(1-p), 0]
  have ha (j : Fin 3) (_ : j ∈ Finset.univ) : 0 ≤ a j := by
    fin_cases j <;> simp [a] <;> linarith
  have hasum : ∑ i : Fin 3, a i = 1 := by
    simp [a, Fin.sum_univ_three]
    ring
  have h := (evenGap_convex criticalQ_one p).map_sum_le (p := x) ha hasum
    (fun j _ => mem_univ (x j))
  have hx : (∑ j : Fin 3, a j • x j) = balancedNearShift l e l p s 1 := by
    simp [a, x, Fin.sum_univ_three, smul_eq_mul, balancedNearShift_facet]
    ring
  rw [hx] at h
  have hz : balancedEvenGap criticalQ p 0 = 0 := by simp [balancedEvenGap]
  simp only [Fin.sum_univ_three, a, x, Matrix.cons_val, smul_eq_mul, hz, mul_zero, add_zero] at h
  linarith

private theorem w_power_small {w : ℝ} (hw : 0 < w) (hw₁ : w ≤ 1) :
    w^criticalQ ≤ w*(1+w)/2 := by
  have h := rpow_one_add_le_one_add_mul_self (s := w-1) (p := (1/2:ℝ)) (by linarith)
    (by norm_num) (by norm_num)
  rw [show 1+(w-1)=w by ring] at h
  have hpow : w^(criticalQ-1) ≤ (1+w)/2 := calc
    _ ≤ w^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_ge hw hw₁ (by linarith [criticalQ_lo])
    _ ≤ _ := by linarith
  rw [rpow_critical_split hw]
  have h := mul_le_mul_of_nonneg_left hpow hw.le
  linarith

private theorem small_power_loss {p : ℝ} (hp : 0 ≤ p) (hpU : p ≤ 1/8) :
    (4/5)*p - 22*p^criticalQ ≤ 1/250 := by
  by_cases hsmall : p ≤ 1/200
  · linarith only [hsmall, Real.rpow_nonneg hp criticalQ]
  · have hpL : 1/200 ≤ p := le_of_not_ge hsmall
    have hp₀ : 0 < p := (by norm_num : (0:ℝ) < 1/200).trans_le hpL
    have hcross : (1/25:ℝ) ≤ (1/200:ℝ)^(3/5:ℝ) := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        (le_natRat_rpow_iff (a := 1) (c := 1) (m := 3) (n := 5)
          (by decide : 0 < (200:ℕ)) (by decide : 0 < (25:ℕ)) (by decide)).2 (by decide)
    have hpow : (1/25:ℝ) ≤ p^(criticalQ-1) := hcross.trans
      ((Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1/200) hpL (by norm_num : (0:ℝ) ≤ 3/5)).trans
        (Real.rpow_le_rpow_of_exponent_ge hp₀ (hpU.trans (by norm_num)) (by linarith [criticalQ_hi])))
    rw [rpow_critical_split hp₀]
    have hm := mul_le_mul_of_nonneg_left hpow hp
    linarith only [hm, hp]

private theorem drift_scale_bound (i : Fin 13) {l : ℝ} (hl : 0 < l)
    (hlU : l ≤ g1SlabRight i) :
    ((1-g1SlabWeight i)/(2*g1SlabWeight i*l))*(2*l)^criticalQ ≤ 14/25 := by
  let μ := g1SlabWeight i
  have hm : 0 < μ := (slab_ranges i).2.2.2.1
  change ((1-μ)/(2*μ*l))*(2*l)^criticalQ ≤ 14/25
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hl.le, two_rpow_criticalQ, rpow_critical_split hl]
  calc
    _ = (3/2)*(1-μ)/μ*l^(criticalQ-1) := by field_simp [hm.ne', hl.ne']
    _ ≤ _ := slab_drift_upper i hl hlU

private theorem normalized_near_margin {μ l p : ℝ}
    (hm : 0 < μ) (hmU : μ ≤ 204/1000) (hl : 0 < l) (hlU : l ≤ 74/4096)
    (hp : |p| ≤ 1/8) (hR : ((1-μ)/(2*μ*l))*(2*l)^criticalQ ≤ 14/25) :
    1/1024 ≤ |p|^criticalQ - 1 + (313/200)*(1-p) -
      ((1-μ)/(2*μ*l))*balancedEvenGap criticalQ p (2*l*(1-p)) := by
  let w := 1-p
  let v := 2*l*w
  let D := (1-μ)/(2*μ*l)
  let A := balancedEvenGap criticalQ p v
  have hwL : 7/8 ≤ w := by dsimp [w]; linarith [(abs_le.mp hp).2]
  have hwU : w ≤ 9/8 := by dsimp [w]; linarith [(abs_le.mp hp).1]
  have hw : 0 < w := (by norm_num : (0:ℝ) < 7/8).trans_le hwL
  have hv : 0 < v := by dsimp [v]; positivity
  have hD : 0 ≤ D := by dsimp [D]; exact div_nonneg (by linarith) (by positivity)
  have hScale : D*v^criticalQ ≤ (14/25)*w^criticalQ := by
    rw [show v = (2*l)*w by rfl, Real.mul_rpow (by positivity) hw.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hw.le _)
  change 1/1024 ≤ |p|^criticalQ-1+(313/200)*w-D*A
  by_cases hp₀ : p ≤ 0
  · have hw₁ : 1 ≤ w := by dsimp [w]; linarith
    have hcost : D*A ≤ (14/25)*w^2 := calc
      _ ≤ D*v^criticalQ := by
        have h := evenGap_upper_power (zero_le_one.trans criticalQ_one) rpow_crit_upper_two p v
        rw [abs_of_pos hv] at h
        exact mul_le_mul_of_nonneg_left h hD
      _ ≤ (14/25)*w^criticalQ := hScale
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hw₁ rpow_crit_upper_two |>.trans_eq (Real.rpow_two _)) (by norm_num)
    have hdiff := mul_nonneg (show 0 ≤ (313/200:ℝ)-(14/25)*(w+1) by linarith)
      (sub_nonneg.mpr hw₁)
    nlinarith only [hcost, hdiff, Real.rpow_nonneg (abs_nonneg p) criticalQ]
  · have hp₀' : 0 ≤ p := (lt_of_not_ge hp₀).le
    have hpU : p ≤ 1/8 := (abs_le.mp hp).2
    have hw₁ : w ≤ 1 := by dsimp [w]; linarith
    have hwprod : 0 ≤ w*(1+w)/2 := by positivity
    have hwPow := w_power_small hw hw₁
    have hcost_base : D*v^criticalQ ≤ (14/25)*(w*(1+w)/2) :=
      hScale.trans (mul_le_mul_of_nonneg_left hwPow (by norm_num))
    by_cases hsmall : p ≤ v
    · have hF : D*A ≤ D*v^criticalQ - (D*(1-criticalQ/2))*p^criticalQ := by
        have h := evenGap_drift_small hv (show |p| ≤ v by rwa [abs_of_nonneg hp₀'])
        rw [abs_of_nonneg hp₀'] at h
        have h := mul_le_mul_of_nonneg_left h hD
        nlinarith only [h]
      have hDenU : 2*μ*l ≤ 2*(204/1000)*(74/4096) := by
        have := mul_le_mul (show 2*μ ≤ 2*(204/1000) by linarith) hlU hl.le
          (by norm_num : (0:ℝ) ≤ 2*(204/1000))
        exact this
      have hDL : 105 ≤ D := (le_div_iff₀ (by positivity : 0 < 2*μ*l)).2 (by linarith)
      have hcoef : 21 ≤ D*(1-criticalQ/2) := calc
        _ = 105*(1/5:ℝ) := by norm_num
        _ ≤ _ := mul_le_mul hDL (by linarith [criticalQ_hi])
          (by norm_num) hD
      have hdiscount := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hp₀' criticalQ)
      have hcost : D*A ≤ (14/25)*(w*(1+w)/2) - 21*p^criticalQ := by
        linarith only [hF, hcost_base, hdiscount]
      have hLoss := small_power_loss hp₀' hpU
      have hquad := mul_nonneg hp₀' (sub_nonneg.mpr hpU)
      rw [abs_of_nonneg hp₀']
      dsimp [w] at hcost ⊢
      nlinarith only [hcost, hLoss, hquad, hp₀']
    · have hF := mul_le_mul_of_nonneg_left
        (evenGap_drift_large hv (show v ≤ |p| by rw [abs_of_nonneg hp₀']; exact (lt_of_not_ge hsmall).le)) hD
      have hscaled := mul_le_mul_of_nonneg_left hcost_base (by norm_num : (0:ℝ) ≤ 4/5)
      have hcost : D*A ≤ (56/125)*(w*(1+w)/2) := by nlinarith only [hF, hscaled]
      have hdiff := mul_nonneg (sub_nonneg.mpr hwL)
        (show 0 ≤ (313/200:ℝ)-(28/125)*(w+7/8+1) by linarith)
      nlinarith only [hcost, hdiff, Real.rpow_nonneg (abs_nonneg p) criticalQ]

private theorem far_normalized_gap_of_drift {μ l e p s : ℝ}
    (hm : 0 < μ) (hmU : μ ≤ 204/1000) (hl : 0 < l) (hLen : l ≤ 74/4096)
    (hDrift : ((1-μ)/(2*μ*l))*(2*l)^criticalQ ≤ 14/25)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hp : |p| ≤ 1/8) :
    (μ/1024)*l ≤ balancedFacetGap criticalQ μ l e p s 1 := by
  let J := balancedJensenGap criticalQ l p 1
  let C := balancedEvenGap criticalQ p (2*l*(1-p))
  let A := balancedEvenGap criticalQ p s
  have hb : 0 ≤ 1-μ := by linarith
  have hnormalized := normalized_near_margin hm hmU hl hLen hp hDrift
  have hDiff : 1/1024 ≤ J/l - ((1-μ)/(2*μ*l))*C :=
    hnormalized.trans (sub_le_sub_right (far_jensen_linear hl hLen hp) _)
  have hscale := mul_le_mul_of_nonneg_left hDiff (mul_nonneg hm.le hl.le)
  have hcancel : μ*l*(J/l-((1-μ)/(2*μ*l))*C) = μ*J - (1-μ)*C/2 := by
    have hμ₀ : μ ≠ 0 := hm.ne'
    field_simp [hl.ne', hμ₀]
  rw [hcancel] at hscale
  have hNear := mul_le_mul_of_nonneg_left (near_split_uniform (l := l) (p := p) (s := s) he₀ he₁) hb
  have hFar := mul_le_mul_of_nonneg_left (far_absorption (s := s) hl.le hLen he₀ he₁ hp) hm.le
  have hA := evenGap_nonneg criticalQ_one p s
  have hprod := mul_le_mul_of_nonneg_left (show 1/2+e ≤ 1 by linarith)
    (show 0 ≤ (20/9)*μ from mul_nonneg (by norm_num) hm.le)
  have hfactor : 0 ≤ (1-μ) - (20/9)*μ*(1/2+e) := by nlinarith only [hprod, hmU]
  have hcoef : 0 ≤ 1-μ*(1-l)-(1-μ)*e-μ*((20/9)*(1-e^2)) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr he₁) hfactor, mul_nonneg hm.le hl.le, hmU]
  change (μ/1024)*l ≤ balancedFacetGap criticalQ μ l e p s 1
  calc
    _ = μ*l*(1/1024) := by ring
    _ ≤ μ*J-(1-μ)*C/2 := hscale
    _ ≤ _ := by
      unfold balancedFacetGap
      dsimp [J, C, A]
      nlinarith only [hNear, hFar, mul_nonneg hcoef hA]

theorem g1_far_gap_of_drift {μ l e p s z : ℝ}
    (hm : 0 < μ) (hmU : μ ≤ 204/1000) (hl : 0 < l) (hLen : l ≤ 74/4096)
    (hDrift : ((1-μ)/(2*μ*l))*(2*l)^criticalQ ≤ 14/25) (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2)
    (hfar : 8*|p| ≤ |z|) :
    (μ/1024)*l*|z|^criticalQ ≤ balancedFacetGap criticalQ μ l e p s z := by
  by_cases hz : z = 0
  · have hp : p = 0 := by
      rw [hz, abs_zero] at hfar
      exact abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg p))
    subst z
    subst p
    have he : |e| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
    have hm₁ : μ ≤ 1 := hmU.trans (by norm_num)
    have hF := balancedFacetGap_transverse_bound (l := l) criticalQ_one rpow_crit_upper_two hm.le hm₁ he s
    have hcoef : 0 ≤ (1-3*μ)*(1-|e|)+μ*l :=
      add_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr he)) (mul_nonneg hm.le hl.le)
    simp only [abs_zero, Real.zero_rpow (show criticalQ ≠ 0 by linarith [criticalQ_one]), mul_zero]
    exact (mul_nonneg hcoef (Real.rpow_nonneg (abs_nonneg s) _)).trans hF
  have hp : |p/z| ≤ 1/8 := by
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hz)).2 (by linarith)
  have h := mul_le_mul_of_nonneg_right
    (far_normalized_gap_of_drift (s := s/z) hm hmU hl hLen hDrift he₀ he₁ hp)
    (Real.rpow_nonneg (abs_nonneg z) criticalQ)
  rw [mul_comm (balancedFacetGap criticalQ μ l e (p/z) (s/z) 1),
    ← balancedFacetGap_scale, mul_div_cancel₀ _ hz, mul_div_cancel₀ _ hz, mul_one] at h
  exact h

private theorem far_gap_for_slab_weight (i : Fin 13) {l e p s z : ℝ}
    (hl : 0 < l) (hlU : l ≤ g1SlabRight i) (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2)
    (hfar : 8*|p| ≤ |z|) :
    (g1SlabWeight i/1024)*l*|z|^criticalQ ≤ balancedFacetGap criticalQ (g1SlabWeight i) l e p s z := by
  obtain ⟨_, _, hL, hm, hmU⟩ := slab_ranges i
  exact g1_far_gap_of_drift hm hmU hl (hlU.trans hL) (drift_scale_bound i hl hlU) he₀ he₁ hfar

/-- Each of the thirteen written weights works on its own length slab for the
entire upper-facet far chart, with a common normalized margin. The two slab
endpoints interpolate with the same profile weight and an affine input margin. -/
theorem g1_slab_far_gap (i : Fin 13) {l e p s z : ℝ}
    (hl₀ : g1SlabLeft i ≤ l) (hl₁ : l ≤ g1SlabRight i)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hfar : 8*|p| ≤ |z|) :
    (g1SlabWeight i/1024)*l*|z|^criticalQ ≤ balancedFacetGap criticalQ (g1SlabWeight i) l e p s z := by
  let μ := g1SlabWeight i
  let a := μ/1024
  let l₀ := g1SlabLeft i
  let l₁ := g1SlabRight i
  obtain ⟨hL₀, hL, _, hm, hmU⟩ := slab_ranges i
  have hd : 0 < l₁-l₀ := sub_pos.mpr hL
  let u := (l-l₀)/(l₁-l₀)
  have hu₀ : 0 ≤ u := div_nonneg (sub_nonneg.mpr hl₀) hd.le
  have hu₁ : u ≤ 1 := (div_le_one hd).2 (sub_le_sub_right hl₁ _)
  have hlen : l = (1-u)*l₀+u*l₁ := by
    dsimp [u]
    field_simp [hd.ne']
    ring
  have hπ := (isSimplex_balancedPi (μ := μ) hm.le (hmU.trans (by norm_num))
    (show |e| ≤ 1 by rw [abs_of_nonneg he₀]; linarith)).1
  have hleft := (weightedRow_farMargin_iff criticalQ μ a l₀ e p s z).2
    (far_gap_for_slab_weight i hL₀ hL.le he₀ he₁ hfar)
  have hright := (weightedRow_farMargin_iff criticalQ μ a l₁ e p s z).2
    (far_gap_for_slab_weight i (hL₀.trans hL) le_rfl he₀ he₁ hfar)
  have hprofile : balancedProfile l e l =
      profileLerp u (balancedProfile l₀ e l₀) (balancedProfile l₁ e l₁) := by
    funext j
    rw [hlen]
    fin_cases j <;> simp [balancedProfile, splitProfile, profileLerp] <;> ring
  have hgamma : farMarginGamma μ a l =
      rowLerp u (farMarginGamma μ a l₀) (farMarginGamma μ a l₁) := by
    funext j
    rw [hlen]
    fin_cases j <;> simp (config := {decide := true}) [farMarginGamma, balancedGamma, rowLerp] <;> ring
  apply (weightedRow_farMargin_iff criticalQ μ a l e p s z).1
  rw [hprofile, hgamma]
  exact weightedRow_profileLerp criticalQ_one hu₀ hu₁ hπ hleft hright

end HlawkaSchatten.BelowExponent
