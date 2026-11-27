/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Compact
import all HlawkaSchatten.BelowExponent.G1Compact
import all HlawkaSchatten.BelowExponent.G1Large
import Batteries.Tactic.OpenPrivate

/-! Quartic remainder bounds for the near terms of the G3 p = 1 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set Filter Topology
open private choose_nonneg_of_lt binomial_hasSum from HlawkaSchatten.BelowExponent.G1Compact
open private absPower_deriv from HlawkaSchatten.BelowExponent.G1Large

noncomputable section

def g3NearC2 : ℝ := criticalQ * (criticalQ - 1) / 2

def g3NearC4 : ℝ := criticalQ * Ring.choose (criticalQ - 1) 3 / 4

theorem g3NearC4_eq : g3NearC4 = Ring.choose criticalQ 4 := by
  have h := Ring.choose_smul_choose criticalQ (by decide : 1 ≤ (4 : ℕ))
  have h' : (4 : ℝ) * Ring.choose criticalQ 4 =
      criticalQ * Ring.choose (criticalQ - 1) 3 := by
    norm_num [nsmul_eq_mul, Nat.choose_one_right] at h ⊢
    exact h
  unfold g3NearC4
  linarith only [h']

def g3NearRemainder (t : ℝ) : ℝ :=
  balancedEvenGap criticalQ 1 t - g3NearC2 * t ^ 2 - g3NearC4 * t ^ 4

private theorem q_lo : 1 < criticalQ :=
  (by norm_num : (1 : ℝ) < 1054 / 665).trans criticalQ_bracket.1

private theorem q_hi : criticalQ < 2 :=
  criticalQ_bracket.2.trans (by norm_num)

private theorem choose_odd_nonneg {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) {n : ℕ}
    (hn : Odd n) : 0 ≤ Ring.choose r n := by
  obtain ⟨j, hj⟩ := hn
  have hn₁ : 1 ≤ n := by omega
  let k := n - 1
  have hki : Even (k : ℤ) := ⟨(j : ℤ), by
    have h : k = j + j := by dsimp [k]; omega
    exact_mod_cast h⟩
  have h := Ring.choose_smul_choose r hn₁
  simp only [Nat.cast_one] at h
  change (n.choose 1) • Ring.choose r n = Ring.choose r 1 * Ring.choose (r - 1) k at h
  have hc : 0 ≤ Ring.choose (r - 1) k := by
    rw [show r - 1 = -(1 - r) by ring, Ring.choose_neg,
      show Int.negOnePow (k : ℤ) = 1 from Int.negOnePow_even _ hki, one_smul]
    exact choose_nonneg_of_lt (by linarith)
  have hchoose : Ring.choose r 1 = r := by simp
  rw [nsmul_eq_mul, Nat.choose_one_right, hchoose] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn₁
  exact nonneg_of_mul_nonneg_right (show 0 ≤ (n : ℝ) * Ring.choose r n by
    rw [h]; exact mul_nonneg hr hc) hn'

private def oddCoefficient (r : ℝ) (n : ℕ) : ℝ :=
  if Odd n then Ring.choose r n else 0

private def nearSlope (t : ℝ) : ℝ :=
  criticalQ * ((1 + t) ^ (criticalQ - 1) - (1 - t) ^ (criticalQ - 1)) / 2

private def remainderSlope (t : ℝ) : ℝ :=
  nearSlope t - 2 * g3NearC2 * t - 4 * g3NearC4 * t ^ 3

private theorem remainder_hasDeriv {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt g3NearRemainder (remainderSlope t) t := by
  have h₁ : 0 ≤ 1 + t := by linarith [ht.1]
  have h₂ : 0 ≤ 1 - t := by linarith [ht.2]
  have hd₁ := (absPower_deriv q_lo (1 + t)).comp t ((hasDerivAt_id t).const_add 1)
  have hd₂ := (absPower_deriv q_lo (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
  rw [ite_eq_left h₁, abs_of_nonneg h₁] at hd₁
  rw [ite_eq_left h₂, abs_of_nonneg h₂] at hd₂
  have hd := (((hd₁.add hd₂).div_const 2).sub_const (|(1 : ℝ)| ^ criticalQ)).sub
    (((hasDerivAt_id t).pow 2).const_mul g3NearC2)
  convert hd.sub (((hasDerivAt_id t).pow 4).const_mul g3NearC4) using 1
  · funext x
    rfl
  · dsimp [remainderSlope, nearSlope]
    ring

private theorem remainderSlope_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => criticalQ * oddCoefficient (criticalQ - 1) (n + 5) * t ^ (n + 5))
      (remainderSlope t) := by
  let r := criticalQ - 1
  let f (n : ℕ) := criticalQ * oddCoefficient r n * t ^ n
  have h₁ := binomial_hasSum (q := r) ht
  have h₂ := binomial_hasSum (q := r) (by simpa only [abs_neg] using ht : |-t| < 1)
  have h := (h₁.sub h₂).mul_left (criticalQ / 2)
  have hsum : HasSum f (nearSlope t) := by
    rw [nearSlope, div_eq_inv_mul]
    rw [show (1 - t : ℝ) = 1 + -t by ring]
    convert h using 1
    · funext n
      rcases Nat.even_or_odd n with hn | hn
      · simp only [f, oddCoefficient, ite_eq_right (Nat.not_odd_iff_even.mpr hn), hn.neg_pow]
        ring
      · simp only [f, oddCoefficient, ite_eq_left hn, hn.neg_pow]
        ring
    · dsimp [r]
      ring
  have htail := (hasSum_nat_add_iff' 5).mpr hsum
  have hpre : ∑ n ∈ Finset.range 5, f n = 2 * g3NearC2 * t + 4 * g3NearC4 * t ^ 3 := by
    simp [Finset.sum_range_succ, f, oddCoefficient, g3NearC2, g3NearC4, r,
      (by decide : Odd (3 : ℕ)), (by decide : ¬Odd (2 : ℕ)), (by decide : ¬Odd (4 : ℕ))]
    ring
  rw [hpre] at htail
  convert htail using 1
  unfold remainderSlope
  ring

private theorem remainderSlope_coeff_nonneg (n : ℕ) :
    0 ≤ criticalQ * oddCoefficient (criticalQ - 1) (n + 5) := by
  apply mul_nonneg (by linarith [q_lo])
  unfold oddCoefficient
  split
  · exact choose_odd_nonneg (by linarith [q_lo]) (by linarith [q_hi]) (by assumption)
  · exact le_rfl

private theorem remainderSlope_continuous : Continuous remainderSlope := by
  have hq : 0 ≤ criticalQ - 1 := by linarith [q_lo]
  unfold remainderSlope nearSlope
  fun_prop (disch := assumption)

private theorem remainderSlope_one_le : remainderSlope 1 ≤ criticalQ * (7 / 4 - criticalQ) := by
  have h₂ : (2 : ℝ) ^ (criticalQ - 1) = 3 / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, two_rpow_criticalQ]
  have h₄ : 0 ≤ g3NearC4 := by
    exact div_nonneg (mul_nonneg (by linarith [q_lo])
      (choose_odd_nonneg (by linarith [q_lo]) (by linarith [q_hi]) (by decide))) (by norm_num)
  simp only [remainderSlope, nearSlope, one_add_one_eq_two, sub_self, h₂,
    Real.zero_rpow (sub_ne_zero.mpr q_lo.ne'), sub_zero, one_pow, mul_one, g3NearC2]
  linarith only [h₄]

theorem g3NearRemainder_hasDeriv {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ d, HasDerivAt g3NearRemainder d t ∧
      0 ≤ d ∧ d ≤ criticalQ * (7 / 4 - criticalQ) * t ^ 5 := by
  have ht₀ := ht.1
  have ht₁ := ht.2
  have hsmall (x : ℝ) (hx : |x| < 1) := remainderSlope_hasSum hx
  have hpos (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) : 0 ≤ remainderSlope x :=
    hasSum_le (fun n => mul_nonneg (remainderSlope_coeff_nonneg n) (pow_nonneg hx₀ _))
      hasSum_zero (hsmall x (by rwa [abs_of_nonneg hx₀]))
  have hpos₁ : 0 ≤ remainderSlope 1 := by
    apply ge_of_tendsto (remainderSlope_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      : Tendsto remainderSlope (𝓝[<] 1) (𝓝 (remainderSlope 1)))
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx₀
    exact hpos x hx₀.le hx
  refine ⟨remainderSlope t, remainder_hasDeriv ht, ?_⟩
  obtain rfl | ht₁ := ht₁.eq_or_lt
  · exact ⟨hpos₁, by simpa using remainderSlope_one_le⟩
  refine ⟨hpos t ht₀ ht₁, ?_⟩
  have ht' : |t| < 1 := by rwa [abs_of_nonneg ht₀]
  have hcmp (x : ℝ) (htx : t ≤ x) (hx : x < 1) :
      x ^ 5 * remainderSlope t ≤ t ^ 5 * remainderSlope x := by
    have hx₀ := ht₀.trans htx
    refine hasSum_le (fun n => ?_) ((hsmall t ht').mul_left _)
      ((hsmall x (by rwa [abs_of_nonneg hx₀])).mul_left _)
    convert mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀ htx n)
      (mul_nonneg (remainderSlope_coeff_nonneg n) (mul_nonneg (pow_nonneg ht₀ 5)
        (pow_nonneg hx₀ 5))) using 1 <;> rw [pow_add] <;> ring
  have hleft : Tendsto (fun x : ℝ => x ^ 5 * remainderSlope t) (𝓝[<] 1)
      (𝓝 ((1:ℝ)^5 * remainderSlope t)) :=
    (((continuous_id.pow 5).mul continuous_const).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun x : ℝ => t ^ 5 * remainderSlope x) (𝓝[<] 1)
      (𝓝 (t ^ 5 * remainderSlope 1)) :=
    ((continuous_const.mul remainderSlope_continuous).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hup := le_of_tendsto_of_tendsto hleft hright <| by
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (lt_mem_nhds ht₁)] with x hx htx
    exact hcmp x htx.le hx
  simp only [one_pow, one_mul] at hup
  rw [mul_comm (criticalQ * (7 / 4 - criticalQ))]
  exact hup.trans (mul_le_mul_of_nonneg_left remainderSlope_one_le (pow_nonneg ht₀ 5))

private theorem g3NearRemainder_secant {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    0 ≤ g3NearRemainder y - g3NearRemainder x ∧
    g3NearRemainder y - g3NearRemainder x ≤ criticalQ * (7 / 4 - criticalQ) * y ^ 5 * (y - x) := by
  obtain rfl | hxy := hxy.eq_or_lt
  · simp
  have hdomain : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx hy
  have hcont : ContinuousOn g3NearRemainder (Icc x y) := fun t ht =>
    (remainder_hasDeriv (hdomain ht)).continuousAt.continuousWithinAt
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope g3NearRemainder remainderSlope hxy hcont
    (fun t ht => remainder_hasDeriv (hdomain (Ioo_subset_Icc_self ht)))
  have htab := hdomain (Ioo_subset_Icc_self ht)
  obtain ⟨d, hd, hd₀, hdb⟩ := g3NearRemainder_hasDeriv htab
  have hdvalue : d = remainderSlope t := hd.unique (remainder_hasDeriv htab)
  rw [hdvalue, heq] at hd₀ hdb
  have hq : 0 ≤ criticalQ * (7 / 4 - criticalQ) :=
    mul_nonneg (by linarith [q_lo]) (by linarith [criticalQ_bracket.2])
  refine ⟨by simpa only [zero_mul] using (le_div_iff₀ (sub_pos.mpr hxy)).mp hd₀,
    (div_le_iff₀ (sub_pos.mpr hxy)).mp ?_⟩
  exact hdb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htab.1 ht.2.le 5) hq)

private theorem g3NearEven_abs (t : ℝ) :
    balancedEvenGap criticalQ 1 t = balancedEvenGap criticalQ 1 |t| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht]
    simp only [balancedEvenGap, sub_neg_eq_add, ← sub_eq_add_neg (1 : ℝ) t]
    ring

theorem g3NearEven_lower {s : ℝ} (hs : |s| ≤ 1) :
    g3NearC2 * s ^ 2 + g3NearC4 * s ^ 4 ≤ balancedEvenGap criticalQ 1 s := by
  have h := (g3NearRemainder_secant (x := 0) (y := |s|) le_rfl (abs_nonneg s) hs).1
  have hfour : |s| ^ 4 = s ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_mul, sq_abs]
  rw [g3NearRemainder, g3NearRemainder, ← g3NearEven_abs, sq_abs, hfour] at h
  have hzero : balancedEvenGap criticalQ 1 0 = 0 := by simp [balancedEvenGap]
  simp only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, sub_zero] at h
  linarith only [h]

/-- A quadratic and quartic lower bound on the divided difference in the near chart. -/
theorem g3NearDivided_lower {h s w : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hs : |s| ≤ 1) (hw : |w| ≤ 1) :
    let v := (1 - h) * s + h * w
    let D₂ := (2 - h) * s ^ 2 - 2 * (1 - h) * w * s - h * w ^ 2
    g3NearC2 * D₂ + g3NearC4 * D₂ * (s ^ 2 + v ^ 2) -
        criticalQ * (7 / 4 - criticalQ) * |w| ^ 5 * max 0 (|w| - |s|) ≤
      (balancedEvenGap criticalQ 1 s - balancedEvenGap criticalQ 1 v) / h := by
  dsimp only
  let v := (1 - h) * s + h * w
  let D₂ := (2 - h) * s ^ 2 - 2 * (1 - h) * w * s - h * w ^ 2
  let K := criticalQ * (7 / 4 - criticalQ)
  have hK : 0 ≤ K := mul_nonneg (by linarith [q_lo]) (by linarith [criticalQ_bracket.2])
  have hv' : |v| ≤ (1 - h) * |s| + h * |w| := by
    dsimp [v]
    simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr hh₁), abs_of_nonneg hh.le] using
      abs_add_le ((1 - h) * s) (h * w)
  have hv : |v| ≤ 1 := hv'.trans (by
    have ha := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hh₁)
    have hb := mul_le_mul_of_nonneg_left hw hh.le
    linarith only [ha, hb])
  have hrem : -K * |w| ^ 5 * max 0 (|w| - |s|) * h ≤
      g3NearRemainder |s| - g3NearRemainder |v| := by
    rcases le_or_gt |v| |s| with hle | hlt
    · have hr := (g3NearRemainder_secant (abs_nonneg v) hle hs).1
      have hp := mul_nonneg (mul_nonneg (mul_nonneg hK (pow_nonneg (abs_nonneg w) 5))
        (le_max_left (0 : ℝ) (|w| - |s|))) hh.le
      linarith only [hr, hp]
    · have hsw : |s| < |w| := by
        by_contra! hn
        linarith only [hlt, hv', mul_le_mul_of_nonneg_left hn hh.le]
      have hvw : |v| ≤ |w| := by
        linarith only [hv', mul_le_mul_of_nonneg_left hsw.le (sub_nonneg.mpr hh₁)]
      have hhmax : |v| - |s| ≤ max 0 (|w| - |s|) * h := by
        rw [max_eq_right (sub_nonneg.mpr hsw.le)]
        linarith only [hv']
      have hr := (g3NearRemainder_secant (abs_nonneg s) hlt.le hv).2
      change g3NearRemainder |v| - g3NearRemainder |s| ≤ K * |v| ^ 5 * (|v| - |s|) at hr
      have hpow : K * |v| ^ 5 ≤ K * |w| ^ 5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg v) hvw 5) hK
      have hc := mul_le_mul hpow hhmax (sub_nonneg.mpr hlt.le)
        (mul_nonneg hK (pow_nonneg (abs_nonneg w) 5))
      linarith only [hr, hc]
  have hrem_eq (x : ℝ) : g3NearRemainder |x| =
      balancedEvenGap criticalQ 1 x - g3NearC2 * x ^ 2 - g3NearC4 * x ^ 4 := by
    have hfour : |x| ^ 4 = x ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_mul, sq_abs]
    rw [g3NearRemainder, ← g3NearEven_abs, sq_abs, hfour]
  rw [hrem_eq, hrem_eq] at hrem
  have hD : D₂ * h = s ^ 2 - v ^ 2 := by dsimp [D₂, v]; ring
  have hfour : D₂ * (s ^ 2 + v ^ 2) * h = s ^ 4 - v ^ 4 := by
    calc
      _ = (D₂ * h) * (s ^ 2 + v ^ 2) := by ring
      _ = _ := by rw [hD]; ring
  change g3NearC2 * D₂ + g3NearC4 * D₂ * (s ^ 2 + v ^ 2) -
    K * |w| ^ 5 * max 0 (|w| - |s|) ≤
    (balancedEvenGap criticalQ 1 s - balancedEvenGap criticalQ 1 v) / h
  apply (le_div_iff₀ hh).2
  rw [show (g3NearC2 * D₂ + g3NearC4 * D₂ * (s ^ 2 + v ^ 2) -
    K * |w| ^ 5 * max 0 (|w| - |s|)) * h =
    g3NearC2 * (D₂ * h) + g3NearC4 * (D₂ * (s ^ 2 + v ^ 2) * h) -
    K * |w| ^ 5 * max 0 (|w| - |s|) * h by ring, hD, hfour]
  linarith only [hrem]

end

end HlawkaSchatten.BelowExponent
