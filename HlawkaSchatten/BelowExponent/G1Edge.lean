/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Compact
public import HlawkaSchatten.BelowExponent.G3PJensen
import all HlawkaSchatten.BelowExponent.G1
import all HlawkaSchatten.BelowExponent.G1Far
import all HlawkaSchatten.BelowExponent.G1Large
import all HlawkaSchatten.BelowExponent.G1Compact

/-! The balanced G1 weight down to zero depth, with a single analytic compact chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open private rpow_critical_split from HlawkaSchatten.BelowExponent.G1
open private criticalQ_lo criticalQ_hi criticalQ_one drift_scale_bound from HlawkaSchatten.BelowExponent.G1Far
open private absPower_deriv g1_large_gap from HlawkaSchatten.BelowExponent.G1Large
open private g1Curvature g1Curvature_le_half compact_compensated_lower
  compact_gap_of_certificates from HlawkaSchatten.BelowExponent.G1Compact

noncomputable section

def g1EdgeWeight (l : ℝ) : ℝ := (47 / 1000) * (4096 * l) ^ (41 / 100 : ℝ)

private def edgeThreshold (l : ℝ) : ℝ := (1 / 90) * (4096 * l) ^ (49 / 50 : ℝ)

private theorem q19 : (19 : ℝ) / 12 ≤ criticalQ :=
  (by norm_num : (19 : ℝ) / 12 ≤ 1054 / 665).trans criticalQ_lo

private theorem edgeScale {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    0 < 4096 * l ∧ 4096 * l ≤ 1 := ⟨by positivity, by linarith⟩

theorem g1EdgeWeight_bounds {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    0 < g1EdgeWeight l ∧ g1EdgeWeight l ≤ 47 / 1000 := by
  obtain ⟨hx, hx₁⟩ := edgeScale hl hL
  refine ⟨mul_pos (by norm_num) (Real.rpow_pos_of_pos hx _), ?_⟩
  unfold g1EdgeWeight
  have hb := Real.rpow_le_one hx.le hx₁ (by norm_num : (0 : ℝ) ≤ 41 / 100)
  linarith

theorem g1EdgeWeight_join : g1EdgeWeight (1 / 4096) = g1SlabWeight 0 := by
  norm_num [g1EdgeWeight, g1SlabWeight, g1WeightNumerator]

private theorem edge_depth_ratio {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    l / g1EdgeWeight l ≤ 1 / 180 := by
  obtain ⟨hx, hx₁⟩ := edgeScale hl hL
  have hp := Real.rpow_le_rpow_of_exponent_ge hx hx₁
    (by norm_num : (41 / 100 : ℝ) ≤ 1)
  rw [Real.rpow_one] at hp
  apply (div_le_iff₀ (g1EdgeWeight_bounds hl hL).1).2
  unfold g1EdgeWeight
  linarith only [hp, hl]

private theorem edge_base_power :
    (1 / 4096 : ℝ) ^ (criticalQ - 1) = (2 / 3 : ℝ) ^ (12 : ℕ) := by
  have hhalf : (1 / 2 : ℝ) ^ (criticalQ - 1) = 2 / 3 := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.rpow_sub (by norm_num), Real.rpow_one, two_rpow_criticalQ]
    norm_num
  rw [show (1 / 4096 : ℝ) = (1 / 2 : ℝ) ^ (12 : ℝ) by norm_num [Real.rpow_ofNat],
    ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num), hhalf, Real.rpow_ofNat]

private theorem edge_drift_ratio {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    l ^ (criticalQ - 1) / g1EdgeWeight l ≤ 1 / 6 := by
  obtain ⟨hx, hx₁⟩ := edgeScale hl hL
  have hp := Real.rpow_le_rpow_of_exponent_ge hx hx₁
    (by linarith [q19] : (41 / 100 : ℝ) ≤ criticalQ - 1)
  have h := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ (2 / 3) ^ (12 : ℕ))
  apply (div_le_iff₀ (g1EdgeWeight_bounds hl hL).1).2
  rw [show l ^ (criticalQ - 1) = ((1 / 4096) * (4096 * l)) ^ (criticalQ - 1) by ring_nf,
    Real.mul_rpow (by norm_num) hx.le, edge_base_power, g1EdgeWeight]
  have hpos := Real.rpow_nonneg hx.le (41 / 100 : ℝ)
  linarith only [h, hpos]

private theorem edge_far_drift {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    ((1 - g1EdgeWeight l) / (2 * g1EdgeWeight l * l)) * (2 * l) ^ criticalQ ≤ 14 / 25 := by
  let μ := g1EdgeWeight l
  have hm := (g1EdgeWeight_bounds hl hL).1
  let hp := l ^ (criticalQ - 1) / μ
  have hp₀ : 0 ≤ hp := by
    dsimp [hp]
    exact div_nonneg (Real.rpow_nonneg hl.le _) hm.le
  have hp₁ : hp ≤ 1 / 6 := edge_drift_ratio hl hL
  rw [Real.mul_rpow (by norm_num) hl.le, two_rpow_criticalQ, rpow_critical_split hl]
  change ((1 - μ) / (2 * μ * l)) * (3 * (l * l ^ (criticalQ - 1))) ≤ 14 / 25
  rw [show ((1 - μ) / (2 * μ * l)) * (3 * (l * l ^ (criticalQ - 1))) =
      (3 / 2) * ((1 - μ) * hp) by dsimp [hp]; field_simp [hm.ne', hl.ne']]
  have h := mul_le_mul_of_nonneg_right (show 1 - μ ≤ 1 by linarith only [hm]) hp₀
  linarith only [h, hp₁]

private theorem edgeThreshold_bounds {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    0 < edgeThreshold l ∧ edgeThreshold l ≤ 1 / 90 := by
  obtain ⟨hx, hx₁⟩ := edgeScale hl hL
  refine ⟨mul_pos (by norm_num) (Real.rpow_pos_of_pos hx _), ?_⟩
  unfold edgeThreshold
  have hb := Real.rpow_le_one hx.le hx₁ (by norm_num : (0 : ℝ) ≤ 49 / 50)
  linarith

private theorem edge_alpha {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    g1EdgeWeight l * (criticalQ / 2 * (edgeThreshold l) ^ (criticalQ - 2)) ≤ 1 / 4 := by
  obtain ⟨hx, hx₁⟩ := edgeScale hl hL
  let x := 4096 * l
  have hcross : (90 : ℝ) ^ (5 / 12 : ℝ) ≤ 33 / 5 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using
      (natRat_rpow_le_iff (a := 90) (c := 33) (m := 5) (n := 12)
        (by decide : 0 < (1 : ℕ)) (by decide : 0 < (5 : ℕ)) (by decide)).2 (by decide)
  have hc : (1 / 90 : ℝ) ^ (criticalQ - 2) ≤ 33 / 5 := by
    refine (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show -(5/12 : ℝ) ≤ criticalQ - 2 by linarith [q19])).trans ?_
    rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, one_div, inv_inv]
    exact hcross
  have hprod : x ^ (41 / 100 : ℝ) * x ^ ((49 / 50 : ℝ) * (criticalQ - 2)) ≤ 1 := by
    rw [← Real.rpow_add hx]
    exact Real.rpow_le_one hx.le hx₁ (by linarith [q19])
  have hc' : criticalQ / 2 * (1 / 90 : ℝ) ^ (criticalQ - 2) ≤ (4 / 5) * (33 / 5) :=
    mul_le_mul (by linarith [criticalQ_hi]) hc (Real.rpow_nonneg (by norm_num) _)
      (by norm_num)
  unfold g1EdgeWeight edgeThreshold
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  change (47 / 1000) * x ^ (41 / 100 : ℝ) *
    (criticalQ / 2 * ((1 / 90 : ℝ) ^ (criticalQ - 2) * x ^ ((49 / 50 : ℝ) * (criticalQ - 2)))) ≤ _
  have h₀ : 0 ≤ x ^ (41 / 100 : ℝ) * x ^ ((49 / 50 : ℝ) * (criticalQ - 2)) := by positivity
  have h := mul_le_mul hc' hprod h₀ (by norm_num)
  nlinarith only [h]

private theorem edge_beta {l : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096) :
    (1 - criticalQ / 2) * (edgeThreshold l) ^ criticalQ ≤ (7 / 10) * l := by
  obtain ⟨hx, hx₁⟩ := edgeScale hl hL
  have hcross : (1 / 90 : ℝ) ^ (19 / 12 : ℝ) ≤ 21 / 26000 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (natRat_rpow_le_iff (a := 1) (c := 21) (m := 19) (n := 12)
        (by decide : 0 < (90 : ℕ)) (by decide : 0 < (26000 : ℕ)) (by decide)).2 (by decide)
  have hc := (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) q19).trans hcross
  have hexp := Real.rpow_le_rpow_of_exponent_ge hx hx₁
    (show (1 : ℝ) ≤ (49 / 50) * criticalQ by linarith [q19])
  rw [Real.rpow_one] at hexp
  have hconst : (1 - criticalQ / 2) * (1 / 90 : ℝ) ^ criticalQ ≤ (5 / 24) * (21 / 26000) :=
    mul_le_mul (by linarith [q19]) hc (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  unfold edgeThreshold
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le, ← mul_assoc]
  have h := mul_le_mul hconst hexp (Real.rpow_nonneg hx.le _) (by norm_num)
  linarith only [h, hl]

private theorem edge_curvature : 23 / 50 ≤ g1Curvature := by
  have hb : (19 / 12 : ℝ) * (7 / 12) ≤ criticalQ * (criticalQ - 1) :=
    mul_le_mul q19 (by linarith [q19]) (by norm_num) (by linarith [q19])
  unfold g1Curvature
  linarith only [hb]

private theorem edge_near_center {l z : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4000)
    (hZ₁ : |balancedFarCenter l l 1 z| ≤ 1 / 90) :
    |z| ≤ 1 / 32 ∧ (3 / 4 : ℝ) ≤ g3DividedJensen l z := by
  let Z := balancedFarCenter l l 1 z
  change |Z| ≤ 1 / 90 at hZ₁
  have hlin : (1 - l) * z = Z - l := by dsimp [Z, balancedFarCenter]; ring
  have habs : (1 - l) * |z| ≤ |Z| + l := by
    rw [← abs_of_nonneg (show 0 ≤ 1 - l by linarith), ← abs_mul, hlin]
    simpa only [sub_eq_add_neg, abs_neg, abs_of_pos hl] using abs_add_le Z (-l)
  have hz : |z| ≤ 1 / 32 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1 - l by linarith)).mp
    linarith only [habs, hZ₁, hL]
  refine ⟨hz, ?_⟩
  have hsum := g3DividedJensen_right_sum (z := z) (n := 1) hl (by decide)
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, zero_add, one_mul, div_one] at hsum
  rw [show z + l * (1 - z) = Z by linarith only [hlin]] at hsum
  have hzu : |z| ^ criticalQ ≤ 1 / 32 := by
    calc
      _ ≤ (1 / 32 : ℝ) ^ criticalQ := Real.rpow_le_rpow (abs_nonneg z) hz (by linarith [q19])
      _ ≤ (1 / 32 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) criticalQ_one
      _ = _ := Real.rpow_one _
  have hqp : 1 < criticalQ := by linarith [q19]
  have hpower : |Z| ^ (criticalQ - 1) ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 64 : ℝ) ^ (criticalQ - 1) :=
        Real.rpow_le_rpow (abs_nonneg Z) (hZ₁.trans (by norm_num)) (by linarith [q19])
      _ ≤ (1 / 64 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [q19])
      _ = _ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num),
          show (64 : ℝ) = 8 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
        norm_num
  have hd : deriv (fun x : ℝ => |x| ^ criticalQ) Z ≤ 1 / 5 := by
    rw [(absPower_deriv hqp Z).deriv]
    split
    · have h := mul_le_mul criticalQ_hi hpower (Real.rpow_nonneg (abs_nonneg Z) _) (by norm_num)
      linarith only [h]
    · have h := mul_nonneg (show 0 ≤ criticalQ by linarith [q19])
        (Real.rpow_nonneg (abs_nonneg Z) (criticalQ - 1))
      linarith only [h]
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1 - z by linarith [(abs_le.mp hz).2])
  linarith only [hsum, hzu, hh, (abs_le.mp hz).1]

private structure EdgeBounds (l μ w : ℝ) : Prop where
  weight : 0 < μ ∧ μ ≤ 47/1000
  threshold : 0 < w ∧ w ≤ 1/90
  depthRatio : l/μ ≤ 1/180
  slope : μ * (criticalQ / 2 * w^(criticalQ-2)) ≤ 1/4
  intercept : (1-criticalQ/2)*w^criticalQ ≤ (7/10)*l

private theorem edge_compact_unit {l μ w e s z : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4000)
    (bounds : EdgeBounds l μ w)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1 / 2) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ balancedFacetGap criticalQ μ l e 1 s z := by
  let α := criticalQ / 2 * w ^ (criticalQ - 2)
  let β := (1 - criticalQ / 2) * w ^ criticalQ
  let Z := balancedFarCenter l l 1 z
  obtain ⟨hμ, hμ₁⟩ := bounds.weight
  have hw := bounds.threshold.1
  have hL₁ : l ≤ 1 := hL.trans (by norm_num)
  have hα : (criticalQ / 2) * (w ^ criticalQ / w ^ (2 : ℕ)) ≤ α := by
    rw [← Real.rpow_two, ← Real.rpow_sub hw]
  have hClose : |Z| ≤ w → (8 / 5) * l ^ 2 / μ * (z - 1) ^ 2 + β + α * Z ^ 2 + l/25 ≤
      l + (1 - l) * |z| ^ criticalQ := by
    intro hZ
    obtain ⟨hz', hJ⟩ := edge_near_center hl hL (hZ.trans bounds.threshold.2)
    have hb := (le_div_iff₀ hl).mp hJ
    simp only [balancedJensenGap, abs_one, Real.one_rpow, mul_one] at hb
    change _ ≤ (1 - l) * |z| ^ criticalQ + l - |Z| ^ criticalQ at hb
    have hαZ : α * Z ^ 2 ≤ |Z| ^ criticalQ := by
      by_cases hZ₀ : Z = 0
      · simp [hZ₀, Real.zero_rpow (ne_of_gt (by linarith [q19] : 0 < criticalQ))]
      have hZa := abs_pos.mpr hZ₀
      have hW := Real.rpow_le_rpow_of_nonpos hZa hZ (by linarith [criticalQ_hi] : criticalQ - 2 ≤ 0)
      have hcoef : α ≤ |Z| ^ (criticalQ - 2) :=
        mul_le_of_le_one_left (Real.rpow_nonneg hw.le _) (by linarith [criticalQ_hi]) |>.trans hW
      rw [← sq_abs Z, ← Real.rpow_two]
      calc
        _ ≤ |Z| ^ (criticalQ - 2) * |Z| ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hZa.le _)
        _ = _ := by rw [← Real.rpow_add hZa, sub_add_cancel]
    have hzabs : |z - 1| ≤ 33 / 32 := by
      have hab := abs_add_le z (-1)
      rw [← sub_eq_add_neg, abs_neg, abs_one] at hab
      linarith only [hab, hz']
    have hsq : (z - 1) ^ 2 ≤ (33 / 32 : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (z - 1)) hzabs 2
    have hc := mul_le_mul bounds.depthRatio hsq (sq_nonneg _) (by norm_num)
    have hcost := mul_le_mul_of_nonneg_left hc (show 0 ≤ (8 / 5 : ℝ) * l by positivity)
    have heq : (8 / 5) * l ^ 2 / μ * (z - 1) ^ 2 = (8 / 5) * l * (l / μ * (z - 1) ^ 2) := by ring
    change (8 / 5) * l * (l / μ * (z - 1) ^ 2) ≤ _ at hcost
    rw [heq]
    have hβ : β ≤ (7 / 10) * l := bounds.intercept
    linarith only [hb, hαZ, hcost, hβ, hl]
  refine compact_gap_of_certificates (C := 1 / 4) (k := 8 / 5)
    hμ hl.le hL₁ (by norm_num : (0 : ℝ) ≤ 1) hw hz hα le_rfl
    ?_ ?_ (fun hZ => (le_add_of_nonneg_right (show 0 ≤ l/25 by positivity)).trans (hClose hZ)) ?_
  · simpa only [mul_one] using bounds.slope
  · have h := mul_le_mul_of_nonneg_left bounds.depthRatio (by norm_num : (0 : ℝ) ≤ 8 / 5)
    rw [← mul_div_assoc] at h
    have h' := mul_le_mul edge_curvature (show (1 : ℝ) - 1 / 4000 ≤ 1 - l by linarith)
      (by norm_num) (by linarith [edge_curvature])
    have h'' := mul_le_mul_of_nonneg_right h' (by norm_num : (0 : ℝ) ≤ 27 / 64)
    linarith only [h, h'']
  · have hR : (1/2 : ℝ) + 9*l ≤ 1 := by linarith
    have hT : g1Curvature + (1 / 2 - g1Curvature) * ((1 / 2 : ℝ) + 9 * l) ^ 2 ≤ 1 / 2 := by
      have hh := pow_le_pow_left₀ (show 0 ≤ (1 / 2 : ℝ) + 9 * l by positivity) hR 2
      have h := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr g1Curvature_le_half)
      linarith only [h]
    let a := (1 - μ * (1 - l)) * g1Curvature - (1 - μ) * (1 / 2) * (1 / 2 : ℝ)^2 - 1 / 4
    have ha : 1 / 16 ≤ a := by
      have hM := mul_nonneg hμ.le hl.le
      change 0 ≤ μ * l at hM
      have hB : 0 ≤ 1 - μ := by linarith only [hμ₁]
      have hC := mul_le_mul_of_nonneg_left edge_curvature hB
      have hL := mul_nonneg hM (show 0 ≤ g1Curvature by linarith [edge_curvature])
      dsimp only [a]
      change μ ≤ 47/1000 at hμ₁
      linarith only [hC, hL, hμ₁]
    have ha₀ : 0 < a := (by norm_num : (0 : ℝ) < 1 / 16).trans_le ha
    have hm₀ : 0 ≤ (1 - μ) * (1/2) * (1/2) := by
      change μ ≤ 47/1000 at hμ₁
      linarith only [hμ₁]
    have hm₁ : (1 - μ) * (1/2) * (1/2) ≤ 1 / 4 := by linarith only [hμ.le]
    have hk : (1 - μ) * (1/2) + ((1 - μ) * (1/2) * (1/2)) ^ 2 / a ≤ 8/5 := by
      have hsq := pow_le_pow_left₀ hm₀ hm₁ 2
      have hd : ((1 - μ) * (1/2) * (1/2)) ^ 2 / a ≤ 1 := (div_le_one₀ ha₀).2 (by
        linarith only [ha, hsq])
      linarith only [hd, hμ.le]
    exact compact_compensated_lower hμ.le (hμ₁.trans (by norm_num)) hl.le hL₁ he₀ he₁ he₁
      (by linarith only [sq_nonneg e]) hR hs hz hT ha₀ hk

private theorem facetGap_of_edge_bounds {l μ w e : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4000)
    (bounds : EdgeBounds l μ w) (drift : ((1-μ)/(2*μ*l))*(2*l)^criticalQ ≤ 14/25)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1 / 2) (p s z : ℝ) :
    0 ≤ balancedFacetGap criticalQ μ l e p s z := by
  obtain ⟨hm, hmU⟩ := bounds.weight
  have hLen : l ≤ 74 / 4096 := hL.trans (by norm_num)
  have hmU' : μ ≤ 204 / 1000 := hmU.trans (by norm_num)
  have hfar {p s z : ℝ} (h : 8 * |p| ≤ |z|) :
      0 ≤ balancedFacetGap criticalQ μ l e p s z := by
    have hbound := g1_far_gap_of_drift (s := s) hm hmU' hl hLen drift he₀ he₁ h
    exact (mul_nonneg (mul_nonneg (div_nonneg hm.le (by norm_num)) hl.le)
      (Real.rpow_nonneg (abs_nonneg z) _)).trans hbound
  apply balancedFacetGap_nonneg_of_charts (zero_lt_one.trans_le criticalQ_one) _ _ _ p s z
  · intro a b ha _
    apply hfar
    simpa [abs_one] using (show 8 * |a| ≤ 1 by linarith)
  · exact fun a b => edge_compact_unit hl hL bounds he₀ he₁ (s := a) (z := b)
  · intro a b ha hb
    rcases le_total (8 * |a|) |b| with h | h
    · exact hfar h
    · have ha' : |a| ≤ |(1 : ℝ)| := by simpa only [abs_one] using ha
      have hbound := g1_large_gap hm.le hmU' hl.le hLen he₀ he₁ h ha'
      exact (mul_nonneg (by norm_num) (Real.rpow_nonneg (abs_nonneg 1) _)).trans hbound

/-- Every normalized chart is controlled by the same depth-dependent balanced weight. -/
theorem g1Edge_facetGap {l e : ℝ} (hl : 0 < l) (hL : l ≤ 1 / 4096)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1 / 2) (p s z : ℝ) :
    0 ≤ balancedFacetGap criticalQ (g1EdgeWeight l) l e p s z :=
  facetGap_of_edge_bounds hl (hL.trans (by norm_num))
    ⟨g1EdgeWeight_bounds hl hL, edgeThreshold_bounds hl hL, edge_depth_ratio hl hL,
      edge_alpha hl hL, edge_beta hl hL⟩ (edge_far_drift hl hL) he₀ he₁ p s z

theorem rowAt_g1Edge {t : Profile} (ht : IsSimplex t) (hl : 0 < t 2 + t 3)
    (hL : t 2 + t 3 ≤ 1 / 4096) (he₀ : 0 ≤ t 0 - t 1) (he₁ : t 0 - t 1 ≤ 1 / 2) :
    RowAt criticalQ t := by
  obtain ⟨hμ, hμ₁⟩ := g1EdgeWeight_bounds hl hL
  exact rowAt_of_balancedFacetGap criticalQ_one ht hμ.le (hμ₁.trans (by norm_num))
    (g1Edge_facetGap hl hL he₀ he₁)

/-- Keep the join weight constant on the short overlap, using the same scalar estimates. -/
theorem rowAt_g1Edge_overlap {t : Profile} (ht : IsSimplex t)
    (hl : 1/4096 ≤ t 2+t 3) (hL : t 2+t 3 ≤ 1/4000)
    (he₀ : 0 ≤ t 0-t 1) (he₁ : t 0-t 1 ≤ 1/2) : RowAt criticalQ t := by
  let l := t 2+t 3
  have hl₀ : 0 < l := (by norm_num : (0:ℝ) < 1/4096).trans_le hl
  have hb := edge_beta (l := 1/4096) (by norm_num) le_rfl
  have ha := edge_alpha (l := 1/4096) (by norm_num) le_rfl
  norm_num only [edgeThreshold, g1EdgeWeight, show (4096:ℝ)*(1/4096)=1 by norm_num,
    Real.one_rpow, mul_one] at ha hb
  have bounds : EdgeBounds l (47/1000) (1/90) :=
    ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩,
      (div_le_iff₀ (by norm_num)).2 (by dsimp only [l]; linarith only [hL]), ha,
      by dsimp only [l]; linarith only [hb, hl]⟩
  have hright : l ≤ g1SlabRight 0 := hL.trans (by norm_num [g1SlabRight, g1LengthNumerator])
  have hd := drift_scale_bound 0 hl₀ hright
  rw [show g1SlabWeight 0 = 47/1000 by norm_num [g1SlabWeight, g1WeightNumerator]] at hd
  apply rowAt_of_balancedFacetGap (μ := 47/1000) criticalQ_one ht (by norm_num) (by norm_num)
  exact facetGap_of_edge_bounds hl₀ hL bounds hd he₀ he₁

end

end HlawkaSchatten.BelowExponent
