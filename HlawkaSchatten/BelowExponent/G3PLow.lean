/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3
public import HlawkaSchatten.BelowExponent.G3PFar
public import HlawkaSchatten.BelowExponent.G3PJensen
import all HlawkaSchatten.BelowExponent.G1
import all HlawkaSchatten.BelowExponent.G1Far
import all HlawkaSchatten.BelowExponent.G1Large
import all HlawkaSchatten.BelowExponent.G1Compact

/-! An analytic p = 1 certificate at all positive sigma up to 7/10000. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set
open private evenGap_convex from HlawkaSchatten.BelowExponent.G1
open private criticalQ_lo criticalQ_hi criticalQ_one from HlawkaSchatten.BelowExponent.G1Far
open private absPower_deriv from HlawkaSchatten.BelowExponent.G1Large
open private g1Curvature g1Curvature_le_half g1_evenGap_abs_bounds compact_jensen_lower
  eight_critical_pred variance_tangent from HlawkaSchatten.BelowExponent.G1Compact

noncomputable section

private theorem q19 : (19 : ℝ) / 12 ≤ criticalQ :=
  (by norm_num : (19 : ℝ) / 12 ≤ 1054 / 665).trans criticalQ_lo

private theorem C_lower : 23 / 50 ≤ g1Curvature := by
  have hb : (19 / 12 : ℝ) * (7 / 12) ≤ criticalQ * (criticalQ - 1) :=
    mul_le_mul q19 (by linarith [q19]) (by norm_num) (by linarith [q19])
  unfold g1Curvature
  linarith only [hb]

private def lowThreshold (σ : ℝ) : ℝ := 6 * σ ^ (11 / 10 : ℝ)

private theorem lowWeight (h σ : ℝ) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hσ : 0 < σ) (hcap : σ ≤ 7 / 10000) :
    0 < g3Weight h σ ∧ g3Weight h σ ≤ (51/80) * σ^(12/25:ℝ) ∧ g3Weight h σ ≤ 1/50 := by
  have hw : g3Weight h σ = (3/5)*(1+h/16)*σ^(12/25:ℝ) := by
    simp [g3Weight, show σ < 3/20 by linarith]
  have hx : 0 < σ^(12/25:ℝ) := Real.rpow_pos_of_pos hσ _
  have hU : g3Weight h σ ≤ (51/80) * σ^(12/25:ℝ) := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right (by linarith) hx.le
  have hp : (7 / 10000 : ℝ) ^ (12 / 25 : ℝ) ≤ 8 / 255 := by
    simpa only [Nat.cast_ofNat] using
      (natRat_rpow_le_iff (a := 7) (c := 8) (m := 12) (n := 25)
        (by decide : 0 < (10000 : ℕ)) (by decide : 0 < (255 : ℕ)) (by decide)).2 (by decide)
  have hb := (Real.rpow_le_rpow hσ.le hcap (by norm_num : (0 : ℝ) ≤ 12/25)).trans hp
  refine ⟨by rw [hw]; positivity, hU, hU.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 51/80)
  linarith only [hh]

private theorem lowRatio {h σ : ℝ} (hh : 0 ≤ h) (hσ : 0 < σ) (hcap : σ ≤ 7 / 10000) :
    (σ / (2 - σ)) / (2 * g3Weight h σ) ≤ 1 / 80 := by
  let k := σ / (2 - σ)
  let μ := g3Weight h σ
  have hden : 0 < 2 - σ := by linarith
  have hw : μ = (3/5)*(1+h/16)*σ^(12/25:ℝ) := by
    simp [μ, g3Weight, show σ < 3/20 by linarith]
  have hx : 0 < σ^(12/25:ℝ) := Real.rpow_pos_of_pos hσ _
  have hM : (3/5) * σ^(12/25:ℝ) ≤ μ := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right (by linarith) hx.le
  have hp : (7 / 10000 : ℝ) ^ (13 / 25 : ℝ) ≤ 1 / 40 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (natRat_rpow_le_iff (a := 7) (c := 1) (m := 13) (n := 25)
        (by decide : 0 < (10000 : ℕ)) (by decide : 0 < (40 : ℕ)) (by decide)).2 (by decide)
  have hp' := (Real.rpow_le_rpow hσ.le hcap (by norm_num : (0 : ℝ) ≤ 13/25)).trans hp
  have heq : σ^(12/25:ℝ) * σ^(13/25:ℝ) = σ := by
    rw [← Real.rpow_add hσ, show (12/25:ℝ) + 13/25 = 1 by norm_num, Real.rpow_one]
  have hl := mul_le_mul_of_nonneg_left hp' hx.le
  rw [heq] at hl
  have hk : k ≤ (3/200) * σ^(12/25:ℝ) := by
    apply (div_le_iff₀ hden).2
    have hb := mul_le_mul_of_nonneg_right (show (5/3:ℝ) ≤ 2-σ by linarith)
      (show 0 ≤ (3/200:ℝ) * σ^(12/25:ℝ) by positivity)
    linarith only [hl,hb]
  change k / (2 * μ) ≤ 1/80
  have hm : 0 < μ := lt_of_lt_of_le (by positivity) hM
  apply (div_le_iff₀ (mul_pos (by norm_num) hm)).2
  linarith only [hk, hM]

private theorem lowAlpha {h σ : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hσ : 0 < σ) (hcap : σ ≤ 7 / 10000) :
    g3Weight h σ * (criticalQ * (lowThreshold σ)^(criticalQ-2)) ≤ 9/20 := by
  have he₁ : (6 : ℝ) ^ (criticalQ - 2) ≤ 49/100 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) (show criticalQ - 2 ≤ -(2/5) by linarith [criticalQ_hi])).trans ?_
    rw [show (6 : ℝ)^(-(2/5):ℝ) = (1/6:ℝ)^(2/5:ℝ) by
      rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, one_div]]
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (natRat_rpow_le_iff (a := 1) (c := 49) (m := 2) (n := 5)
        (by decide : 0 < (6 : ℕ)) (by decide : 0 < (100 : ℕ)) (by decide)).2 (by decide)
  have he₂ : σ ^ ((12/25:ℝ) + (11/10) * (criticalQ - 2)) ≤ 9/10 := by
    refine (Real.rpow_le_rpow_of_exponent_ge hσ (by linarith)
      (show (1/50:ℝ) ≤ 12/25 + (11/10)*(criticalQ-2) by linarith [q19])).trans ?_
    refine (Real.rpow_le_rpow hσ.le hcap (by norm_num : (0:ℝ) ≤ 1/50)).trans ?_
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (natRat_rpow_le_iff (a := 7) (c := 9) (m := 1) (n := 50)
        (by decide : 0 < (10000 : ℕ)) (by decide : 0 < (10 : ℕ)) (by decide)).2 (by decide)
  have h := mul_le_mul_of_nonneg_right (lowWeight h σ hh hh₁ hσ hcap).2.1
    (show 0 ≤ criticalQ * (lowThreshold σ)^(criticalQ-2) by
      exact mul_nonneg (by linarith [q19]) (Real.rpow_nonneg (by unfold lowThreshold; positivity) _))
  unfold lowThreshold at h
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hσ.le _), ← Real.rpow_mul hσ.le] at h
  have hfactor : (51/80:ℝ) * σ^(12/25:ℝ) *
      (criticalQ * ((6:ℝ)^(criticalQ-2) * σ^((11/10:ℝ)*(criticalQ-2)))) =
      (51/80) * (criticalQ * (6:ℝ)^(criticalQ-2)) *
        σ^((12/25:ℝ) + (11/10)*(criticalQ-2)) := by
    rw [Real.rpow_add hσ]
    ring
  rw [hfactor] at h
  unfold lowThreshold
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hσ.le _), ← Real.rpow_mul hσ.le]
  refine h.trans ?_
  have hbase := mul_le_mul criticalQ_hi he₁ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hbase (by norm_num : (0:ℝ) ≤ 51/80))
    he₂ (Real.rpow_nonneg hσ.le _) (by norm_num)
  linarith only [hh']

private theorem lowBeta {σ : ℝ} (hσ : 0 < σ) (hcap : σ ≤ 7 / 10000) :
    2 * (1 - criticalQ / 2) * (lowThreshold σ)^criticalQ ≤ (3/40) * (σ / (2-σ)) := by
  have hp : (6:ℝ)^criticalQ ≤ 18 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) criticalQ_hi).trans ?_
    simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using
      (natRat_rpow_le_iff (a := 6) (c := 18) (m := 8) (n := 5)
        (by decide : 0 < (1 : ℕ)) (by decide : 0 < (1 : ℕ)) (by decide)).2 (by decide)
  have hp' : σ^((11/10:ℝ)*criticalQ-1) ≤ 1/200 := by
    refine (Real.rpow_le_rpow_of_exponent_ge hσ (by linarith)
      (show (89/120:ℝ) ≤ (11/10)*criticalQ-1 by linarith [q19])).trans ?_
    refine (Real.rpow_le_rpow hσ.le hcap (by norm_num : (0:ℝ) ≤ 89/120)).trans ?_
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (natRat_rpow_le_iff (a := 7) (c := 1) (m := 89) (n := 120)
        (by decide : 0 < (10000 : ℕ)) (by decide : 0 < (200 : ℕ)) (by decide)).2 (by decide)
  have hp'' := mul_le_mul_of_nonneg_left hp' hσ.le
  rw [mul_comm σ, ← Real.rpow_add_one hσ.ne', sub_add_cancel] at hp''
  have hconst : (2 * (1 - criticalQ / 2)) * (6:ℝ)^criticalQ ≤ (5/12) * 18 :=
    mul_le_mul (by linarith [q19]) hp (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  unfold lowThreshold
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hσ.le _), ← Real.rpow_mul hσ.le, ← mul_assoc]
  have hbound := mul_le_mul hconst hp'' (Real.rpow_nonneg hσ.le _) (by norm_num)
  have hk : σ / 2 ≤ σ / (2-σ) :=
    div_le_div_of_nonneg_left hσ.le (by linarith) (by linarith)
  linarith only [hbound, hk]

private theorem lowJensen_inner {l z : ℝ} (hl : 0 < l) (hl₁ : l ≤ 1 / 2048) (hz : |z| ≤ 1 / 8) :
    (3 / 20 : ℝ) ≤ g3DividedJensen l z := by
  let Z := balancedFarCenter l l 1 z
  have hl' : l ≤ 1 := by linarith
  have hZ : |Z| ≤ 1 / 7 := by
    have h := abs_add_le ((1-l)*z) l
    simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr hl'), abs_of_pos hl] at h
    have h' := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hl')
    rw [show Z = (1-l)*z+l by simp [Z, balancedFarCenter]]
    linarith only [h, h', hl₁]
  have hzP : |z| ^ criticalQ ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 8 : ℝ) ^ criticalQ := Real.rpow_le_rpow (abs_nonneg z) hz (by linarith [q19])
      _ ≤ (1 / 8 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) criticalQ_one
      _ = _ := Real.rpow_one _
  have hPow : |Z| ^ (criticalQ - 1) ≤ 2 / 5 := by
    refine (Real.rpow_le_rpow (abs_nonneg Z) hZ (by linarith [q19])).trans ?_
    refine (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show (1/2:ℝ) ≤ criticalQ - 1 by linarith [q19])).trans ?_
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (natRat_rpow_le_iff (a := 1) (c := 2) (m := 1) (n := 2)
        (by decide : 0 < (7 : ℕ)) (by decide : 0 < (5 : ℕ)) (by decide)).2 (by decide)
  have hD : deriv (fun x : ℝ => |x|^criticalQ) Z ≤ 16/25 := by
    rw [(absPower_deriv (by linarith [q19] : 1 < criticalQ) Z).deriv]
    split
    · have hd := mul_le_mul criticalQ_hi hPow (Real.rpow_nonneg (abs_nonneg Z) _) (by norm_num)
      linarith only [hd]
    · have hd := mul_nonneg (show 0 ≤ criticalQ by linarith [q19])
        (Real.rpow_nonneg (abs_nonneg Z) (criticalQ - 1))
      linarith only [hd]
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ 1 - z by linarith [(abs_le.mp hz).2])
  have hJ := g3DividedJensen_right_endpoint (z := z) hl
  change 1 - |z|^criticalQ - (1-z)*deriv (fun x : ℝ => |x| ^ criticalQ) Z ≤ _ at hJ
  linarith only [hJ, hzP, hh, (abs_le.mp hz).1]

private theorem lowJensen_outer {l z : ℝ} (hl : 0 < l) (hl₁ : l ≤ 1 / 2048) (hz : |z| ≤ 8) :
    (3 / 20) * (z - 1) ^ 2 ≤ g3DividedJensen l z := by
  have hJ := compact_jensen_lower hl.le (show l ≤ 1 by linarith) hz
  rw [eight_critical_pred] at hJ
  have hcoef : (3 / 20 : ℝ) ≤ g1Curvature * (27/64) * (1-l) := by
    have ht := mul_le_mul C_lower (show (1 : ℝ) - 1/2048 ≤ 1-l by linarith)
      (by norm_num) (by linarith [C_lower])
    have h := mul_le_mul_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 27/64)
    linarith only [h]
  apply (le_div_iff₀ hl).2
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (z-1))
  have h := mul_le_mul_of_nonneg_right hh hl.le
  linarith only [hJ, h]

private theorem lowNear {h w s : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hw : |w| ≤ 1) (hs : |s| ≤ 1) :
    g1Curvature * s^2 - w^2/2 ≤
      (balancedEvenGap criticalQ 1 s - balancedEvenGap criticalQ 1 ((1-h)*s+h*w))/h := by
  let A := balancedEvenGap criticalQ 1
  have hc : A ((1-h)*s+h*w) ≤ (1-h)*A s+h*A w :=
    (evenGap_convex criticalQ_one 1).2 (mem_univ s) (mem_univ w)
      (sub_nonneg.mpr hh₁) hh.le (sub_add_cancel 1 h)
  have hA : g1Curvature * s^2 ≤ A s := (g1_evenGap_abs_bounds hs).1
  have hW : A w ≤ w^2/2 := by
    have hu := (g1_evenGap_abs_bounds hw).2
    have hw₂ : w^2 ≤ 1 := by simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg w) hw 2
    have h4 : w^4 ≤ w^2 := by
      have hc := mul_le_mul_of_nonneg_right hw₂ (sq_nonneg w)
      linarith only [hc, show w^4 = w^2*w^2 by ring]
    have he := mul_le_mul_of_nonneg_left h4 (sub_nonneg.mpr g1Curvature_le_half)
    change A w ≤ _ at hu
    linarith only [hu, he]
  have hd : g1Curvature * s^2 - w^2/2 ≤ A s - A w := sub_le_sub hA hW
  refine hd.trans ((le_div_iff₀ hh).2 ?_)
  change (A s - A w) * h ≤ A s - A ((1-h)*s+h*w)
  linarith only [hc]

/-- The p = 1 G3 chart in the vertex-edge junction, with no lower cutoff on sigma or h. -/
theorem g3_p_low_chart_gap {h σ s z : ℝ} (hh : 0 < h) (hσ : 0 < σ) (hcap : σ ≤ 7/10000)
    (hh₁ : h ≤ 1/(2-σ/(2-σ))) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  let k := σ/(2-σ)
  let l := h*k
  let μ := g3Weight h σ
  let w := k*(z-1)
  let Z := balancedFarCenter l l 1 z
  let J := g3DividedJensen l z
  let H := balancedFarIncrement criticalQ (1-h) Z s / h
  let A := balancedEvenGap criticalQ 1
  have hh' : h ≤ 1 := (g3_h_max (hcap.trans (by norm_num)) hh₁).trans (by norm_num)
  have hk : 0 < k := div_pos hσ (by linarith)
  have hk₁ : k ≤ 1/2048 := (div_le_iff₀ (show 0 < 2-σ by linarith)).2 (by linarith)
  have hl : 0 < l := mul_pos hh hk
  have hl₁ : l ≤ 1/2048 := (mul_le_of_le_one_left hk.le hh').trans hk₁
  have hμ := lowWeight h σ hh.le hh' hσ hcap
  have hμ₀ : 0 < μ := hμ.1
  have hμ₁ : μ ≤ 1/50 := hμ.2.2
  have hb : 0 ≤ 1-μ := by linarith
  have hzs : |z-1| ≤ 9 := by
    have h := abs_add_le z (-1)
    rw [← sub_eq_add_neg, abs_neg, abs_one] at h
    linarith
  have hw : |w| ≤ 1 := by
    rw [show w = k*(z-1) by rfl, abs_mul, abs_of_nonneg hk.le]
    exact (mul_le_mul hk₁ hzs (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hNear := mul_le_mul_of_nonneg_left (lowNear hh hh' hw hs) hb
  have hC : (9/20:ℝ) ≤ (1-μ)*g1Curvature := by
    have h := mul_le_mul (show (49/50:ℝ) ≤ 1-μ by linarith) C_lower
      (by norm_num) hb
    linarith only [h]
  have hS := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  have hW := mul_le_mul_of_nonneg_right (show 1-μ ≤ 1 by linarith) (sq_nonneg w)
  have hA := (g1_evenGap_abs_bounds hs).1
  have hA₀ : 0 ≤ A s := (mul_nonneg (by linarith [C_lower]) (sq_nonneg s)).trans hA
  have hg : μ*k*J + (9/20)*s^2 - w^2/2 - μ*H ≤ g3FacetGap h σ 1 s z / h := by
    have hfold : balancedNearShift l (1-h) l 1 s z = (1-h)*s+h*w := by
      rw [balancedNearShift_facet]
      dsimp only [l,w]
      ring
    show _ ≤ balancedFacetGap criticalQ μ (h*k) (1-h) 1 s z / h
    rw [balancedFacetGap_div_h criticalQ μ h k 1 s z hh.ne' hk.ne', ← show l = h*k by rfl, hfold]
    have hJ : 0 ≤ μ*k*A s := mul_nonneg (mul_nonneg hμ₀.le hk.le) hA₀
    change (1-μ)*(g1Curvature * s^2 - w^2/2) ≤
      (1-μ)*((A s - A ((1-h)*s+h*w))/h) at hNear
    rw [mul_div_assoc, mul_div_assoc]
    change _ ≤ μ*k*(J + A s) + (1-μ)*((A s-A ((1-h)*s+h*w))/h)-μ*H
    linarith only [hNear, hJ, hS, hW]
  have hRatio : k / (2*μ) ≤ 1/80 := lowRatio hh.le hσ hcap
  have hCosts : w^2/2 ≤ μ*k*((z-1)^2/80) := by
    have h := (div_le_iff₀ (mul_pos (by norm_num) hμ₀)).mp hRatio
    have hp := mul_le_mul_of_nonneg_right h (mul_nonneg hk.le (sq_nonneg (z-1)))
    unfold w
    nlinarith only [hp]
  suffices hg' : 0 ≤ g3FacetGap h σ 1 s z / h by
    simpa only [zero_mul] using (le_div_iff₀ hh).mp hg'
  refine le_trans ?_ hg
  by_cases hzsmall : |z| ≤ 1/8
  · have hJ : (3/20:ℝ) ≤ J := lowJensen_inner hl hl₁ hzsmall
    let a := lowThreshold σ
    have ha : 0 < a := mul_pos (by norm_num) (Real.rpow_pos_of_pos hσ _)
    have hP : (s^2)^(criticalQ/2) = |s|^criticalQ := by
      rw [← sq_abs s, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg s), show 2*(criticalQ/2)=criticalQ by ring]
    have htan := variance_tangent ha (sq_nonneg s)
    have hratio : a^criticalQ / a^(2:ℕ) = a^(criticalQ-2) := by
      rw [← Real.rpow_two, ← Real.rpow_sub ha]
    rw [hratio,hP] at htan
    have hFar : H ≤ 2 * (1-criticalQ/2) * a^criticalQ + criticalQ*a^(criticalQ-2)*s^2 := by
      have hf : H ≤ 2*|s|^criticalQ := g3FarIncrement_div_le_power hh
      linarith only [hf, htan]
    have hB : 2*(1-criticalQ/2)*a^criticalQ ≤ (3/40)*k := lowBeta hσ hcap
    have halpha : μ*(criticalQ*a^(criticalQ-2)) ≤ 9/20 := lowAlpha hh.le hh' hσ hcap
    have hf : H ≤ (3/40)*k + criticalQ*a^(criticalQ-2)*s^2 := by linarith only [hFar, hB]
    have hc := mul_le_mul_of_nonneg_left hf hμ₀.le
    have hd := mul_le_mul_of_nonneg_right halpha (sq_nonneg s)
    have hZ' : |z-1| ≤ 9/8 := by
      have ht := abs_add_le z (-1)
      rw [← sub_eq_add_neg, abs_neg, abs_one] at ht
      linarith only [ht,hzsmall]
    have hZ₂ : (z-1)^2 ≤ 2 := by
      have ht := pow_le_pow_left₀ (abs_nonneg (z-1)) hZ' 2
      rw [sq_abs] at ht
      linarith only [ht]
    have hu := mul_le_mul_of_nonneg_left hZ₂ (show 0 ≤ μ*k/80 by positivity)
    have hj := mul_le_mul_of_nonneg_left hJ (mul_nonneg hμ₀.le hk.le)
    have hmargin : μ*k/20 ≤ μ*k*J + (9/20)*s^2 - w^2/2 - μ*H := by
      linarith only [hc, hd, hu, hj, hCosts]
    exact (div_nonneg (mul_nonneg hμ₀.le hk.le) (by norm_num)).trans hmargin
  · have hZ : (1/10:ℝ) ≤ |Z| := by
      have hlin : (1-l)*z = Z-l := by dsimp [Z, balancedFarCenter]; ring
      have habs : (1-l)*|z| ≤ |Z|+l := by
        rw [← abs_of_nonneg (show 0 ≤ 1-l by linarith), ← abs_mul, hlin]
        simpa only [sub_eq_add_neg, abs_neg, abs_of_pos hl] using abs_add_le Z (-l)
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge hzsmall) (show 0 ≤ 1-l by linarith)
      linarith only [h, habs, hl₁]
    have hZ₀ : 0 < |Z| := (by norm_num : (0:ℝ)<1/10).trans_le hZ
    have hpow : |Z|^(criticalQ-2) ≤ 3 := by
      refine (Real.rpow_le_rpow_of_nonpos (by norm_num) hZ (by linarith [criticalQ_hi])).trans ?_
      refine (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (show -(5/12:ℝ) ≤ criticalQ-2 by linarith [q19])).trans ?_
      rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
        one_div, inv_inv]
      simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using
        (natRat_rpow_le_iff (a := 10) (c := 3) (m := 5) (n := 12)
          (by decide : 0 < (1 : ℕ)) (by decide : 0 < (1 : ℕ)) (by decide)).2 (by decide)
    have hFar : H ≤ (24/5) * s^2 := by
      have hf := g3FarIncrement_div_le_quadratic (s := s) hh hh' (abs_pos.mp hZ₀)
      have hc := mul_le_mul (show criticalQ/2 ≤ 4/5 by linarith [criticalQ_hi])
        (show 2-h ≤ 2 by linarith) (show 0 ≤ 2-h by linarith) (by norm_num)
      have hd := mul_le_mul hc hpow (Real.rpow_nonneg hZ₀.le _) (by norm_num)
      exact hf.trans (mul_le_mul_of_nonneg_right (hd.trans_eq (by norm_num)) (sq_nonneg s))
    have hH := mul_le_mul_of_nonneg_left hFar hμ₀.le
    have hhμ := mul_le_mul_of_nonneg_right hμ₁ (sq_nonneg s)
    have hJ : (3/20)*(z-1)^2 ≤ J := lowJensen_outer hl hl₁ hz
    have hj := mul_le_mul_of_nonneg_left hJ (mul_nonneg hμ₀.le hk.le)
    have hzs₂ := mul_nonneg (mul_nonneg hμ₀.le hk.le) (sq_nonneg (z-1))
    linarith only [hH, hhμ, hj, hCosts, hzs₂, sq_nonneg s]

end

end HlawkaSchatten.BelowExponent
