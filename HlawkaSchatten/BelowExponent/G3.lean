/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Balanced
public import HlawkaSchatten.BelowExponent.Bulk
public import HlawkaSchatten.BelowExponent.Coverage

/-! Common weights and facet reduction for the written G3 vertex corner. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- The single G3 weight used on all three normalized row charts.
At the shared breakpoint this takes the upper band's weight. -/
noncomputable def g3Weight (h σ : ℝ) : ℝ :=
  (if σ < 3/20 then 1 else 49/50) * (3/5) * (1+h/16) * σ^(12/25:ℝ)

noncomputable def g3FacetGap (h σ p s z : ℝ) : ℝ :=
  balancedFacetGap criticalQ (g3Weight h σ) (h*(σ/(2-σ))) (1-h) p s z

theorem g3_weight_pos_lt_third {h σ : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1)
    (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1/5) : 0 < g3Weight h σ ∧ g3Weight h σ < 1/3 := by
  let a : ℝ := if σ < 3/20 then 1 else 49/50
  have ha : 0 < a ∧ a ≤ 1 := by dsimp [a]; split <;> norm_num
  have hp₀ : 0 < σ ^ (12/25:ℝ) := Real.rpow_pos_of_pos hσ₀ _
  have hp₁ : σ ^ (12/25:ℝ) ≤ 1/2 := by
    have hexact : (1/5:ℝ)^(12/25:ℝ) ≤ 1/2 := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a := 1) (c := 1) (m := 12) (n := 25)
          (by decide : 0 < (5:ℕ)) (by decide : 0 < (2:ℕ)) (by decide)).mpr (by decide)
    exact (Real.rpow_le_rpow hσ₀.le hσ₁ (by norm_num)).trans hexact
  have hh : 0 < 1+h/16 := by linarith
  have hg : 1+h/16 ≤ (17/16:ℝ) := by linarith
  change 0 < a*(3/5)*(1+h/16)*σ^(12/25:ℝ) ∧ a*(3/5)*(1+h/16)*σ^(12/25:ℝ) < 1/3
  refine ⟨by positivity, ?_⟩
  exact (calc
    _ ≤ 1*(3/5)*(17/16)*(1/2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right ha.2 (by norm_num)) hg hh.le
        (by norm_num)) hp₁ hp₀.le (by norm_num)
    _ < (1/3:ℝ) := by norm_num)

private theorem g3_k_max {σ : ℝ} (hσ : σ ≤ 1/5) : σ/(2-σ) ≤ 1/9 := by
  apply (div_le_iff₀ (by linarith : 0 < 2-σ)).2
  linarith

theorem g3_h_max {σ h : ℝ} (hσ : σ ≤ 1/5) (hh : h ≤ 1/(2-σ/(2-σ))) : h ≤ 9/17 := by
  have hl : (17/9:ℝ) ≤ 2-σ/(2-σ) := by linarith only [g3_k_max hσ]
  exact hh.trans (by
    have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) < 17/9) hl
    norm_num at hd
    simpa only [one_div] using hd)

/-- The transverse coefficient in the G3 equality cone is positive for
the chosen weight on both sides of the breakpoint. -/
theorem g3_weight_cone_transverse {h σ : ℝ} (hh₀ : 0 ≤ h)
    (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1/5) :
    g3Weight h σ * (1-σ/(2-σ)+(4/3)*(2-h)) < 1 := by
  have hk₀ : 0 ≤ σ/(2-σ) := div_nonneg hσ₀.le (by linarith)
  have he : 0 ≤ 1+h/16 := by linarith
  have hFactor : (1+h/16)*(1-σ/(2-σ)+(4/3)*(2-h)) ≤ 11/3 := by
    calc
      _ ≤ (1+h/16)*(1+(4/3)*(2-h)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hk₀]) he
      _ ≤ _ := by nlinarith only [sq_nonneg h, hh₀]
  have hpow₀ : 0 ≤ σ^(12/25:ℝ) := Real.rpow_nonneg hσ₀.le _
  unfold g3Weight
  split
  · rename_i hBand
    have hb : (3/20:ℝ)^(12/25:ℝ) ≤ 9/20 := by
      simpa only [Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a := 3) (c := 9) (m := 12) (n := 25)
          (by decide : 0 < (20:ℕ)) (by decide : 0 < (20:ℕ)) (by decide)).mpr (by decide)
    have hc := (Real.rpow_le_rpow hσ₀.le hBand.le (by norm_num : 0 ≤ (12/25:ℝ))).trans hb
    calc
      _ = ((3/5)*σ^(12/25:ℝ)) * ((1+h/16)*(1-σ/(2-σ)+(4/3)*(2-h))) := by ring
      _ ≤ ((3/5)*σ^(12/25:ℝ))*(11/3) := mul_le_mul_of_nonneg_left hFactor (by positivity)
      _ ≤ ((3/5)*(9/20))*(11/3) := by gcongr
      _ < _ := by norm_num
  · have hb : (1/5:ℝ)^(12/25:ℝ) ≤ 37/80 := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a := 1) (c := 37) (m := 12) (n := 25)
          (by decide : 0 < (5:ℕ)) (by decide : 0 < (80:ℕ)) (by decide)).mpr (by decide)
    have hc := (Real.rpow_le_rpow hσ₀.le hσ₁ (by norm_num : 0 ≤ (12/25:ℝ))).trans hb
    calc
      _ = ((49/50)*(3/5)*σ^(12/25:ℝ)) * ((1+h/16)*(1-σ/(2-σ)+(4/3)*(2-h))) := by ring
      _ ≤ ((49/50)*(3/5)*σ^(12/25:ℝ))*(11/3) := mul_le_mul_of_nonneg_left hFactor (by positivity)
      _ ≤ ((49/50)*(3/5)*(37/80))*(11/3) := by gcongr
      _ < _ := by norm_num

/-- The second coefficient in the equality cone uses this ratio bound. -/
theorem g3_cornerK_div_weight {h σ : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1)
    (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1/5) : (σ/(2-σ))/g3Weight h σ < 1/2 := by
  let a : ℝ := if σ < 3/20 then 1 else 49/50
  have ha : (49/50:ℝ) ≤ a := by dsimp [a]; split <;> norm_num
  have hp := Real.rpow_pos_of_pos hσ₀ (12/25:ℝ)
  have hσpow : σ^(13/25:ℝ) ≤ 1/2 := by
    have hh : (1/5:ℝ)^(13/25:ℝ) ≤ 1/2 := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a := 1) (c := 1) (m := 13) (n := 25)
          (by decide : 0 < (5:ℕ)) (by decide : 0 < (2:ℕ)) (by decide)).mpr (by decide)
    exact (Real.rpow_le_rpow hσ₀.le hσ₁ (by norm_num)).trans hh
  have hstep : 1 < a*(3/5)*(1+h/16)*(2-σ) := calc
    _ < (49/50:ℝ)*(3/5)*1*(9/5) := by norm_num
    _ ≤ _ := by
      have ha₀ : 0 ≤ a := (by norm_num : (0:ℝ) ≤ 49/50).trans ha
      have ha₃ : 0 ≤ a*(3/5) := by positivity
      have hh : 1 ≤ 1+h/16 := by linarith
      have hl := mul_le_mul (mul_le_mul_of_nonneg_right ha (by norm_num : (0:ℝ) ≤ 3/5))
        hh zero_le_one ha₃
      exact mul_le_mul hl (by linarith) (by norm_num) (by positivity)
  have hfactor : σ^(12/25:ℝ) * σ^(13/25:ℝ) = σ := by
    rw [← Real.rpow_add hσ₀, show (12/25:ℝ)+13/25=1 by norm_num, Real.rpow_one]
  have hpos := (g3_weight_pos_lt_third hh₀ hh₁ hσ₀ hσ₁).1
  have hden : 0 < 2-σ := by linarith
  apply (div_lt_iff₀ hpos).2
  apply (div_lt_iff₀ hden).2
  have hlo := mul_le_mul_of_nonneg_left hσpow hp.le
  have hhi := mul_lt_mul_of_pos_right hstep (show 0 < σ^(12/25:ℝ)/2 by positivity)
  change σ < (1/2)*(a*(3/5)*(1+h/16)*σ^(12/25:ℝ))*(2-σ)
  rw [hfactor] at hlo
  linarith only [hlo, hhi]

/-- The three charts give a physical row at every positive corner ratio. -/
theorem rowAt_g3_of_positive_charts {t : Profile} (ht : OrderedInterior t)
    (hσ₀ : 0 < sigma t) (hσ₁ : sigma t ≤ 1/5)
    (hh₀ : 0 < cornerH t) (hh₁ : cornerH t ≤ 1/(2-cornerK t))
    (hHead : ∀ p s, |p| ≤ 1/8 → |s| ≤ 1/8 →
      0 ≤ g3FacetGap (cornerH t) (sigma t) p s 1)
    (hP : ∀ s z, |s| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) 1 s z)
    (hS : ∀ p z, |p| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) p 1 z) :
    RowAt criticalQ t := by
  have hh := g3_h_max hσ₁ hh₁
  have hweight := g3_weight_pos_lt_third hh₀.le (hh.trans (by norm_num)) hσ₀ hσ₁
  have hq : 1 ≤ criticalQ := (by norm_num : (1:ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le
  apply rowAt_of_balancedFacetGap (μ := g3Weight (cornerH t) (sigma t))
    hq ht.simplex hweight.1.le (hweight.2.le.trans (by norm_num))
  have he : 1-cornerH t = imbalance t := by unfold cornerH; ring
  have hlen := ht.depth_mul_ratio hσ₁
  change cornerH t * (sigma t/(2-sigma t)) = t 2+t 3 at hlen
  have hg : ∀ p s z, 0 ≤ g3FacetGap (cornerH t) (sigma t) p s z :=
    balancedFacetGap_nonneg_of_charts (zero_lt_one.trans_le hq) hHead hP hS
  intro p s z
  simpa only [g3FacetGap, he, hlen] using hg p s z

/-- The original G3 assembly on its written interval. -/
theorem rowAt_g3_of_charts {t : Profile} (ht : OrderedInterior t)
    (hσ₀ : 7/10000 ≤ sigma t) (hσ₁ : sigma t ≤ 1/5)
    (hh₀ : 0 < cornerH t) (hh₁ : cornerH t ≤ 1/(2-cornerK t))
    (hHead : ∀ p s, |p| ≤ 1/8 → |s| ≤ 1/8 →
      0 ≤ g3FacetGap (cornerH t) (sigma t) p s 1)
    (hP : ∀ s z, |s| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) 1 s z)
    (hS : ∀ p z, |p| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) p 1 z) :
    RowAt criticalQ t :=
  rowAt_g3_of_positive_charts ht (lt_of_lt_of_le (by norm_num) hσ₀) hσ₁ hh₀ hh₁ hHead hP hS

end HlawkaSchatten.BelowExponent
