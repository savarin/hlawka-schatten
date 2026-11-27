/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertBounds

/-! Transfer the rational polynomial coefficients to a central G3 row. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

noncomputable section

theorem q_mem : qBounds.Contains criticalQ := by
  exact ⟨by simpa [qBounds] using criticalQ_bracket.1.le,
    by simpa [qBounds] using criticalQ_bracket.2.le⟩

theorem c2_mem : c2.Contains g3NearC2 := by
  have h := RatBounds.mul_mem
    (RatBounds.mul_mem q_mem (RatBounds.sub_mem q_mem (point_has 1))) (point_has (1/2))
  have ee : criticalQ * (criticalQ - ((1 : ℚ) : ℝ)) * (((1/2 : ℚ) : ℝ)) =
      g3NearC2 := by norm_num [g3NearC2]; ring
  rwa [ee] at h

theorem c4_mem : c4.Contains g3NearC4 := by
  have h := RatBounds.mul_mem
    (RatBounds.mul_mem (RatBounds.mul_mem c2_mem (RatBounds.sub_mem q_mem (point_has 2)))
      (RatBounds.sub_mem q_mem (point_has 3))) (point_has (1/12))
  have ee : g3NearC2 * (criticalQ - ((2 : ℚ) : ℝ)) * (criticalQ - ((3 : ℚ) : ℝ)) *
      (((1/12 : ℚ) : ℝ)) = g3NearC4 := by
    unfold g3NearC4
    rw [Ring.choose_eq_smul]
    norm_num [g3NearC2, descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub]
    rw [show (2 : Polynomial ℤ) = ((2 : ℕ) : Polynomial ℤ) by rfl,
      Polynomial.smeval_natCast]
    norm_num [nsmul_eq_mul]
    ring
  rwa [ee] at h

theorem rem_mem : remScale.Contains (criticalQ * (7 / 4 - criticalQ)) := by
  simpa [remScale] using RatBounds.mul_mem q_mem (RatBounds.sub_mem (point_has (7/4)) q_mem)

theorem near_sound {B : Box} {w : RowWitness} (positive : Bool)
    {h σ u z F : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hu : 0 ≤ u) (hu₁ : u ≤ 1) (hz : |z| ≤ 8)
    (hH : (bounds B 0).Contains h) (hU : (bounds B 2).Contains u)
    (hZ : (bounds B 3).Contains z) (hK : (kBounds B).Contains (σ/(2-σ)))
    (hM : (muBounds B w).Contains (g3Weight h σ))
    (hJ : (w.jensen.value B : ℝ) ≤ g3DividedJensen (h * (σ/(2-σ))) z)
    (hF : balancedFarIncrement criticalQ (1 - h)
      (balancedFarCenter (h * (σ / (2 - σ))) (h * (σ / (2 - σ))) 1 z) (signed positive u) / h ≤ F) :
    let A := nearTerms B positive w
    (A.squared : ℝ) * u ^ 2 - (A.linearCost : ℝ) * u + (A.constant : ℝ) -
      g3Weight h σ * F ≤ g3FacetGap h σ 1 (signed positive u) z / h := by
  intro A
  let k := σ / (2 - σ)
  let μ := g3Weight h σ
  let s := signed positive u
  let r := (signRat positive : ℝ)
  let W := k * (z - 1)
  let V := (1 - h) * s + h * W
  let D := (2 - h) * u ^ 2 - 2 * (1 - h) * W * s - h * W ^ 2
  let j := (w.jensen.value B : ℝ)
  let rm := criticalQ * (7 / 4 - criticalQ)
  have hs : s = r * u := signed_eq_mul _ _
  have hs_abs : |s| = u := signed_abs _ hu
  have hs₂ : s ^ 2 = u ^ 2 := by rw [← sq_abs s, hs_abs]
  have hs₄ : s ^ 4 = u ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_mul, hs₂]
  have h1 : (point 1).Contains (1 : ℝ) := by simpa using point_has 1
  have h2 : (point 2).Contains (2 : ℝ) := by simpa using point_has 2
  have hS := RatBounds.mul_mem (point_has (signRat positive)) hU
  rw [← hs] at hS
  have hW : ((kBounds B).mul ((bounds B 3).sub (point 1))).Contains W :=
    RatBounds.mul_mem hK (RatBounds.sub_mem hZ h1)
  have h2h := RatBounds.sub_mem h2 hH
  have h1h := RatBounds.sub_mem h1 hH
  have hV := RatBounds.add_mem (RatBounds.mul_mem h1h hS) (RatBounds.mul_mem hH hW)
  have hD := RatBounds.sub_mem
    (RatBounds.sub_mem (RatBounds.mul_mem h2h (square_mem hU))
      (RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem h2 h1h) hW) hS))
    (RatBounds.mul_mem hH (square_mem hW))
  have hM' := RatBounds.sub_mem h1 hM
  have hMK := RatBounds.mul_mem hM hK
  have hCoef := RatBounds.mul_mem c2_mem (RatBounds.add_mem (RatBounds.mul_mem hM' h2h) hMK)
  have hLinear := RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem
    (RatBounds.mul_mem hM' c2_mem) h2) h1h) (RatBounds.mul_mem hW (point_has (signRat positive)))
  have hGain := RatBounds.mul_mem c4_mem
    (RatBounds.add_mem (RatBounds.mul_mem (RatBounds.mul_mem hM' hD)
      (RatBounds.add_mem (square_mem hU) (square_mem hV)))
      (RatBounds.mul_mem hMK (fourth_mem hU)))
  have hConst := (RatBounds.add_mem (RatBounds.mul_mem hMK (point_has (w.jensen.value B))) hGain).1
  have hSq := (RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem hM' c2_mem) hH)
    (square_mem hW)).2
  let cap := max 0 ((absBounds ((kBounds B).mul ((bounds B 3).sub (point 1)))).hi - B.lo 2)
  have hWabs := abs_mem hW
  have hcap : max 0 (|W| - u) ≤ (cap : ℝ) := by
    simp only [cap, Rat.cast_max, Rat.cast_sub, Rat.cast_zero]
    exact max_le_max_left 0 (sub_le_sub hWabs.2 hU.1)
  have hrem := RatBounds.mul_mem (RatBounds.mul_mem hM' rem_mem)
    (pos_pow_mem hWabs (abs_pos_lo _) 5)
  have hTail := (RatBounds.mul_mem hrem (point_has cap)).2
  have hμpos := g3_weight_pos_lt_third hh.le hh₁ hσ hσ₁
  have hmR : 0 ≤ (1 - μ) * rm * |W| ^ 5 := by
    have hμ : μ < 1 / 3 := hμpos.2
    have hrm : 0 ≤ rm := mul_nonneg (by linarith only [criticalQ_bracket.1])
      (by linarith only [criticalQ_bracket.2])
    exact mul_nonneg (mul_nonneg (by linarith only [hμ]) hrm) (pow_nonneg (abs_nonneg W) _)
  have hTail' := mul_le_mul_of_nonneg_left hcap hmR
  have hCoef' := mul_le_mul_of_nonneg_right hCoef.1 (sq_nonneg u)
  have hLinear' := mul_le_mul_of_nonneg_right hLinear.2 hu
  have htermA : (A.squared : ℝ) * u ^ 2 ≤
      g3NearC2 * ((1 - μ) * (2 - h) + μ * k) * u ^ 2 := hCoef'
  have htermB : (1 - μ) * g3NearC2 * 2 * (1 - h) * (W * r) * u ≤
      (A.linearCost : ℝ) * u := hLinear'
  have htermC : (A.constant : ℝ) ≤ μ * k * j +
      g3NearC4 * ((1 - μ) * D * (u ^ 2 + V ^ 2) + μ * k * u ^ 4) -
      (1 - μ) * g3NearC2 * h * W ^ 2 - (1 - μ) * rm * |W| ^ 5 * max 0 (|W| - u) := by
    unfold A nearTerms
    simp only [Rat.cast_sub]
    have h₀ : _ ≤ μ * k * j +
        g3NearC4 * ((1 - μ) * D * (u ^ 2 + V ^ 2) + μ * k * u ^ 4) := hConst
    have h₁ : (1 - μ) * g3NearC2 * h * W ^ 2 ≤ _ := hSq
    have h₂ : (1 - μ) * rm * |W| ^ 5 * (cap : ℝ) ≤ _ := hTail
    exact sub_le_sub (sub_le_sub h₀ h₁) (hTail'.trans h₂)
  have hlo := divided_gap_lower hh hh₁ hσ hσ₁ (s := s) (by rwa [hs_abs]) hz hJ hF
  dsimp only at hlo
  change μ * k * (j + g3NearC2 * s ^ 2 + g3NearC4 * s ^ 4) +
    (1 - μ) * (g3NearC2 * ((2 - h) * s ^ 2 - 2 * (1 - h) * W * s - h * W ^ 2) +
      g3NearC4 * ((2 - h) * s ^ 2 - 2 * (1 - h) * W * s - h * W ^ 2) *
        (s ^ 2 + V ^ 2) - rm * |W| ^ 5 * max 0 (|W| - |s|)) - μ * F ≤ _ at hlo
  rw [hs₂, hs₄, hs_abs] at hlo
  change μ * k * (j + g3NearC2 * u ^ 2 + g3NearC4 * u ^ 4) +
    (1 - μ) * (g3NearC2 * D + g3NearC4 * D * (u ^ 2 + V ^ 2) -
      rm * |W| ^ 5 * max 0 (|W| - u)) - μ * F ≤ _ at hlo
  have hpoly := sub_le_sub_right (add_le_add (sub_le_sub htermA htermB) htermC) (μ * F)
  refine hpoly.trans ?_
  refine le_trans (le_of_eq ?_) hlo
  dsimp only [D]
  rw [hs]
  ring

end

end HlawkaSchatten.BelowExponent.G3P
