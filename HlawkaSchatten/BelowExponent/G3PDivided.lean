/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3SWide
public import HlawkaSchatten.BelowExponent.G3PNear
public import HlawkaSchatten.BelowExponent.G3PJensen
public import HlawkaSchatten.BelowExponent.G3PFar

/-! Secants for the far pair and the real divided-gap bound on the G3 p = 1 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open G3S (power)

noncomputable section

def farCoeff (h₀ h₁ a₀ a₁ : ℝ) : ℝ :=
  (power (a₀ + h₀ - 2) - power (a₀ + h₀)) / 2 + G3S.farSecant a₁ h₁

theorem far_div_eq {h Z s : ℝ} (hh : h ≠ 0) (hs : s ≠ 0) :
    let a := Z / s
    balancedFarIncrement criticalQ (1 - h) Z s / h =
      power s * ((power (a + h - 2) - power (a + h)) / 2 +
        (power (a + h) - power a) / h) := by
  intro a
  have ha : a * s = Z := div_mul_cancel₀ _ hs
  have hp (x : ℝ) : power (x * s) = power s * power x := by
    unfold power
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm]
  have h0 : Z - (1 + (1 - h)) * s = (a + h - 2) * s := by
    rw [← ha]; ring
  have h1 : Z + (1 - (1 - h)) * s = (a + h) * s := by
    rw [← ha]; ring
  unfold balancedFarIncrement
  rw [h0, h1]
  change (((1 - (1 - h)) / 2) * power ((a + h - 2) * s) +
    ((1 + (1 - h)) / 2) * power ((a + h) * s) - power Z) / h = _
  rw [← ha, hp, hp, hp]
  field_simp [hh]
  ring

/-- Normalize by the signed transverse coordinate and bound each far-pair secant. -/
theorem far_div_le_secants {h h₀ h₁ Z s a₀ a₁ : ℝ}
    (hh : 0 < h) (hh₀ : h₀ ≤ h) (hh₁ : h ≤ h₁) (hs : s ≠ 0)
    (ha₀ : a₀ ≤ Z / s) (ha₁ : Z / s ≤ a₁) :
    balancedFarIncrement criticalQ (1 - h) Z s / h ≤ power s * farCoeff h₀ h₁ a₀ a₁ := by
  let a := Z / s
  have hpair := G3S.farPair_upper (U := a + h) (U₀ := a₀ + h₀) (add_le_add ha₀ hh₀)
  have hsec := G3S.rightSecant_upper ha₁ hh.le hh₁ (hh.trans_le hh₁)
  have hcost : (power (a + h - 2) - power (a + h)) / 2 +
      (power (a + h) - power a) / h ≤ farCoeff h₀ h₁ a₀ a₁ :=
    add_le_add hpair ((div_le_iff₀ hh).2 hsec)
  rw [far_div_eq hh.ne' hs]
  exact mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (abs_nonneg s) _)

theorem divided_gap_lower {h σ s z J F : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5)
    (hs : |s| ≤ 1) (hz : |z| ≤ 8)
    (hJ : J ≤ g3DividedJensen (h * (σ / (2 - σ))) z)
    (hF : balancedFarIncrement criticalQ (1 - h)
      (balancedFarCenter (h * (σ / (2 - σ))) (h * (σ / (2 - σ))) 1 z) s / h ≤ F) :
    let k := σ / (2 - σ)
    let μ := g3Weight h σ
    let w := k * (z - 1)
    let v := (1 - h) * s + h * w
    let D := (2 - h) * s ^ 2 - 2 * (1 - h) * w * s - h * w ^ 2
    μ * k * (J + g3NearC2 * s ^ 2 + g3NearC4 * s ^ 4) +
      (1 - μ) * (g3NearC2 * D + g3NearC4 * D * (s ^ 2 + v ^ 2) -
        criticalQ * (7 / 4 - criticalQ) * |w| ^ 5 * max 0 (|w| - |s|)) -
      μ * F ≤ g3FacetGap h σ 1 s z / h := by
  intro k μ w v D
  have hk : 0 < k := div_pos hσ (by linarith)
  have hk₁ : k ≤ 1 / 9 := (div_le_iff₀ (by linarith : 0 < 2 - σ)).2 (by linarith)
  have hμ := g3_weight_pos_lt_third hh.le hh₁ hσ hσ₁
  have hw : |w| ≤ 1 := by
    have hd := abs_sub z 1
    simp only [abs_one] at hd
    have hz' : |z - 1| ≤ 9 := by linarith only [hd, hz]
    dsimp [w]
    rw [abs_mul, abs_of_pos hk]
    calc
      k * |z - 1| ≤ (1 / 9) * 9 := mul_le_mul hk₁ hz' (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hnear := g3NearDivided_lower hh hh₁ hs hw
  have hshift : balancedNearShift (h * k) (1 - h) (h * k) 1 s z = v := by
    dsimp [balancedNearShift, v, w]
    ring
  have hA := g3NearEven_lower hs
  have hfirst := mul_le_mul_of_nonneg_left (add_le_add hJ hA) (mul_nonneg hμ.1.le hk.le)
  have hmid := mul_le_mul_of_nonneg_left hnear (show 0 ≤ 1 - μ by linarith only [hμ.2])
  have hfar := mul_le_mul_of_nonneg_left hF hμ.1.le
  change _ ≤ balancedFacetGap criticalQ μ (h * k) (1 - h) 1 s z / h
  rw [balancedFacetGap_div_h criticalQ μ h k 1 s z hh.ne' hk.ne', hshift]
  change _ ≤ μ * k * (g3DividedJensen (h * k) z + balancedEvenGap criticalQ 1 s) +
    (1 - μ) * (balancedEvenGap criticalQ 1 s - balancedEvenGap criticalQ 1 v) / h - _
  simp only [mul_div_assoc]
  change (1 - μ) * (g3NearC2 * D + g3NearC4 * D * (s ^ 2 + v ^ 2) -
      criticalQ * (7 / 4 - criticalQ) * |w| ^ 5 * max 0 (|w| - |s|)) ≤
    (1 - μ) * ((balancedEvenGap criticalQ 1 s - balancedEvenGap criticalQ 1 v) / h) at hmid
  have hsum := sub_le_sub (add_le_add hfirst hmid) hfar
  convert hsum using 1
  ring

end

end HlawkaSchatten.BelowExponent.G3P
