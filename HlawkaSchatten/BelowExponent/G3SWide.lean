/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3
import all HlawkaSchatten.BelowExponent.G1
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Convex.Slope

/-! Secant bounds for the divided transverse G3 gap on a closed box. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3S

open Set
open private absPower_convex from HlawkaSchatten.BelowExponent.G1

noncomputable section

def power (x : ℝ) : ℝ := |x| ^ criticalQ

def pairMean (p w : ℝ) : ℝ := (power (w + p) + power (w - p)) / 2

private theorem power_neg (x : ℝ) : power (-x) = power x := by simp [power]

private theorem power_convex : ConvexOn ℝ univ power :=
  absPower_convex ((by norm_num : (1 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le)

private theorem secant_le {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hbd : b ≤ d) : slope power a b ≤ slope power c d := by
  have had := hab.trans_le hbd
  calc
    slope power a b ≤ slope power a d := by
      simp only [slope_def_field]
      exact power_convex.secant_mono (mem_univ _) (mem_univ _) (mem_univ _)
        hab.ne' had.ne' hbd
    _ ≤ slope power c d := by
      rw [slope_comm power a d, slope_comm power c d]
      simp only [slope_def_field]
      exact power_convex.secant_mono (mem_univ _) (mem_univ _) (mem_univ _)
        had.ne hcd.ne hac

theorem leftSecant_lower {x x₀ t T : ℝ}
    (hx : x₀ ≤ x) (ht : 0 ≤ t) (htT : t ≤ T) (hT : 0 < T) :
    ((power x₀ - power (x₀ - T)) / T) * t ≤ power x - power (x - t) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have h := secant_le (a := x₀ - T) (b := x₀) (c := x - t) (d := x)
    (by linarith) (by linarith) (by linarith) hx
  simp only [slope_def_field, sub_sub_cancel] at h
  exact (le_div_iff₀ ht).mp h

theorem rightSecant_upper {x x₁ t T : ℝ}
    (hx : x ≤ x₁) (ht : 0 ≤ t) (htT : t ≤ T) (hT : 0 < T) :
    power (x + t) - power x ≤ ((power (x₁ + T) - power x₁) / T) * t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have h := secant_le (a := x) (b := x + t) (c := x₁) (d := x₁ + T)
    (by linarith) (by linarith) hx (by linarith)
  simp only [slope_def_field, add_sub_cancel_left] at h
  exact (div_le_iff₀ ht).mp h

theorem farPair_upper {U U₀ : ℝ} (hU : U₀ ≤ U) :
    (power (U - 2) - power U) / 2 ≤ (power (U₀ - 2) - power U₀) / 2 := by
  have h := secant_le (a := U₀ - 2) (b := U₀) (c := U - 2) (d := U)
    (by linarith) (by linarith) (by linarith) hU
  simp only [slope_def_field, sub_sub_cancel] at h
  linarith only [h]

theorem gap_identity (h σ p z : ℝ) :
    let k := σ / (2 - σ)
    let μ := g3Weight h σ
    let a := 1 + k * (p - z)
    let U := z + h * a
    g3FacetGap h σ p 1 z =
      (1 - μ) * (pairMean p 1 - pairMean p (1 - h * a)) +
        μ * (h * k * (pairMean p 1 - power z) - (power U - power z) -
          h * ((power (U - 2) - power U) / 2)) := by
  intro k μ a U
  have hU₀ : balancedFarCenter (h * k) (h * k) p z - (1 + (1 - h)) * 1 = U - 2 := by
    dsimp [balancedFarCenter, U, a]; ring
  have hU₁ : balancedFarCenter (h * k) (h * k) p z + (1 - (1 - h)) * 1 = U := by
    dsimp [balancedFarCenter, U, a]; ring
  have hv : balancedNearShift (h * k) (1 - h) (h * k) p 1 z = 1 - h * a := by
    dsimp [balancedNearShift, a]; ring
  have he (w : ℝ) : balancedEvenGap criticalQ p w = pairMean p w - power p := by
    unfold balancedEvenGap pairMean
    change (power (p + w) + power (p - w)) / 2 - power p = _
    rw [add_comm p w, ← power_neg (p - w), neg_sub]
  change balancedFacetGap criticalQ μ (h * k) (1 - h) p 1 z = _
  unfold balancedFacetGap balancedJensenGap balancedFarIncrement
  rw [hv, hU₀, hU₁, he, he]
  simp only [power]
  ring

def nearSecant (p₀ p₁ T : ℝ) : ℝ :=
  ((power (1 + p₀) - power (1 + p₀ - T)) / T +
    (power (1 - p₁) - power (1 - p₁ - T)) / T) / 2

def farSecant (z₁ T : ℝ) : ℝ := (power (z₁ + T) - power z₁) / T

/-- Secant comparison for the actual balanced gap, including the first depth slab. -/
theorem lower_bound {h σ p z p₀ p₁ z₁ T U₀ C : ℝ}
    (hh : 0 ≤ h) (hk : 0 ≤ σ / (2 - σ))
    (ha : 0 ≤ 1 + (σ / (2 - σ)) * (p - z))
    (hT : 0 < T) (htT : h * (1 + (σ / (2 - σ)) * (p - z)) ≤ T)
    (hp₀ : p₀ ≤ p) (hp₁ : p ≤ p₁) (hz₁ : z ≤ z₁)
    (hU₀ : U₀ ≤ z + h * (1 + (σ / (2 - σ)) * (p - z)))
    (hC : C ≤ pairMean p 1 - power z)
    (hμ₀ : 0 ≤ g3Weight h σ) (hμ₁ : g3Weight h σ ≤ 1) :
    let k := σ / (2 - σ)
    let μ := g3Weight h σ
    let a := 1 + k * (p - z)
    h * ((1 - μ) * a * nearSecant p₀ p₁ T +
      μ * (k * C - a * farSecant z₁ T - (power (U₀ - 2) - power U₀) / 2)) ≤
      g3FacetGap h σ p 1 z := by
  intro k μ a
  let t := h * a
  have ht : 0 ≤ t := mul_nonneg hh ha
  have hn₁ := leftSecant_lower (x := 1 + p) (x₀ := 1 + p₀) (t := t)
    (by linarith) ht htT hT
  have hn₂ := leftSecant_lower (x := 1 - p) (x₀ := 1 - p₁) (t := t)
    (by linarith) ht htT hT
  have hn : t * nearSecant p₀ p₁ T ≤ pairMean p 1 - pairMean p (1 - t) := by
    unfold nearSecant pairMean
    rw [show 1 - t + p = 1 + p - t by ring, show 1 - t - p = 1 - p - t by ring]
    linarith only [hn₁, hn₂]
  have hf := rightSecant_upper hz₁ ht htT hT
  have hP := farPair_upper hU₀
  have h₁ := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hμ₁)
  have h₂ := mul_le_mul_of_nonneg_left hC (mul_nonneg hh hk)
  have h₃ := mul_le_mul_of_nonneg_left hP hh
  have hfar : h * k * C - t * farSecant z₁ T -
      h * ((power (U₀ - 2) - power U₀) / 2) ≤
      h * k * (pairMean p 1 - power z) - (power (z + t) - power z) -
      h * ((power (z + t - 2) - power (z + t)) / 2) := by
    dsimp only [farSecant] at *
    change h * ((power (z + t - 2) - power (z + t)) / 2) ≤
      h * ((power (U₀ - 2) - power U₀) / 2) at h₃
    linarith only [h₂, hf, h₃]
  rw [gap_identity]
  have htotal := add_le_add h₁ (mul_le_mul_of_nonneg_left hfar hμ₀)
  dsimp only [t, k, μ, a] at htotal
  convert htotal using 1
  ring

end

end HlawkaSchatten.BelowExponent.G3S
