/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetTaylor
public import HlawkaSchatten.BelowExponent.Tangent.FineTable
public import HlawkaSchatten.BelowExponent.Tangent.Real

/-! Rational Taylor bounds close the rows where the ordinary tangent grid is too coarse. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

open Set

def nearQLo : ℚ := 1054 / 665
def nearQHi : ℚ := 24727 / 15601
def nearC₂lo : ℚ := nearQLo * (nearQLo - 1) / 2
def nearC₂hi : ℚ := nearQHi * (nearQHi - 1) / 2
def nearC₃lo : ℚ := nearQLo * (nearQLo - 1) * (2 - nearQHi) / 6
def nearC₃hi : ℚ := nearQHi * (nearQHi - 1) * (2 - nearQLo) / 6

def nearUpper (u : ℚ) : ℚ :=
  if u ≤ 0 then 1 + nearQLo * u + nearC₂hi * u^2 + nearC₃hi * (-u)^3 / (1+u)^2
  else 1 + nearQHi * u + nearC₂hi * u^2 - nearC₃lo * u^3 / (1+u)^2

def nearSlope (r : ℚ) : ℚ := -nearQHi + 2 * nearC₂lo * r + 3 * nearC₃lo * r^2

def nearIntercept (r : ℚ) : ℚ := 1 - nearC₂lo * r^2 - 2 * nearC₃lo * r^3 + nearSlope r

private theorem nearBracket : (nearQLo : ℝ) ≤ criticalQ ∧ criticalQ ≤ (nearQHi : ℝ) := by
  have h := Tangent.exponent_bracket_of_tabOK TC.fine_tab_ok (by decide)
  simp only [TC.fine_prof, nearQLo, nearQHi, Rat.cast_div, Nat.cast_ofNat, Rat.cast_ofNat] at *
  exact ⟨h.1.le, h.2.le⟩

private theorem nearConstant_bounds :
    1 < criticalQ ∧ criticalQ < 2 ∧
    (nearC₂lo : ℝ) ≤ facetQuadratic criticalQ ∧ facetQuadratic criticalQ ≤ (nearC₂hi : ℝ) ∧
    (nearC₃lo : ℝ) ≤ facetCubic criticalQ ∧ facetCubic criticalQ ≤ (nearC₃hi : ℝ) := by
  obtain ⟨hl, hh⟩ := nearBracket
  have hlo : (1 : ℝ) < nearQLo := by norm_num [nearQLo]
  have hhi : (nearQHi : ℝ) < 2 := by norm_num [nearQHi]
  have h₁ := hlo.trans_le hl
  have h₂ := hh.trans_lt hhi
  have hL := mul_le_mul hl (sub_le_sub_right hl 1) (by linarith) (by linarith)
  have hU := mul_le_mul hh (sub_le_sub_right hh 1) (by linarith) (by linarith)
  have hL' := mul_le_mul hL (sub_le_sub_left hh 2) (by linarith) (by positivity)
  have hU' := mul_le_mul hU (sub_le_sub_left hl 2) (by linarith)
    (show 0 ≤ (nearQHi : ℝ) * ((nearQHi : ℝ) - 1) by exact mul_nonneg (by linarith) (by linarith))
  refine ⟨h₁, h₂, ?_, ?_, ?_, ?_⟩
  all_goals push_cast [nearC₂lo, nearC₂hi, nearC₃lo, nearC₃hi, facetQuadratic, facetCubic]
  all_goals linarith only [hL, hU, hL', hU']

theorem rpow_le_nearUpper {u : ℚ} (hu : -1 < u) :
    (1 + (u : ℝ))^criticalQ ≤ (nearUpper u : ℝ) := by
  let t : ℝ := u
  have ht : -1 < t := by change (-1 : ℝ) < (u : ℝ); exact_mod_cast hu
  obtain ⟨hq₁, hq₂, _, hq₂U, hq₃L, hq₃U⟩ := nearConstant_bounds
  obtain ⟨z, hz, hrem⟩ := facetRemainder_lagrange criticalQ ht
  have hbas : 0 < 1 + t := by linarith
  have hZ : 0 < z := (lt_min zero_lt_one hbas).trans_le hz.1
  have hpower : (1+t)^criticalQ = 1 + criticalQ*t + facetQuadratic criticalQ*t^2 -
      facetCubic criticalQ*z^(criticalQ-3)*t^3 := by
    unfold facetRemainder at hrem
    linarith only [hrem]
  have hc₃ : 0 ≤ facetCubic criticalQ := by unfold facetCubic; positivity
  have hcL : 0 ≤ (nearC₃lo : ℝ) := by norm_num [nearC₃lo, nearQLo, nearQHi]
  have hqp₂ := mul_le_mul_of_nonneg_right hq₂U (sq_nonneg t)
  unfold nearUpper
  split
  · rename_i hu₀
    have ht₀ : t ≤ 0 := by change (u : ℝ) ≤ 0; exact_mod_cast hu₀
    have hzL : 1 + t ≤ z := by
      simpa only [min_eq_right (by linarith : 1+t ≤ 1)] using hz.1
    have hzU : z ≤ 1 := by
      simpa only [max_eq_left (by linarith : 1+t ≤ 1)] using hz.2
    have hp : z^(criticalQ-3) ≤ ((1+t)^2)⁻¹ := by
      calc
        _ ≤ z^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_ge hZ hzU (by linarith)
        _ ≤ (1+t)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos hbas hzL (by norm_num)
        _ = _ := by rw [Real.rpow_neg hbas.le, Real.rpow_two]
    have h3 := mul_le_mul hq₃U hp (Real.rpow_nonneg hZ.le _) (hc₃.trans hq₃U)
    have h3' := mul_le_mul_of_nonneg_right h3 (pow_nonneg (neg_nonneg.mpr ht₀) 3)
    have hq := mul_le_mul_of_nonpos_right nearBracket.1 ht₀
    push_cast
    change (1+t)^criticalQ ≤ 1 + (nearQLo : ℝ)*t + (nearC₂hi : ℝ)*t^2 + (nearC₃hi : ℝ)*(-t)^3 / (1+t)^2
    rw [hpower]
    simp only [div_eq_mul_inv]
    linarith only [hq, hqp₂, h3']
  · rename_i hu₀
    have ht₀ : 0 ≤ t := by change 0 ≤ (u : ℝ); exact_mod_cast (le_of_not_ge hu₀)
    have hzL : 1 ≤ z := by
      simpa only [min_eq_left (by linarith : 1 ≤ 1+t)] using hz.1
    have hzU : z ≤ 1+t := by
      simpa only [max_eq_right (by linarith : 1 ≤ 1+t)] using hz.2
    have hp : ((1+t)^2)⁻¹ ≤ z^(criticalQ-3) := by
      calc
        _ = (1+t)^(-2:ℝ) := by rw [Real.rpow_neg hbas.le, Real.rpow_two]
        _ ≤ z^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos hZ hzU (by norm_num)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hzL (by linarith)
    have h3 := mul_le_mul hq₃L hp (inv_nonneg.mpr (sq_nonneg _)) hc₃
    have h3' := mul_le_mul_of_nonneg_right h3 (pow_nonneg ht₀ 3)
    have hq := mul_le_mul_of_nonneg_right nearBracket.2 ht₀
    push_cast
    change (1+t)^criticalQ ≤ 1 + (nearQHi : ℝ)*t + (nearC₂hi : ℝ)*t^2 - (nearC₃lo : ℝ)*t^3 / (1+t)^2
    rw [hpower]
    simp only [div_eq_mul_inv]
    linarith only [hq, hqp₂, h3']

theorem nearTangent_le_rpow {r : ℚ} (hr : 0 ≤ r) {x : ℝ} (hx : 0 < |x|) (hx₁ : |x| ≤ 1) :
    (nearIntercept r : ℝ) - (nearSlope r : ℝ)*|x| ≤ |x|^criticalQ := by
  let v := 1 - |x|
  have hv : 0 ≤ v := sub_nonneg.mpr hx₁
  have hv₁ : -1 < -v := by dsimp [v]; linarith
  have hr₀ : (0 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨hq₁, hq₂, hq₂L, _, hq₃L, _⟩ := nearConstant_bounds
  obtain ⟨z, hz, hrem⟩ := facetRemainder_lagrange criticalQ hv₁
  have hseq : 1 + -v = |x| := by dsimp [v]; ring
  have hZ : 0 < z := by
    rw [hseq] at hz
    exact (lt_min zero_lt_one hx).trans_le hz.1
  have hZ₁ : z ≤ 1 := by
    simpa only [hseq, max_eq_left hx₁] using hz.2
  have hp : 1 ≤ z^(criticalQ-3) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hZ hZ₁ (show criticalQ-3 ≤ (0 : ℝ) by linarith)
  have hc₃ : 0 ≤ facetCubic criticalQ := by unfold facetCubic; positivity
  have h3 := mul_le_mul_of_nonneg_right (hq₃L.trans (le_mul_of_one_le_right hc₃ hp)) (pow_nonneg hv 3)
  have h2 := mul_le_mul_of_nonneg_right hq₂L (sq_nonneg v)
  have h1 := mul_le_mul_of_nonneg_right nearBracket.2 hv
  unfold facetRemainder at hrem
  rw [hseq] at hrem
  have hPoly : 1 - (nearQHi : ℝ)*v + (nearC₂lo : ℝ)*v^2 + (nearC₃lo : ℝ)*v^3 ≤ |x|^criticalQ := by
    linarith only [hrem,h1,h2,h3]
  refine le_trans ?_ hPoly
  have hC₂ : (0 : ℝ) ≤ nearC₂lo := by norm_num [nearC₂lo, nearQLo]
  have hC₃ : (0 : ℝ) ≤ nearC₃lo := by norm_num [nearC₃lo, nearQLo, nearQHi]
  have hP₂ := mul_nonneg hC₂ (sq_nonneg (v-(r:ℝ)))
  have hP₃ := mul_nonneg (mul_nonneg hC₃ (sq_nonneg (v-(r:ℝ)))) (by linarith : 0 ≤ v+2*(r:ℝ))
  push_cast [nearIntercept, nearSlope]
  have heq : |x| = 1 - v := by dsimp [v]; ring
  rw [heq]
  linarith only [hP₂, hP₃]

end HlawkaSchatten.BelowExponent.FacetNumeric
