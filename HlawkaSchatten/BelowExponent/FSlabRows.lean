/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabScheduledCone
public import HlawkaSchatten.BelowExponent.FSlabCover
public import HlawkaSchatten.BelowExponent.FSlabInterpolation
public import HlawkaSchatten.BelowExponent.Tangent.Rectangle
import all HlawkaSchatten.BelowExponent.Tangent.Rectangle
import Batteries.Tactic.OpenPrivate

/-! The row comparisons used by the F endpoint certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set Tangent
open private chartRow_lerpA chartRow_lerpB abs_eq_mul_on_Icc endpoints_mem_Icc
  cornerOutput_convex from HlawkaSchatten.BelowExponent.Tangent.Rectangle

noncomputable section

def fPairOutput (l μ e₀ e₁ : ℝ) (i : Fin 3) (x : Row) : ℝ :=
  let out e e' := weightedOutput criticalQ (balancedProfile l e l) (balancedPi μ e') x
  ![out e₀ e₀ + out e₀ e₀, out e₁ e₁ + out e₁ e₁, out e₀ e₁ + out e₁ e₀] i

def fDoubleGamma (μ l : ℝ) : Row := fun j => 2*balancedGamma μ l j

theorem fPairOutput_convex {l μ e₀ e₁ : ℝ} (hm₀ : 0 ≤ μ) (hm₁ : μ ≤ 1)
    (he₀ : |e₀| ≤ 1) (he₁ : |e₁| ≤ 1) (i : Fin 3) :
    ConvexOn ℝ Set.univ (fPairOutput l μ e₀ e₁ i) := by
  have h (e e' : ℝ) (he : |e'| ≤ 1) : ConvexOn ℝ (univ : Set Row)
      (weightedOutput criticalQ (balancedProfile l e l) (balancedPi μ e')) :=
    cornerOutput_convex facetCritical_one_lt.le (isSimplex_balancedPi hm₀ hm₁ he).1
  fin_cases i
  · exact (h e₀ e₀ he₀).add (h e₀ e₀ he₀)
  · exact (h e₁ e₁ he₁).add (h e₁ e₁ he₁)
  · exact (h e₀ e₁ he₁).add (h e₁ e₀ he₀)

private theorem affine_corners {f : Row → ℝ} (hf : ConvexOn ℝ univ f) (j : Fin 3)
    {a₀ a₁ b₀ b₁ a b c d e : ℝ} (ha : a ∈ Icc a₀ a₁) (hb : b ∈ Icc b₀ b₁)
    (h : ∀ A ∈ ({a₀,a₁} : Set ℝ), ∀ B ∈ ({b₀,b₁} : Set ℝ), f (chartRow j A B) ≤ c+d*A+e*B) :
    f (chartRow j a b) ≤ c+d*a+e*b := by
  obtain ⟨u, hu, hA⟩ := exists_interval_lerp ha.1 ha.2
  obtain ⟨v, hv, hB⟩ := exists_interval_lerp hb.1 hb.2
  have hline (A : ℝ) (hmem : A ∈ ({a₀,a₁} : Set ℝ)) : f (chartRow j A b) ≤ c+d*A+e*b := by
    calc
      _ ≤ (1-v)*f (chartRow j A b₀)+v*f (chartRow j A b₁) := by
        rw [hB, chartRow_lerpB]
        exact hf.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hv.2) hv.1 (sub_add_cancel 1 v)
      _ ≤ (1-v)*(c+d*A+e*b₀)+v*(c+d*A+e*b₁) :=
        add_le_add (mul_le_mul_of_nonneg_left (h A hmem b₀ (by simp)) (sub_nonneg.mpr hv.2))
          (mul_le_mul_of_nonneg_left (h A hmem b₁ (by simp)) hv.1)
      _ = _ := by rw [hB]; ring
  calc
    _ ≤ (1-u)*f (chartRow j a₀ b)+u*f (chartRow j a₁ b) := by
      rw [hA, chartRow_lerpA]
      exact hf.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)
    _ ≤ (1-u)*(c+d*a₀+e*b)+u*(c+d*a₁+e*b) :=
      add_le_add (mul_le_mul_of_nonneg_left (hline a₀ (by simp)) (sub_nonneg.mpr hu.2))
        (mul_le_mul_of_nonneg_left (hline a₁ (by simp)) hu.1)
    _ = _ := by rw [hA]; ring

theorem fRows_of_signed_rectangle {f : Row → ℝ} (hf : ConvexOn ℝ univ f) {γ : Row}
    (hγ : ∀ j, 0 ≤ γ j) (j : Fin 3) {a₀ a₁ b₀ b₁ a b c₀ c₁ d₀ d₁ : ℝ}
    (ha : a ∈ Icc a₀ a₁) (hb : b ∈ Icc b₀ b₁)
    (hsA : 0 ≤ a₀ ∨ a₁ ≤ 0) (hsB : 0 ≤ b₀ ∨ b₁ ≤ 0)
    (hA : c₀+c₁*|a| ≤ |a|^criticalQ) (hB : d₀+d₁*|b| ≤ |b|^criticalQ)
    (hcorners : ∀ A ∈ ({a₀,a₁} : Set ℝ), ∀ B ∈ ({b₀,b₁} : Set ℝ),
      f (chartRow j A B) ≤ cornerInput γ j (fun x => c₀+c₁*|x|) (fun x => d₀+d₁*|x|) A B) :
    f (chartRow j a b) ≤ ∑ k, γ k*|chartRow j a b k|^criticalQ := by
  obtain ⟨s, hs⟩ := abs_eq_mul_on_Icc hsA
  obtain ⟨t, ht⟩ := abs_eq_mul_on_Icc hsB
  let L (x : ℝ) := c₀+c₁*|x|
  let M (x : ℝ) := d₀+d₁*|x|
  have hlin {A B : ℝ} (hA : A ∈ Icc a₀ a₁) (hB : B ∈ Icc b₀ b₁) :
      cornerInput γ j L M A B = γ j+γ (chartA j)*c₀+γ (chartB j)*d₀
        +(γ (chartA j)*c₁*s)*A+(γ (chartB j)*d₁*t)*B := by
    simp only [cornerInput,L,M,hs A hA,ht B hB]
    ring
  have h : f (chartRow j a b) ≤ cornerInput γ j L M a b := by
    rw [hlin ha hb]
    apply affine_corners hf j ha hb
    intro A hAm B hBm
    rw [← hlin (endpoints_mem_Icc (ha.1.trans ha.2) hAm) (endpoints_mem_Icc (hb.1.trans hb.2) hBm)]
    exact hcorners A hAm B hBm
  refine h.trans ?_
  have h₀ := mul_le_mul_of_nonneg_left hA (hγ (chartA j))
  have h₁ := mul_le_mul_of_nonneg_left hB (hγ (chartB j))
  fin_cases j <;> simp [cornerInput,L,M,chartRow,chartA,chartB,Fin.sum_univ_three] at h₀ h₁ ⊢ <;>
    linarith only [h₀,h₁]

def FBandRows (l μ e₀ e₁ : ℝ) : Prop :=
  ∀ (j : Fin 3) (a b : ℝ), |a| ≤ 1 → |b| ≤ 1 → ¬ FacetRatioCone (1/64) (chartRow j a b) →
    ∀ k, fPairOutput l μ e₀ e₁ k (chartRow j a b) ≤
      ∑ u, fDoubleGamma μ l u * |chartRow j a b u|^criticalQ

theorem weightedRow_fBand {l μ e₀ e₁ e : ℝ} (hl : 74/4096 ≤ l) (hL : l ≤ 7/125)
    (hm : 21/100 ≤ μ) (hM : μ ≤ 27/100) (hml : 37/200 ≤ μ-l)
    (he₀ : 0 ≤ e₀) (he₁ : e₁ ≤ 1/2) (hea : e₀ ≤ e) (heb : e ≤ e₁)
    (h : FBandRows l μ e₀ e₁) (x : Row) : WeightedRow criticalQ
      (balancedProfile l e l) (balancedPi μ e) (balancedGamma μ l) x := by
  apply weightedRow_of_chart_squares (zero_lt_one.trans facetCritical_one_lt) _ x
  intro j a b ha hb
  by_cases hc : FacetRatioCone (1/64) (chartRow j a b)
  · exact fScheduled_cone hl hL (he₀.trans hea) (heb.trans he₁) hm hM hml hc
  · let x := chartRow j a b
    let C := ∑ k, balancedGamma μ l k*|x k|^criticalQ
    let out e e' := weightedOutput criticalQ (balancedProfile l e l) (balancedPi μ e') x
    have hC : ∑ k, fDoubleGamma μ l k*|x k|^criticalQ = 2*C := by
      simp [C, fDoubleGamma, Finset.mul_sum, mul_assoc]
    have h₀ := h j a b ha hb hc 0
    have h₁ := h j a b ha hb hc 1
    have h₂ := h j a b ha hb hc 2
    rw [hC] at h₀ h₁ h₂
    change out e₀ e₀+out e₀ e₀ ≤ 2*C at h₀
    change out e₁ e₁+out e₁ e₁ ≤ 2*C at h₁
    change out e₀ e₁+out e₁ e₀ ≤ 2*C at h₂
    obtain ⟨u, hU, hu⟩ := exists_interval_lerp hea heb
    change out e e ≤ C
    rw [hu]
    exact balancedOutput_of_imbalance_interval (by linarith) (by linarith) he₀ he₁
      (hea.trans heb) hU.1 hU.2 (by linarith only [h₀]) (by linarith only [h₁]) h₂

end

end HlawkaSchatten.BelowExponent
