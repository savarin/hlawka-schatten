/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Balanced
public import HlawkaSchatten.BelowExponent.FacetPrism
import all HlawkaSchatten.BelowExponent.FacetPrism
import Batteries.Tactic.OpenPrivate

/-! The equality cone for the extended balanced facet, uniformly across its slabs. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

open private facet_moment_first facet_moment_second from HlawkaSchatten.BelowExponent.FacetPrism

def fExtensionBase (l e : ℝ) : Row := ![(1 - l + e) / 2, (1 - l - e) / 2, l]

def fExtensionWeight : ℝ := 7 / 25

private theorem fExtension_profile (l e : ℝ) :
    facetBase (fExtensionBase l e) = balancedProfile l e l := by
  funext j
  fin_cases j <;> simp [facetBase, fExtensionBase, balancedProfile, splitProfile]

private theorem fExtension_gamma (l e : ℝ) :
    facetWeight (balancedPi fExtensionWeight e) (fExtensionBase l e) =
      balancedGamma fExtensionWeight l := by
  funext j
  fin_cases j <;>
    simp [facetWeight, balancedPi, fExtensionBase, balancedGamma, Fin.castSucc] <;> ring

private theorem fExtension_pair_bound {l e : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 7/125)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (r : Row)
    (hr : facetMean (fExtensionBase l e) r = 0) :
    (1/6) * facetVariance (fExtensionBase l e) r ≤
      facetPairForm
        ![facetPairWeight (balancedPi fExtensionWeight e) (fExtensionBase l e) 0 1 2,
          facetPairWeight (balancedPi fExtensionWeight e) (fExtensionBase l e) 0 2 1,
          facetPairWeight (balancedPi fExtensionWeight e) (fExtensionBase l e) 1 2 0] r := by
  let x := r 0 - r 1
  let y := r 0 - r 2
  let b := fExtensionBase l e
  let w₀ : ℝ := ((11/25) * (1 - e ^ 2) + l ^ 2) / 4
  let w₁ : ℝ := l * (7/25 + (18/25) * e - l) / 2
  let w₂ : ℝ := l * (7/25 - (18/25) * e - l) / 2
  have hw :
      ![facetPairWeight (balancedPi fExtensionWeight e) b 0 1 2,
        facetPairWeight (balancedPi fExtensionWeight e) b 0 2 1,
        facetPairWeight (balancedPi fExtensionWeight e) b 1 2 0] = ![w₀, w₁, w₂] := by
    funext j
    fin_cases j <;>
      norm_num [facetPairWeight, balancedPi, fExtensionWeight, Fin.castSucc,
        fExtensionBase, b, w₀, w₁, w₂] <;> ring
  change (1/6) * facetVariance b r ≤ _
  rw [hw]
  have hd : (r 1 - r 2) ^ 2 ≤ 4 * x ^ 2 + (4/3) * y ^ 2 := by
    have h := sq_nonneg (3*x + y)
    dsimp [x, y] at h ⊢
    linarith only [h]
  have hd₀ : (3/4) * y^2 - 3*x^2 ≤ (r 1 - r 2)^2 := by
    have h := sq_nonneg (4*x - y)
    dsimp [x, y] at h ⊢
    linarith only [h]
  have hb : ∑ j, b j = 1 := by simp [b, fExtensionBase, Fin.sum_univ_three]; ring
  have hb₁ : 0 ≤ b 1 ∧ b 1 ≤ 1/2 := by dsimp [b, fExtensionBase]; constructor <;> linarith
  have hbs : b 0 + b 1 = 1-l := by dsimp [b,fExtensionBase]; ring
  have hprod : b 0*b 1 ≤ 1/4 := by
    have hp := mul_nonneg hl₀ (show 0 ≤ 2-l by linarith)
    have heq := congrArg (fun x : ℝ => x^2) hbs
    linarith only [sq_nonneg (b 0 - b 1), heq, hp]
  have hV : (1/6) * facetVariance b r ≤ (61/1000) * x ^ 2 + ((7/36)*l) * y ^ 2 := by
    rw [facetVariance_eq_pairs hb hr]
    have hd' := mul_le_mul_of_nonneg_left hd (mul_nonneg hb₁.1 hl₀)
    have hc₀ : (b 0 * b 1 + 4 * b 1 * l) / 6 ≤ 61 / 1000 := by
      have hl := mul_le_mul_of_nonneg_right hb₁.2 hl₀
      linarith only [hprod, hl, hl₁]
    have hc₁ : (b 0 * l + (4/3) * b 1 * l) / 6 ≤ (7/36)*l := by
      have h := mul_le_mul_of_nonneg_right hb₁.2 hl₀
      have heq := congrArg (fun x : ℝ => x*l) hbs
      linarith only [h, heq, sq_nonneg l]
    have hx := mul_le_mul_of_nonneg_right hc₀ (sq_nonneg x)
    have hy := mul_le_mul_of_nonneg_right hc₁ (sq_nonneg y)
    have hb₂ : b 2 = l := rfl
    simp only [facetPairForm, Matrix.cons_val, hb₂]
    change (1/6) * (b 0*b 1*x^2+b 0*l*y^2+b 1*l*(r 1-r 2)^2) ≤ _
    linarith only [hd', hx, hy]
  have heSq : e ^ 2 ≤ 1/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr he₁) (show 0 ≤ 1/2+e by linarith)]
  have hw₀ : 33/400 ≤ w₀ := by dsimp [w₀]; linarith only [heSq, sq_nonneg l]
  have hw₂ : -(17/250) * l ≤ w₂ := by
    dsimp [w₂]
    nlinarith only [mul_le_mul_of_nonneg_left he₁ hl₀, mul_le_mul_of_nonneg_left hl₁ hl₀]
  have hw₀' : 61/1000 ≤ w₀ + 4*w₂ := by linarith only [hw₀, hw₂, hl₁]
  have hw₁' : (7/36)*l ≤ w₁ + (4/3)*w₂ := by
    dsimp [w₁, w₂]
    nlinarith only [mul_le_mul_of_nonneg_left he₁ hl₀, mul_le_mul_of_nonneg_left hl₁ hl₀, hl₀]
  refine hV.trans ?_
  change (61/1000) * x^2 + ((7/36)*l) * y^2 ≤ w₀*x^2 + w₁*y^2 + w₂*(r 1 - r 2)^2
  rcases le_total 0 w₂ with hc | hc
  · have hw₂U : w₂ ≤ (7/50)*l := by
      dsimp [w₂]
      nlinarith only [mul_nonneg hl₀ he₀, sq_nonneg l]
    have h0 : 61/1000 ≤ w₀ - 3*w₂ := by
      rcases eq_or_lt_of_le hl₀ with rfl | hl
      · dsimp [w₂] at *
        linarith only [hw₀]
      · have he : e ≤ 7/18 := by
          have h := nonneg_of_mul_nonneg_right (show 0 ≤ l * (7/25+(0:ℝ)-(18/25)*e-l) by
            dsimp [w₂] at hc; linarith only [hc]) hl
          linarith only [h, hl₀]
        have hs : e^2 ≤ (7/18:ℝ)^2 := pow_le_pow_left₀ he₀ he 2
        have hw : (11/100)*(1-(7/18:ℝ)^2) ≤ w₀ := by
          dsimp [w₀]
          linarith only [hs, sq_nonneg l]
        linarith only [hw, hw₂U, hl₁]
    have h1 : (7/36)*l ≤ w₁ + (3/4)*w₂ := by
      dsimp [w₁,w₂]
      nlinarith only [mul_nonneg hl₀ he₀, mul_le_mul_of_nonneg_left hl₁ hl₀, hl₀]
    have hh := mul_le_mul_of_nonneg_left hd₀ hc
    linarith only [mul_le_mul_of_nonneg_right h0 (sq_nonneg x),
      mul_le_mul_of_nonneg_right h1 (sq_nonneg y), hh]
  · have h₀ := mul_le_mul_of_nonneg_right hw₀' (sq_nonneg x)
    have h₁ := mul_le_mul_of_nonneg_right hw₁' (sq_nonneg y)
    have h₂ := mul_le_mul_of_nonpos_left hd hc
    linarith only [h₀, h₁, h₂]

/-- Lemma 4.1 on every extended balanced slab, including its two endpoints. -/
theorem fExtension_wide_cone_gap {l e p s z : ℝ} (hl₀ : 74/4096 ≤ l) (hl₁ : l ≤ 7/125)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2)
    (hx : FacetRatioCone (1/48) (balancedRow p s z)) :
    0 ≤ balancedFacetGap criticalQ fExtensionWeight l e p s z := by
  let b := fExtensionBase l e
  let π := balancedPi fExtensionWeight e
  have hL : 0 ≤ l := by linarith
  have hL₁ : l ≤ 1 := by linarith
  have hb : ∑ j, b j = 1 := by simp [b, fExtensionBase, Fin.sum_univ_three]; ring
  have hb₀ : ∀ j, 0 ≤ b j := by
    intro j
    fin_cases j <;> simp [b, fExtensionBase] <;> linarith
  have he : |e| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  have hπ : IsSimplex π := isSimplex_balancedPi (by norm_num [fExtensionWeight])
    (by norm_num [fExtensionWeight]) he
  have hπsum : π 3 + (∑ j : Fin 3, π j.castSucc) = 1 := by
    simpa [Fin.sum_univ_castSucc, add_comm, show Fin.last 3 = (3 : Fin 4) by decide] using hπ.2
  have hγ : facetWeight π b = balancedGamma fExtensionWeight l := fExtension_gamma l e
  have hγ₀ (j : Fin 3) : 0 ≤ facetWeight π b j := by
    rw [hγ]
    exact balancedGamma_nonneg (by norm_num [fExtensionWeight])
      (by norm_num [fExtensionWeight]) hL hL₁ j
  have hγhi : ∀ j, facetWeight π b j ≤ 16 * b j := by
    rw [hγ]
    intro j
    fin_cases j <;> norm_num [balancedGamma, b, fExtensionBase, fExtensionWeight] <;> linarith
  have hM : FacetConeMoments b π (facetWeight π b) (1/6) 16 := by
    refine ⟨hb, hb₀, hπsum, hπ.1, ?_, hγ₀, hγhi, fun y => facet_moment_first π b y hπsum, ?_⟩
    · rw [hγ]
      exact balancedGamma_sum _ _
    · intro r hr
      have eq := facet_moment_second π b r hπsum hb
      rw [hr, zero_pow (by decide), mul_zero, sub_zero] at eq
      rw [eq]
      exact fExtension_pair_bound hL hl₁ he₀ he₁ r hr
  apply (weightedRow_balancedFacet_iff _ _ _ _ _ _ _).1
  have hc := facetCritical_cone_of_budget (U := 576/529) (hm := hM) (hx := hx)
    (by norm_num) (by norm_num)
    (by
      convert facetCritical_inverse_square (R := 1/24) (by norm_num) (by norm_num) using 1 <;>
        norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hγ, fExtension_profile] at hc
  exact hc

theorem fExtension_cone_gap {l e p s z : ℝ} (hl₀ : 74/4096 ≤ l) (hl₁ : l ≤ 7/125)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hx : FacetRatioCone (1/256) (balancedRow p s z)) :
    0 ≤ balancedFacetGap criticalQ fExtensionWeight l e p s z :=
  fExtension_wide_cone_gap hl₀ hl₁ he₀ he₁ ⟨hx.1, fun i j => (hx.2 i j).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))⟩

end

end HlawkaSchatten.BelowExponent
