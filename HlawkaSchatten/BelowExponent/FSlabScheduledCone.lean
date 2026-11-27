/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCone
public import HlawkaSchatten.BelowExponent.FSlabWeights
import all HlawkaSchatten.BelowExponent.FSlabCone
import all HlawkaSchatten.BelowExponent.FacetPrism
import Batteries.Tactic.OpenPrivate

/-! Equality-cone bounds for the four weights on the closed F slab endpoints. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open private fExtension_profile from HlawkaSchatten.BelowExponent.FSlabCone
open private facet_moment_first facet_moment_second from HlawkaSchatten.BelowExponent.FacetPrism

private theorem fScheduled_variance {l e μ : ℝ} (hl : 0 ≤ l) (hL : l ≤ 7/125)
    (he : 0 ≤ e) (hE : e ≤ 1/2) (hm : 21/100 ≤ μ) (hM : μ ≤ 27/100) (hml : 37/200 ≤ μ-l)
    (r : Row) (hr : facetMean (fExtensionBase l e) r = 0) :
    (1/8)*facetVariance (fExtensionBase l e) r ≤
      facetPairForm ![facetPairWeight (balancedPi μ e) (fExtensionBase l e) 0 1 2,
        facetPairWeight (balancedPi μ e) (fExtensionBase l e) 0 2 1,
        facetPairWeight (balancedPi μ e) (fExtensionBase l e) 1 2 0] r := by
  let x := r 0-r 1
  let y := r 0-r 2
  let b := fExtensionBase l e
  let w₀ := ((1-2*μ)*(1-e^2)+l^2)/4
  let w₁ := l*(μ+(1-μ)*e-l)/2
  let w₂ := l*(μ-(1-μ)*e-l)/2
  have hw : ![facetPairWeight (balancedPi μ e) b 0 1 2,
      facetPairWeight (balancedPi μ e) b 0 2 1,
      facetPairWeight (balancedPi μ e) b 1 2 0] = ![w₀,w₁,w₂] := by
    funext j
    fin_cases j <;> norm_num [facetPairWeight, balancedPi, fExtensionBase, b, w₀,w₁,w₂,Fin.castSucc] <;> ring
  change (1/8)*facetVariance b r ≤ _
  rw [hw]
  have hd : (r 1-r 2)^2 ≤ 4*x^2+(4/3)*y^2 := by
    have h := sq_nonneg (3*x+y)
    dsimp [x,y] at h ⊢
    linarith only [h]
  have hd' : (3/4)*y^2-3*x^2 ≤ (r 1-r 2)^2 := by
    have h := sq_nonneg (4*x-y)
    dsimp [x,y] at h ⊢
    linarith only [h]
  have hb : ∑ i, b i = 1 := by simp [b,fExtensionBase,Fin.sum_univ_three]; ring
  have hb₁ : 0 ≤ b 1 ∧ b 1 ≤ 1/2 := by dsimp [b,fExtensionBase]; constructor <;> linarith
  have hbs : b 0+b 1 = 1-l := by dsimp [b,fExtensionBase]; ring
  have hbp : b 0*b 1 ≤ 1/4 := by
    have heq := congrArg (fun t : ℝ => t^2) hbs
    have hh := mul_nonneg hl (show 0 ≤ 2-l by linarith)
    linarith only [sq_nonneg (b 0-b 1), heq, hh]
  have hV : (1/8)*facetVariance b r ≤ (23/500)*x^2+(7/48)*l*y^2 := by
    rw [facetVariance_eq_pairs hb hr]
    have hd'' := mul_le_mul_of_nonneg_left hd (mul_nonneg hb₁.1 hl)
    have hx : (b 0*b 1+4*b 1*l)/8 ≤ 23/500 := by
      have h := mul_le_mul_of_nonneg_right hb₁.2 hl
      linarith only [hbp, h, hL]
    have hy : (b 0*l+(4/3)*b 1*l)/8 ≤ (7/48)*l := by
      have h := mul_le_mul_of_nonneg_right hb₁.2 hl
      have heq := congrArg (fun t : ℝ => t*l) hbs
      linarith only [h, heq, sq_nonneg l]
    have hX := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    have hY := mul_le_mul_of_nonneg_right hy (sq_nonneg y)
    have hb₂ : b 2 = l := rfl
    simp only [facetPairForm, Matrix.cons_val, hb₂]
    change (1/8)*(b 0*b 1*x^2+b 0*l*y^2+b 1*l*(r 1-r 2)^2) ≤ _
    linarith only [hd'',hX,hY]
  have he2 : e^2 ≤ 1/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hE) (show 0 ≤ 1/2+e by linarith)]
  have hw₀ : 69/800 ≤ w₀ := by
    have h := mul_le_mul (show (23/50 : ℝ) ≤ 1-2*μ by linarith) (show 3/4 ≤ 1-e^2 by linarith)
      (by norm_num) (by linarith)
    dsimp [w₀]
    linarith only [h, sq_nonneg l]
  have heμ : (1-μ)*e ≤ 79/200 := by
    have h := mul_le_mul (show 1-μ ≤ 79/100 by linarith) hE he (by norm_num)
    linarith only [h]
  have heμ₀ : 0 ≤ (1-μ)*e := mul_nonneg (by linarith) he
  have hw₂U : w₂ ≤ (27/200)*l := by
    dsimp [w₂]
    have h := mul_le_mul_of_nonneg_left (show μ-(1-μ)*e-l ≤ 27/100 by linarith) hl
    linarith only [h]
  have hw₂L : -(21/200)*l ≤ w₂ := by
    dsimp [w₂]
    have h := mul_le_mul_of_nonneg_left (show -(21/100:ℝ) ≤ μ-(1-μ)*e-l by linarith) hl
    linarith only [h]
  refine hV.trans ?_
  change (23/500)*x^2+(7/48)*l*y^2 ≤ w₀*x^2+w₁*y^2+w₂*(r 1-r 2)^2
  rcases le_total 0 w₂ with h | h
  · have hx : 23/500 ≤ w₀-3*w₂ := by linarith only [hw₀, hw₂U, hL]
    have hy : (7/48)*l ≤ w₁+(3/4)*w₂ := by
      have h := mul_le_mul_of_nonneg_left (show (7/24:ℝ) ≤ (7/4)*(μ-l)+(1/4)*((1-μ)*e) by linarith) hl
      dsimp [w₁,w₂]
      linarith only [h]
    have hX := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    have hY := mul_le_mul_of_nonneg_right hy (sq_nonneg y)
    have hh := mul_le_mul_of_nonneg_left hd' h
    linarith only [hX,hY,hh]
  · have hx : 23/500 ≤ w₀+4*w₂ := by linarith only [hw₀, hw₂L, hL]
    have hy : (7/48)*l ≤ w₁+(4/3)*w₂ := by
      have h := mul_le_mul_of_nonneg_left (show (7/24:ℝ) ≤ (7/3)*(μ-l)-(1/3)*((1-μ)*e) by linarith) hl
      dsimp [w₁,w₂]
      linarith only [h]
    have hX := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    have hY := mul_le_mul_of_nonneg_right hy (sq_nonneg y)
    have hh := mul_le_mul_of_nonpos_left hd h
    linarith only [hX,hY,hh]

theorem fScheduled_cone {l e μ : ℝ} (hl : 74/4096 ≤ l) (hL : l ≤ 7/125)
    (he : 0 ≤ e) (hE : e ≤ 1/2) (hm : 21/100 ≤ μ) (hM : μ ≤ 27/100) (hml : 37/200 ≤ μ-l)
    {x : Row} (hx : FacetRatioCone (1/64) x) :
    WeightedRow criticalQ (balancedProfile l e l) (balancedPi μ e) (balancedGamma μ l) x := by
  let b := fExtensionBase l e
  let π := balancedPi μ e
  have hl₀ : 0 ≤ l := by linarith
  have hl₁ : l ≤ 1 := by linarith
  have hμ₀ : 0 ≤ μ := by linarith
  have hμ₁ : μ ≤ 1 := by linarith
  have hπ : IsSimplex π := isSimplex_balancedPi hμ₀ hμ₁ (by rw [abs_of_nonneg he]; linarith)
  have hb : ∑ j, b j = 1 := by simp [b,fExtensionBase,Fin.sum_univ_three]; ring
  have hb₀ : ∀ j, 0 ≤ b j := by intro j; fin_cases j <;> simp [b,fExtensionBase] <;> linarith
  have hπsum : π 3 + (∑ j : Fin 3, π j.castSucc) = 1 := by
    simpa [Fin.sum_univ_castSucc, add_comm, show Fin.last 3 = (3 : Fin 4) by decide] using hπ.2
  have hγ : facetWeight π b = balancedGamma μ l := by
    funext j
    fin_cases j <;> simp [facetWeight,π,balancedPi,b,fExtensionBase,balancedGamma,Fin.castSucc] <;> ring
  have hγpos (j : Fin 3) : 0 ≤ facetWeight π b j := by rw [hγ]; exact balancedGamma_nonneg hμ₀ hμ₁ hl₀ hl₁ j
  have hγhi (j : Fin 3) : facetWeight π b j ≤ 16*b j := by
    rw [hγ]
    have hmul := mul_nonneg hμ₀ (sub_nonneg.mpr hl₁)
    have hmul' := mul_le_mul_of_nonneg_left (show 1-l ≤ 1 by linarith) hμ₀
    fin_cases j <;> norm_num [balancedGamma,b,fExtensionBase] <;>
      linarith only [hmul,hmul',hl,hL,he,hE,hM]
  have hMoments : FacetConeMoments b π (facetWeight π b) (1/8) 16 := by
    refine ⟨hb,hb₀,hπsum,hπ.1,?_,hγpos,hγhi,fun y => facet_moment_first π b y hπsum,?_⟩
    · rw [hγ]; exact balancedGamma_sum _ _
    · intro r hr
      have eq := facet_moment_second π b r hπsum hb
      rw [hr, zero_pow (by decide), mul_zero, sub_zero] at eq
      rw [eq]
      exact fScheduled_variance hl₀ hL he hE hm hM hml r hr
  have hc := facetCritical_cone_of_budget (U := 1024/961) (hm := hMoments) (hx := hx)
    (by norm_num) (by norm_num)
    (by convert facetCritical_inverse_square (R := 1/32) (by norm_num) (by norm_num) using 1 <;> norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hγ, fExtension_profile] at hc
  exact hc

end HlawkaSchatten.BelowExponent
