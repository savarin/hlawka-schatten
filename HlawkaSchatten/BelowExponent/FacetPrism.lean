/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetConeRow
public import HlawkaSchatten.BelowExponent.Exponents

/-! The affine facet weights and their exact first and second moments. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def facetWeight (π : Profile) (b : Row) (j : Fin 3) : ℝ :=
  1 - π 3 - π j.castSucc + (2 * π 3 - 1) * b j

def prismWeight (π : Profile) (slope : Row) (t : Profile) (j : Fin 3) : ℝ :=
  facetWeight π (fun i => t i.castSucc) j + slope j * t 3

def facetCap (b : Row) (d : ℝ) : Profile :=
  ![(1 - d) * b 0, (1 - d) * b 1, (1 - d) * b 2, d]

def facetPairWeight (π : Profile) (b : Row) (j k l : Fin 3) : ℝ :=
  b j * b k - (π j.castSucc + π l.castSucc) * b j -
    (π k.castSucc + π l.castSucc) * b k + π l.castSucc

private theorem facet_moment_first (π : Profile) (b y : Row)
    (hπ : π 3 + (∑ j : Fin 3, π j.castSucc) = 1) :
    π 3 * facetMean b y + ∑ j : Fin 3, π j.castSucc * facetOther b y j =
      ∑ j, facetWeight π b j * y j := by
  simp [facetMean, facetOther, facetWeight, Fin.sum_univ_succ] at *
  linear_combination (y 0 + y 1 + y 2 - (b 0 * y 0 + b 1 * y 1 + b 2 * y 2)) * hπ

private theorem facet_moment_second (π : Profile) (b r : Row)
    (hπ : π 3 + (∑ j : Fin 3, π j.castSucc) = 1) (hb : ∑ j, b j = 1) :
    (∑ j, facetWeight π b j * r j ^ 2) - π 3 * facetMean b r ^ 2 -
        (∑ j : Fin 3, π j.castSucc * facetOther b r j ^ 2) =
      facetPairForm ![facetPairWeight π b 0 1 2, facetPairWeight π b 0 2 1,
        facetPairWeight π b 1 2 0] r := by
  simp [Fin.sum_univ_succ] at hπ hb
  have hπ₂ : π 2 = 1 - π 3 - π 0 - π 1 := by linarith
  have hb₂ : b 2 = 1 - b 0 - b 1 := by linarith
  simp [facetMean, facetOther, facetWeight, facetPairForm, facetPairWeight, Fin.sum_univ_succ,
    hπ₂, hb₂]
  ring

theorem facetConeMoments_of_pairWeights {π : Profile} {b : Row} {lam gammaBound : ℝ}
    (hb : ∑ j, b j = 1) (hb₀ : ∀ j, 0 ≤ b j) (hπ : IsSimplex π)
    (hγ₀ : ∀ j, 0 ≤ facetWeight π b j)
    (hγhi : ∀ j, facetWeight π b j ≤ gammaBound * b j)
    (h01 : lam * (b 0 * b 1) ≤ facetPairWeight π b 0 1 2)
    (h02 : lam * (b 0 * b 2) ≤ facetPairWeight π b 0 2 1)
    (h12 : lam * (b 1 * b 2) ≤ facetPairWeight π b 1 2 0) :
    FacetConeMoments b π (facetWeight π b) lam gammaBound := by
  have hπsum : π 3 + (∑ j : Fin 3, π j.castSucc) = 1 := by
    have h := hπ.2
    rw [Fin.sum_univ_castSucc, show Fin.last 3 = (3 : Fin 4) by decide, add_comm] at h
    exact h
  refine ⟨hb, hb₀, hπsum, hπ.1, ?_, hγ₀, hγhi, fun y => facet_moment_first π b y hπsum, ?_⟩
  · simp [facetWeight, Fin.sum_univ_succ] at hπsum hb ⊢
    linear_combination (2 * π 3 - 1) * hb - hπsum
  · intro r hr
    have eq := facet_moment_second π b r hπsum hb
    rw [hr, zero_pow (by decide), mul_zero, sub_zero] at eq
    rw [eq]
    exact facetPairForm_lower hb hr h01 h02 h12

theorem facetCritical_one_lt : 1 < criticalQ :=
  (by norm_num : (1 : ℝ) < 1054 / 665).trans criticalQ_bracket.1

theorem facetCritical_lt_two : criticalQ < 2 :=
  criticalQ_bracket.2.trans (by norm_num)

theorem facetCritical_quarter :
    (1 - 2 * (1 / 4 : ℝ)) ^ (criticalQ - 3) = 8 / 3 := by
  rw [show (1 - 2 * (1 / 4 : ℝ)) = (2 : ℝ)⁻¹ by norm_num,
    Real.rpow_sub (by norm_num : 0 < (2 : ℝ)⁻¹), Real.inv_rpow (by norm_num),
    two_rpow_criticalQ]
  norm_num [Real.rpow_ofNat]

theorem facetCritical_inverse_square {R : ℝ} (hR₀ : 0 ≤ R) (hR₁ : R < 1) :
    (1 - R) ^ (criticalQ - 3) ≤ ((1 - R) ^ 2)⁻¹ := by
  have h := Real.rpow_le_rpow_of_exponent_ge (show 0 < 1 - R by linarith)
    (show 1 - R ≤ 1 by linarith) (show -2 ≤ criticalQ - 3 by linarith [facetCritical_one_lt])
  rwa [Real.rpow_neg (by linarith : 0 ≤ 1 - R), Real.rpow_two] at h

theorem facetCritical_cone_of_budget {b x : Row} {π : Profile} {ρ U lam gammaBound : ℝ}
    (hρ₀ : 0 ≤ ρ) (hρ₁ : 2 * ρ < 1)
    (hU : (1 - 2 * ρ) ^ (criticalQ - 3) ≤ U) (hLam : 0 ≤ lam) (hGamma : 0 ≤ gammaBound)
    (hm : FacetConeMoments b π (facetWeight π b) lam gammaBound) (hx : FacetRatioCone ρ x)
    (hgap : ρ * (1 + 2 * U) * (2 - 1054 / 665) * gammaBound ≤ 3 * lam) :
    WeightedRow criticalQ (facetBase b) π (facetWeight π b) x := by
  have hU₀ : 0 ≤ U := (Real.rpow_nonneg (by linarith) _).trans hU
  apply facetCone_weightedRow facetCritical_one_lt facetCritical_lt_two hρ₀ hρ₁ hU hLam hm hx
  have hq := sub_le_sub_left criticalQ_bracket.1.le 2
  calc
    _ ≤ ρ * (1 + 2 * U) * (2 - 1054 / 665) * gammaBound :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (by positivity)) hGamma
    _ ≤ _ := hgap

end

end HlawkaSchatten.BelowExponent
