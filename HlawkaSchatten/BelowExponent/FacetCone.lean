/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetTaylor
public import HlawkaSchatten.BelowExponent.Interpolation

/-! The first and second moment conditions for the adaptive facet cone. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def facetMean (b y : Row) : ℝ := ∑ j, b j * y j

def facetOther (b y : Row) (j : Fin 3) : ℝ :=
  (∑ i, y i) - y j - facetMean b y

def facetVariance (b r : Row) : ℝ := ∑ j, b j * r j ^ 2

def facetPairForm (w r : Row) : ℝ :=
  w 0 * (r 0 - r 1) ^ 2 + w 1 * (r 0 - r 2) ^ 2 + w 2 * (r 1 - r 2) ^ 2

/-- The three pair weights \(b_j b_k\) give the variance on the mean-zero plane. -/
theorem facetVariance_eq_pairs {b r : Row} (hb : ∑ j, b j = 1)
    (hr : facetMean b r = 0) :
    facetVariance b r = facetPairForm ![b 0 * b 1, b 0 * b 2, b 1 * b 2] r := by
  have h : facetVariance b r * (∑ j, b j) - (facetMean b r) ^ 2 =
      facetPairForm ![b 0 * b 1, b 0 * b 2, b 1 * b 2] r := by
    simp [facetVariance, facetMean, facetPairForm, Fin.sum_univ_succ]
    ring
  simpa [hb, hr] using h

theorem facetPairForm_lower {b w r : Row} {lam : ℝ} (hb : ∑ j, b j = 1)
    (hr : facetMean b r = 0) (h01 : lam * (b 0 * b 1) ≤ w 0)
    (h02 : lam * (b 0 * b 2) ≤ w 1) (h12 : lam * (b 1 * b 2) ≤ w 2) :
    lam * facetVariance b r ≤ facetPairForm w r := by
  rw [facetVariance_eq_pairs hb hr]
  have h01' := mul_le_mul_of_nonneg_right h01 (sq_nonneg (r 0 - r 1))
  have h02' := mul_le_mul_of_nonneg_right h02 (sq_nonneg (r 0 - r 2))
  have h12' := mul_le_mul_of_nonneg_right h12 (sq_nonneg (r 1 - r 2))
  simp [facetPairForm]
  linarith only [h01', h02', h12']

structure FacetConeMoments (b : Row) (π : Profile) (γ : Row) (lam gammaBound : ℝ) : Prop where
  base_mass : ∑ j, b j = 1
  base_nonneg : ∀ j, 0 ≤ b j
  output_mass : π 3 + (∑ j : Fin 3, π j.castSucc) = 1
  output_nonneg : ∀ s, 0 ≤ π s
  input_mass : ∑ j, γ j = 1
  input_nonneg : ∀ j, 0 ≤ γ j
  input_dom : ∀ j, γ j ≤ gammaBound * b j
  first_eq : ∀ y : Row, π 3 * facetMean b y + (∑ j : Fin 3, π j.castSucc * facetOther b y j) =
    ∑ j, γ j * y j
  second_lower : ∀ r : Row, facetMean b r = 0 →
    lam * facetVariance b r ≤
      (∑ j, γ j * r j ^ 2) - (∑ j : Fin 3, π j.castSucc * facetOther b r j ^ 2)

private theorem facetOther_abs_le {b r : Row} {ρ : ℝ}
    (hm : facetMean b r = 0) (hr : ∀ j, |r j| ≤ ρ) (j : Fin 3) :
    |facetOther b r j| ≤ 2 * ρ := by
  have H₀ := abs_le.mp (hr 0)
  have H₁ := abs_le.mp (hr 1)
  have H₂ := abs_le.mp (hr 2)
  rw [abs_le]
  fin_cases j <;> simp [facetOther, hm, Fin.sum_univ_succ] <;> constructor <;> linarith

private theorem max_cube_le {u R : ℝ} (hu : |u| ≤ R) :
    max u 0 ^ 3 ≤ R * u ^ 2 := by
  rcases le_total 0 u with h | h
  · rw [max_eq_left h, pow_succ, mul_comm (u ^ 2) u]
    exact mul_le_mul_of_nonneg_right (abs_le.mp hu).2 (sq_nonneg _)
  · rw [max_eq_right h, zero_pow (by decide)]
    exact mul_nonneg ((abs_nonneg _).trans hu) (sq_nonneg _)

private theorem sum_mul_bound {w f g : Row} {c : ℝ}
    (hw : ∀ j, 0 ≤ w j) (h : ∀ j, f j ≤ c * g j) :
    (∑ j, w j * f j) ≤ c * (∑ j, w j * g j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h j) (hw j)

/-- The normalized form of Lemma 4.1. Its proof includes the signed Taylor estimates. -/
theorem facetCone_normalized {q ρ U lam gammaBound : ℝ} {b r γ : Row} {π : Profile}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hρ₀ : 0 ≤ ρ) (hρ₁ : 2 * ρ < 1)
    (hU : (1 - 2 * ρ) ^ (q - 3) ≤ U) (hLam : 0 ≤ lam)
    (hm : FacetConeMoments b π γ lam gammaBound) (hrmean : facetMean b r = 0)
    (hr : ∀ j, |r j| ≤ ρ)
    (hgap : ρ * (1 + 2 * U) * (2 - q) * gammaBound ≤ 3 * lam) :
    π 3 + (∑ j : Fin 3, π j.castSucc * (1 + facetOther b r j) ^ q) ≤
      ∑ j, γ j * (1 + r j) ^ q := by
  let k := facetCubic q
  let c := facetQuadratic q
  let V := facetVariance b r
  let I : ℝ := ∑ j, γ j * r j ^ 2
  let O : ℝ := ∑ j : Fin 3, π j.castSucc * facetOther b r j ^ 2
  have hk : 0 ≤ k := by dsimp [k, facetCubic]; positivity
  have hc : 0 ≤ c := by dsimp [c, facetQuadratic]; positivity
  have hU₀ : 0 ≤ U := (Real.rpow_nonneg (by linarith) _).trans hU
  have hV : 0 ≤ V := Finset.sum_nonneg fun j _ =>
    mul_nonneg (hm.base_nonneg j) (sq_nonneg _)
  have hI : I ≤ gammaBound * V := by
    dsimp [I, V, facetVariance]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hm.input_dom j) (sq_nonneg _)
  have hquad : lam * V ≤ I - O := hm.second_lower r hrmean
  have hO : O ≤ gammaBound * V := by nlinarith only [hI, hquad, mul_nonneg hLam hV]
  have hIn j : -(facetRemainder q (r j)) ≤ k * ρ * r j ^ 2 := by
    have h₁ := (facetRemainder_signed hq₁ hq₂ hρ₁
      ((hr j).trans (by linarith : ρ ≤ 2 * ρ)) hU).1
    have h₂ := mul_le_mul_of_nonneg_left (max_cube_le (hr j)) hk
    linarith only [h₁, h₂]
  have hOut j : facetRemainder q (facetOther b r j) ≤
      k * U * (2 * ρ) * facetOther b r j ^ 2 := by
    have ha := facetOther_abs_le hrmean hr j
    have h₁ := (facetRemainder_signed hq₁ hq₂ hρ₁ ha hU).2
    have hn : |-(facetOther b r j)| ≤ 2 * ρ := by rwa [abs_neg]
    have h₂ := mul_le_mul_of_nonneg_left (max_cube_le hn) (mul_nonneg hk hU₀)
    rw [neg_sq] at h₂
    linarith only [h₁, h₂]
  have hi := sum_mul_bound hm.input_nonneg hIn
  simp only [mul_neg, Finset.sum_neg_distrib] at hi
  have ho := sum_mul_bound (fun j => hm.output_nonneg j.castSucc) hOut
  have hLinear := hm.first_eq r
  rw [hrmean, mul_zero, zero_add] at hLinear
  have hInput (j : Fin 3) : (1 + r j) ^ q =
      1 + q * r j + facetQuadratic q * r j ^ 2 + facetRemainder q (r j) := by
    unfold facetRemainder
    ring
  have hOutput (j : Fin 3) : (1 + facetOther b r j) ^ q =
      1 + q * facetOther b r j + facetQuadratic q * facetOther b r j ^ 2 +
        facetRemainder q (facetOther b r j) := by
    unfold facetRemainder
    ring
  have hI' := mul_le_mul_of_nonneg_left hI (mul_nonneg hk hρ₀)
  have hO' := mul_le_mul_of_nonneg_left hO
    (mul_nonneg (mul_nonneg hk hU₀) (by positivity : 0 ≤ 2 * ρ))
  have hQ' := mul_le_mul_of_nonneg_left hquad hc
  have hbudget : k * ρ * (1 + 2 * U) * gammaBound ≤ c * lam := by
    have h := mul_le_mul_of_nonneg_left hgap (show 0 ≤ q * (q - 1) / 6 by positivity)
    dsimp [k, c, facetCubic, facetQuadratic]
    linarith only [h]
  have hbudget' := mul_le_mul_of_nonneg_right hbudget hV
  simp only [hOutput, hInput, mul_add, Finset.sum_add_distrib, mul_one]
  simp_rw [mul_left_comm _ q, mul_left_comm _ (facetQuadratic q), ← Finset.mul_sum]
  change π 3 + ((∑ j : Fin 3, π j.castSucc) +
      q * (∑ j : Fin 3, π j.castSucc * facetOther b r j) + c * O +
      (∑ j : Fin 3, π j.castSucc * facetRemainder q (facetOther b r j))) ≤
      (∑ j, γ j) + q * (∑ j, γ j * r j) + c * I +
      ∑ j, γ j * facetRemainder q (r j)
  have hLin' := congrArg (q * ·) hLinear
  linarith only [hm.input_mass, hm.output_mass, hLin', hi, ho, hI', hO', hQ', hbudget']

end

end HlawkaSchatten.BelowExponent
