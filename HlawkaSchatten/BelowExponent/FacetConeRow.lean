/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetCone

/-! Convert the normalized facet estimate to the physical row coordinates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def facetBase (b : Row) : Profile := ![b 0, b 1, b 2, 0]

def facetFlip (x : Row) : Row := ![x 0, -x 1, -x 2]

private theorem facetFlip_involutive (x : Row) : facetFlip (facetFlip x) = x := by
  funext j
  fin_cases j <;> simp [facetFlip]

private theorem facetFlip_smul (a : ℝ) (x : Row) : facetFlip (a • x) = a • facetFlip x := by
  funext j
  fin_cases j <;> simp [facetFlip, Pi.smul_apply, smul_eq_mul]

private theorem facetEval_last (b y : Row) :
    rowEval (facetBase b) 3 (facetFlip y) = facetMean b y := by
  norm_num [rowEval, facetBase, facetFlip, facetMean, sign, partner, Fin.sum_univ_succ]

private theorem facetEval_other {b : Row} (hb : ∑ j, b j = 1) (y : Row) (j : Fin 3) :
    rowEval (facetBase b) j.castSucc (facetFlip y) = -facetOther b y j := by
  simp [Fin.sum_univ_succ] at hb
  fin_cases j
  · norm_num [rowEval, facetBase, facetFlip, facetOther, facetMean, sign, partner,
      Fin.sum_univ_succ, Fin.castSucc]
    linear_combination -(y 1 + y 2) * hb
  · norm_num [rowEval, facetBase, facetFlip, facetOther, facetMean, sign, partner,
      Fin.sum_univ_succ, Fin.castSucc]
    linear_combination -(y 0 + y 2) * hb
  · norm_num [rowEval, facetBase, facetFlip, facetOther, facetMean, sign, partner,
      Fin.sum_univ_succ, Fin.castSucc]
    linear_combination -(y 0 + y 1) * hb

private theorem facetCone_weighted_normalized {q ρ U lam gammaBound : ℝ} {b r γ : Row}
    {π : Profile} (hq₁ : 1 < q) (hq₂ : q < 2) (hρ₀ : 0 ≤ ρ) (hρ₁ : 2 * ρ < 1)
    (hU : (1 - 2 * ρ) ^ (q - 3) ≤ U) (hLam : 0 ≤ lam)
    (hm : FacetConeMoments b π γ lam gammaBound) (hrmean : facetMean b r = 0)
    (hr : ∀ j, |r j| ≤ ρ) (hgap : ρ * (1 + 2 * U) * (2 - q) * gammaBound ≤ 3 * lam) :
    WeightedRow q (facetBase b) π γ (facetFlip fun j => 1 + r j) := by
  let y : Row := fun j => 1 + r j
  have hG : facetMean b y = 1 := by
    dsimp [facetMean, y] at hrmean ⊢
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, hm.base_mass, hrmean, add_zero]
  have hK j : facetOther b y j = 1 + facetOther b r j := by
    simp [facetOther, hG, hrmean, y, Finset.sum_add_distrib]
    ring
  have hK₀ j : 0 ≤ 1 + facetOther b r j := by
    have h₀ := (abs_le.mp (hr 0)).1
    have h₁ := (abs_le.mp (hr 1)).1
    have h₂ := (abs_le.mp (hr 2)).1
    fin_cases j <;> simp [facetOther, hrmean, Fin.sum_univ_succ] <;> linarith
  have hy₀ j : 0 ≤ y j := by
    dsimp [y]
    linarith [(abs_le.mp (hr j)).1]
  have hAbs j : |facetFlip y j| = y j := by
    fin_cases j <;> simp [facetFlip, abs_of_nonneg (hy₀ _)]
  change WeightedRow q (facetBase b) π γ (facetFlip y)
  unfold WeightedRow
  rw [Fin.sum_univ_castSucc, show Fin.last 3 = (3 : Fin 4) by decide]
  simp only [facetEval_last, facetEval_other hm.base_mass, hAbs, hG, abs_one,
    Real.one_rpow, mul_one, abs_neg, hK, abs_of_nonneg (hK₀ _)]
  rw [add_comm]
  exact facetCone_normalized hq₁ hq₂ hρ₀ hρ₁ hU hLam hm hrmean hr hgap

private theorem facetCone_nonneg {q ρ U lam gammaBound : ℝ} {b y γ : Row} {π : Profile}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hρ₀ : 0 ≤ ρ) (hρ₁ : 2 * ρ < 1)
    (hU : (1 - 2 * ρ) ^ (q - 3) ≤ U) (hLam : 0 ≤ lam)
    (hm : FacetConeMoments b π γ lam gammaBound)
    (hy : ∀ j, 0 ≤ y j) (hpair : ∀ i j, y i ≤ (1 + ρ) * y j)
    (hgap : ρ * (1 + 2 * U) * (2 - q) * gammaBound ≤ 3 * lam) :
    WeightedRow q (facetBase b) π γ (facetFlip y) := by
  let G := facetMean b y
  have hG₀ : 0 ≤ G := Finset.sum_nonneg fun j _ => mul_nonneg (hm.base_nonneg j) (hy j)
  have hhigh i : y i ≤ (1 + ρ) * G := calc
    y i = ∑ j, b j * y i := by rw [← Finset.sum_mul, hm.base_mass, one_mul]
    _ ≤ ∑ j, b j * ((1 + ρ) * y j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpair i j) (hm.base_nonneg j)
    _ = (1 + ρ) * G := by simp [G, facetMean, Finset.mul_sum, mul_left_comm]
  have hlow i : G ≤ (1 + ρ) * y i := calc
    G ≤ ∑ j, b j * ((1 + ρ) * y i) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpair j i) (hm.base_nonneg j)
    _ = (1 + ρ) * y i := by rw [← Finset.sum_mul, hm.base_mass, one_mul]
  rcases hG₀.eq_or_lt with hG | hG
  · have hy0 : y = 0 := by
      funext j
      exact le_antisymm (by simpa [← hG] using hhigh j) (hy j)
    subst y
    have hzero : facetFlip (0 : Row) = 0 := by
      funext j
      fin_cases j <;> simp [facetFlip]
    rw [hzero]
    simp [WeightedRow, rowEval, Real.zero_rpow (by linarith : q ≠ 0)]
  · let r : Row := fun j => y j / G - 1
    have hrmean : facetMean b r = 0 := by
      simp only [facetMean, r, mul_sub, mul_one, Finset.sum_sub_distrib, ← mul_div_assoc,
        ← Finset.sum_div, hm.base_mass]
      change G / G - 1 = 0
      rw [div_self hG.ne', sub_self]
    have hr j : |r j| ≤ ρ := by
      rw [abs_le]
      constructor
      · have hl : (1 - ρ) * G ≤ y j := by
          by_contra! h
          have hyG : y j ≤ G := by linarith [mul_nonneg hρ₀ hG.le]
          linarith only [h, hlow j, mul_le_mul_of_nonneg_left hyG hρ₀]
        have hl' := (le_div_iff₀ hG).2 hl
        dsimp [r]
        linarith
      · have hh := (div_le_iff₀ hG).2 (hhigh j)
        dsimp [r]
        linarith
    have heq : y = G • (fun j => 1 + r j : Row) := by
      funext j
      simp [r, Pi.smul_apply, smul_eq_mul, mul_div_cancel₀, hG.ne']
    have h := facetCone_weighted_normalized hq₁ hq₂ hρ₀ hρ₁ hU hLam hm hrmean hr hgap
    rw [show facetFlip y = G • facetFlip (fun j => 1 + r j) by
      exact (congrArg facetFlip heq).trans (facetFlip_smul _ _)]
    exact (weightedRow_smul_iff hG.ne').mpr h

def FacetRatioCone (ρ : ℝ) (x : Row) : Prop :=
  ((∀ j, 0 ≤ facetFlip x j) ∨ (∀ j, facetFlip x j ≤ 0)) ∧
    ∀ i j, |facetFlip x i| ≤ (1 + ρ) * |facetFlip x j|

/-- Lemma 4.1 at a facet profile, stated on the physical row and for the prescribed weights. -/
theorem facetCone_weightedRow {q ρ U lam gammaBound : ℝ} {b γ x : Row} {π : Profile}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hρ₀ : 0 ≤ ρ) (hρ₁ : 2 * ρ < 1)
    (hU : (1 - 2 * ρ) ^ (q - 3) ≤ U) (hLam : 0 ≤ lam)
    (hm : FacetConeMoments b π γ lam gammaBound) (hx : FacetRatioCone ρ x)
    (hgap : ρ * (1 + 2 * U) * (2 - q) * gammaBound ≤ 3 * lam) :
    WeightedRow q (facetBase b) π γ x := by
  rcases hx with ⟨h | h, hratio⟩
  · have hpair i j := hratio i j
    simp_rw [abs_of_nonneg (h _)] at hpair
    simpa only [facetFlip_involutive] using
      facetCone_nonneg hq₁ hq₂ hρ₀ hρ₁ hU hLam hm h hpair hgap
  · let y := (-1 : ℝ) • facetFlip x
    have hy j : 0 ≤ y j := by simpa [y, Pi.smul_apply, smul_eq_mul] using h j
    have hpair i j : y i ≤ (1 + ρ) * y j := by
      simpa only [abs_of_nonpos (h _), y, Pi.smul_apply, smul_eq_mul, neg_one_mul] using hratio i j
    have hyx : facetFlip y = (-1 : ℝ) • x := by
      dsimp only [y]
      rw [facetFlip_smul, facetFlip_involutive]
    have hp := facetCone_nonneg hq₁ hq₂ hρ₀ hρ₁ hU hLam hm hy hpair hgap
    rw [hyx] at hp
    exact (weightedRow_smul_iff (by norm_num : (-1 : ℝ) ≠ 0)).mp hp

end

end HlawkaSchatten.BelowExponent
