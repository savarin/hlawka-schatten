/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic

/-! Signed Taylor remainders used at the base of an adaptive facet prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Filter Set
open scoped Topology

noncomputable section

def facetQuadratic (q : ℝ) : ℝ := q * (q - 1) / 2

def facetCubic (q : ℝ) : ℝ := q * (q - 1) * (2 - q) / 6

def facetRemainder (q u : ℝ) : ℝ :=
  (1 + u) ^ q - (1 + q * u + facetQuadratic q * u ^ 2)

private theorem iteratedDeriv_rpow_pos (q : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ => y ^ q) x =
      (∏ k ∈ Finset.range n, (q - (k : ℝ))) * x ^ (q - (n : ℝ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    let c : ℝ := ∏ k ∈ Finset.range n, (q - (k : ℝ))
    have heq : iteratedDeriv n (fun y : ℝ => y ^ q) =ᶠ[𝓝 x]
        fun y => c * y ^ (q - (n : ℝ)) :=
      (eventually_gt_nhds hx).mono fun _ hy => ih hy
    rw [heq.deriv_eq]
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := q - (n : ℝ))
      (Or.inl hx.ne')).const_mul c
    rw [hd.deriv, Finset.prod_range_succ, Nat.cast_succ]
    change c * ((q - (n : ℝ)) * x ^ (q - (n : ℝ) - 1)) =
      c * (q - (n : ℝ)) * x ^ (q - ((n : ℝ) + 1))
    rw [show q - ((n : ℝ) + 1) = q - (n : ℝ) - 1 by ring, mul_assoc]

/-- The quadratic expansion of \(x^q\) at \(1\), with its exact cubic Lagrange remainder. -/
theorem facetRemainder_lagrange (q : ℝ) {u : ℝ} (hu : -1 < u) :
    ∃ z ∈ uIcc (1 : ℝ) (1 + u),
      facetRemainder q u = -facetCubic q * z ^ (q - 3) * u ^ 3 := by
  by_cases hz : u = 0
  · subst u
    exact ⟨1, by simp, by simp [facetRemainder]⟩
  have hne : (1 : ℝ) ≠ 1 + u := by
    intro h
    exact hz (by linarith)
  have hpos : ∀ z ∈ uIcc (1 : ℝ) (1 + u), 0 < z := by
    intro z h
    exact (lt_min (by norm_num) (by linarith)).trans_le h.1
  have hcont : ContDiffOn ℝ 3 (fun y : ℝ => y ^ q) (uIcc (1 : ℝ) (1 + u)) :=
    fun _ hz => (Real.contDiffAt_rpow_const_of_ne (hpos _ hz).ne').contDiffWithinAt
  obtain ⟨z, hz', h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hcont
  refine ⟨z, Ioo_subset_Icc_self hz', ?_⟩
  have hbase : (1 : ℝ) ∈ uIcc (1 : ℝ) (1 + u) := left_mem_uIcc
  have hderiv (n : ℕ) :
      iteratedDerivWithin n (fun y : ℝ => y ^ q) (uIcc 1 (1 + u)) 1 =
        ∏ k ∈ Finset.range n, (q - (k : ℝ)) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (Real.contDiffAt_rpow_const_of_ne one_ne_zero) hbase,
      iteratedDeriv_rpow_pos q n zero_lt_one, Real.one_rpow, mul_one]
  rw [taylor_within_apply, iteratedDeriv_rpow_pos q 3 (hpos _ (Ioo_subset_Icc_self hz'))] at h
  norm_num [Finset.sum_range_succ, Finset.prod_range_succ, hderiv] at h
  unfold facetRemainder facetCubic facetQuadratic
  linarith only [h]

/-- The positive increment only needs the unit derivative bound. The negative increment
uses the derivative bound at the leftmost permitted point. -/
theorem facetRemainder_signed {q u R U : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : R < 1) (hu : |u| ≤ R) (hU : (1 - R) ^ (q - 3) ≤ U) :
    -facetCubic q * max u 0 ^ 3 ≤ facetRemainder q u ∧
      facetRemainder q u ≤ facetCubic q * U * max (-u) 0 ^ 3 := by
  obtain ⟨z, hz, heq⟩ := facetRemainder_lagrange q (show -1 < u by
    linarith only [(abs_le.mp hu).1, hR])
  have hc : 0 ≤ facetCubic q := by
    dsimp [facetCubic]
    positivity
  have hz₀ : 0 < z := by
    have hu₀ := (abs_le.mp hu).1
    exact (lt_min (by norm_num) (by linarith)).trans_le hz.1
  have hp : 0 ≤ z ^ (q - 3) := Real.rpow_nonneg hz₀.le _
  have he : q - 3 ≤ 0 := by linarith
  rw [heq]
  rcases le_total 0 u with hu₀ | hu₀
  · have hz₁ : 1 ≤ z := by
      simpa only [min_eq_left (show (1:ℝ) ≤ 1 + u by linarith)] using hz.1
    have hpow := Real.rpow_le_rpow_of_nonpos zero_lt_one hz₁ he
    rw [Real.one_rpow] at hpow
    rw [max_eq_left hu₀, max_eq_right (neg_nonpos.mpr hu₀), zero_pow (by decide), mul_zero]
    have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc)
      (pow_nonneg hu₀ 3)
    exact ⟨by linarith only [hbound], by
      rw [neg_mul, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hc hp) (pow_nonneg hu₀ 3))⟩
  · have hzR : 1 - R ≤ z := by
      have hmin : 1 - R ≤ min 1 (1 + u) :=
        le_min (by linarith [abs_nonneg u]) (by linarith [(abs_le.mp hu).1])
      exact hmin.trans hz.1
    have hpow := (Real.rpow_le_rpow_of_nonpos (show 0 < 1 - R by linarith) hzR he).trans hU
    rw [max_eq_right hu₀, max_eq_left (neg_nonneg.mpr hu₀), zero_pow (by decide), mul_zero,
      show -facetCubic q * z ^ (q - 3) * u ^ 3 =
        facetCubic q * z ^ (q - 3) * (-u) ^ 3 by ring]
    exact ⟨mul_nonneg (mul_nonneg hc hp) (pow_nonneg (neg_nonneg.mpr hu₀) 3),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc)
        (pow_nonneg (neg_nonneg.mpr hu₀) 3)⟩

end

end HlawkaSchatten.BelowExponent
