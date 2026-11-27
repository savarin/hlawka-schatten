/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Center
public import HlawkaSchatten.BelowExponent.Interpolation
public import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Covariance estimates on the centre cube omitted by the E2 certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.CenterCovariance

noncomputable section

/-- Young's inequality charges a small covariance quadratically, uniformly in
the row coordinate. This is the term paid from the centre weight budget. -/
theorem small_cross_term {b s : ℝ} (hb : 0 ≤ b) (hsmall : b ≤ 1/120) (hs : 0 ≤ s) :
    criticalQ * b * s ≤ (1/5) * s ^ criticalQ + (3/8) * b ^ 2 := by
  rcases eq_or_lt_of_le hb with he | hpos
  · subst b
    simpa using (mul_nonneg (by norm_num : 0 ≤ (1/5 : ℝ)) (Real.rpow_nonneg hs criticalQ))
  have hq := critical_conjugate.symm
  have hp : 8/3 ≤ criticalP := by
    rw [hq.conjugate_eq]
    apply (le_div_iff₀ hq.sub_one_pos).2
    linarith only [criticalQ_bracket.2]
  have hbase : 0 < 5*b := by positivity
  have hrat : (1/24 : ℝ) ^ (2/3 : ℝ) ≤ 1/8 := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _)
      (by norm_num) (by norm_num : (0 : ℝ) < 3)).1
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have htail : (5*b) ^ (criticalP-2) ≤ 1/8 :=
    (Real.rpow_le_rpow_of_exponent_ge hbase (by linarith) (by linarith : 2/3 ≤ criticalP-2)).trans
      ((Real.rpow_le_rpow hbase.le (by linarith : 5*b ≤ 1/24) (by norm_num)).trans hrat)
  have hpow : (5*b)^criticalP ≤ 25*b^2/8 := calc
    _ = (5*b) ^ (2:ℝ) * (5*b)^(criticalP-2) := by
      rw [← Real.rpow_add hbase]; congr 1; ring
    _ ≤ (5*b) ^ (2:ℝ) * (1/8) := mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hbase.le _)
    _ = _ := by rw [Real.rpow_two]; ring
  have hy : s*(5*b)*criticalQ ≤ s^criticalQ + (5*b)^criticalP*(criticalQ-1) := calc
    _ ≤ (s^criticalQ/criticalQ + (5*b)^criticalP/criticalP)*criticalQ :=
      mul_le_mul_of_nonneg_right (Real.young_inequality_of_nonneg hs hbase.le hq) hq.pos.le
    _ = s^criticalQ + (5*b)^criticalP*(criticalQ/criticalP) := by
      field_simp [hq.ne_zero, critical_conjugate.ne_zero]
    _ = _ := by rw [hq.div_conj_eq_sub_one]
  have hc := mul_le_mul hpow (by linarith only [criticalQ_bracket.2] : criticalQ-1 ≤ 3/5)
    hq.sub_one_pos.le (by positivity : 0 ≤ 25*b^2/8)
  linarith only [hy, hc]

def axisBudget (d u v : ℝ) : ℝ :=
  1 - criticalQ/2 * d^2 + (3/8) * (u^2 + v^2)

private theorem budget_lower {d : ℝ} (hd : |d| ≤ 1/125) (u v : ℝ) :
    15624/15625 ≤ axisBudget d u v := by
  have hsq : d^2 ≤ (1/125 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have h := mul_le_mul_of_nonneg_right (by linarith only [criticalQ_bracket.2] : criticalQ/2 ≤ 1)
    (sq_nonneg d)
  unfold axisBudget
  linarith only [hsq, h, sq_nonneg u, sq_nonneg v]

private theorem row_square_absorbed {x γ : ℝ} (hx : |x| ≤ 1) (hγ : 15624/15625 ≤ γ) :
    criticalQ/2*(1+1/120)*x^2 + (1/5)*|x|^criticalQ ≤ γ*|x|^criticalQ := by
  have hq := critical_conjugate.symm
  have hs : x^2 ≤ |x|^criticalQ := by
    rw [← sq_abs, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hx hq.nonneg
      (by linarith only [criticalQ_bracket.2])
  have hfactor : criticalQ/2*(1+1/120) + 1/5 ≤ γ := by
    linarith only [criticalQ_bracket.2, hγ]
  have h₁ := mul_le_mul_of_nonneg_left hs
    (by have := hq.pos; positivity : 0 ≤ criticalQ/2*(1+1/120))
  have h₂ := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (abs_nonneg x) criticalQ)
  linarith only [h₁, h₂]

private theorem mixed_term {a b w : ℝ} (hw : |w| ≤ 1/120) :
    2*w*a*b ≤ (1/120)*(a^2+b^2) := by
  have ha : w*a*b ≤ |w| * |a| * |b| := by simpa only [abs_mul] using le_abs_self (w*a*b)
  have hs := sq_nonneg (|a| - |b|)
  have h : 2 * |a| * |b| ≤ a^2+b^2 := by nlinarith only [hs, sq_abs a, sq_abs b]
  nlinarith only [ha, mul_le_mul_of_nonneg_left h (abs_nonneg w),
    mul_le_mul_of_nonneg_right hw (add_nonneg (sq_nonneg a) (sq_nonneg b))]

private theorem linear_term {a u : ℝ} (hu : |u| ≤ 1/120) :
    criticalQ*u*a ≤ (1/5)*|a|^criticalQ + (3/8)*u^2 := by
  have h : u*a ≤ |u| * |a| := by simpa only [abs_mul] using le_abs_self (u*a)
  have hc := small_cross_term (abs_nonneg u) hu (abs_nonneg a)
  rw [sq_abs] at hc
  linarith only [mul_le_mul_of_nonneg_left h critical_conjugate.symm.nonneg, hc]

/-- The covariance estimate on a chart whose largest coordinate is one. -/
theorem chart_majorant {d e f u v w a b A B : ℝ} (hu : |u| ≤ 1/120)
    (hv : |v| ≤ 1/120) (hw : |w| ≤ 1/120) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hA : 15624/15625 ≤ A) (hB : 15624/15625 ≤ B) :
    1 + criticalQ/2 * ((1-d^2) + (1-e^2)*a^2 + (1-f^2)*b^2 +
      2*(u*a+v*b+w*a*b) - 1) ≤ axisBudget d u v + A*|a|^criticalQ + B*|b|^criticalQ := by
  have hq : 0 ≤ criticalQ/2 := by have := critical_conjugate.symm.pos; positivity
  have hh := mul_le_mul_of_nonneg_left (mixed_term (a := a) (b := b) hw) hq
  have he := mul_nonneg hq (sq_nonneg (e*a))
  have hf := mul_nonneg hq (sq_nonneg (f*b))
  unfold axisBudget
  linarith only [hh, he, hf, linear_term (a := a) hu, linear_term (a := b) hv,
    row_square_absorbed ha hA, row_square_absorbed hb hB]

def mean (t : Profile) : Row :=
  ![2*(t 1+t 2)-1, 2*(t 1+t 3)-1, 2*(t 2+t 3)-1]

def cov (m : Row) : Row :=
  ![m 0-m 1*m 2, m 1-m 2*m 0, m 2-m 0*m 1]

def budgets (m : Row) : Row :=
  ![axisBudget (m 0) (cov m 2) (cov m 1), axisBudget (m 1) (cov m 2) (cov m 0),
    axisBudget (m 2) (cov m 1) (cov m 0)]

def variance (m x : Row) : ℝ :=
  (1-(m 0)^2)*(x 0)^2 + (1-(m 1)^2)*(x 1)^2 + (1-(m 2)^2)*(x 2)^2 +
  2*((cov m 2)*x 0*x 1 + (cov m 1)*x 0*x 2 + (cov m 0)*x 1*x 2)

private theorem mean_bound {t : Profile} (hc : ∀ s, |t s - 1/4| ≤ 1/500)
    (j : Fin 3) : |mean t j| ≤ 1/125 := by
  have h₁ := abs_le.mp (hc 1)
  have h₂ := abs_le.mp (hc 2)
  have h₃ := abs_le.mp (hc 3)
  fin_cases j <;> apply abs_le.mpr <;> simp [mean] <;> constructor <;> linarith

private theorem cov_bound_aux {x y z : ℝ} (hx : |x| ≤ 1/125) (hy : |y| ≤ 1/125)
    (hz : |z| ≤ 1/125) : |x-y*z| ≤ 1/120 := by
  have hprod := mul_le_mul hy hz (abs_nonneg z) (by norm_num)
  calc
    _ ≤ |x| + |y*z| := abs_sub _ _
    _ ≤ _ := by rw [abs_mul]; linarith only [hx, hprod]

private theorem cov_bound {m : Row} (h : ∀ i, |m i| ≤ 1/125) (i : Fin 3) :
    |cov m i| ≤ 1/120 := by
  fin_cases i
  · exact cov_bound_aux (h 0) (h 1) (h 2)
  · exact cov_bound_aux (h 1) (h 2) (h 0)
  · exact cov_bound_aux (h 2) (h 0) (h 1)

private theorem cov_sq {x y z : ℝ} (hz : |z| ≤ 1/125) :
    (x-y*z)^2 ≤ (101/100)*x^2 + (1/100)*y^2 := by
  have hsq : z^2 ≤ (1/125 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  nlinarith only [mul_le_mul_of_nonneg_left hsq (sq_nonneg y),
    sq_nonneg (x+100*(y*z)), sq_nonneg y]

private theorem budgets_lower {m : Row} (h : ∀ i, |m i| ≤ 1/125) (j : Fin 3) :
    15624/15625 ≤ budgets m j := by
  fin_cases j
  · exact budget_lower (h 0) _ _
  · exact budget_lower (h 1) _ _
  · exact budget_lower (h 2) _ _

private theorem budgets_sum {m : Row} (h : ∀ i, |m i| ≤ 1/125) :
    ∑ j, budgets m j ≤ 3 := by
  have h₀ : (cov m 0)^2 ≤ (101/100)*(m 0)^2 + (1/100)*(m 1)^2 := cov_sq (h 2)
  have h₁ : (cov m 1)^2 ≤ (101/100)*(m 1)^2 + (1/100)*(m 2)^2 := cov_sq (h 0)
  have h₂ : (cov m 2)^2 ≤ (101/100)*(m 2)^2 + (1/100)*(m 0)^2 := cov_sq (h 1)
  have hq : 153/200 ≤ criticalQ/2 := by linarith only [criticalQ_bracket.1]
  have hsum := mul_le_mul_of_nonneg_right hq
    (add_nonneg (add_nonneg (sq_nonneg (m 0)) (sq_nonneg (m 1))) (sq_nonneg (m 2)))
  simp [Fin.sum_univ_three, budgets, axisBudget]
  linarith only [h₀, h₁, h₂, hsum]

private theorem variance_eq {t : Profile} (ht : IsSimplex t) (x : Row) :
    ∑ s, (1/2-t s) * (2*rowEval t s x)^2 = variance (mean t) x := by
  have hs := ht.2
  simp only [Fin.sum_univ_four] at hs
  have h₃ : t 3 = 1 - t 0 - t 1 - t 2 := by linarith only [hs]
  simp (config := { decide := true }) [rowEval, mean, cov, variance, sign, partner,
    Fin.sum_univ_four, Fin.sum_univ_three, h₃]
  ring

private theorem power_tangent (y : ℝ) :
    3*|y|^criticalQ ≤ 1 + criticalQ/2*((2*y)^2-1) := by
  have hp : ((2*y)^2)^(criticalQ/2) = 3*|y|^criticalQ := calc
    _ = (|2*y|^(2:ℝ))^(criticalQ/2) := by rw [Real.rpow_two, sq_abs]
    _ = |2*y|^criticalQ := by rw [← Real.rpow_mul (abs_nonneg _), show 2*(criticalQ/2)=criticalQ by ring]
    _ = _ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
        Real.mul_rpow (by norm_num) (abs_nonneg _), two_rpow_criticalQ]
  have h := rpow_one_add_le_one_add_mul_self
    (by linarith only [sq_nonneg (2*y)] : -1 ≤ (2*y)^2-1)
    (by have := critical_conjugate.symm.pos; positivity : 0 ≤ criticalQ/2)
    (by linarith only [criticalQ_bracket.2])
  rwa [show 1+((2*y)^2-1) = (2*y)^2 by ring, hp] at h

private theorem weighted_tangent {t : Profile} (ht : IsSimplex t) (hw : ∀ s, 0 ≤ 1/2-t s)
    (hs : ∑ s, (1/2-t s) = 1) (x : Row) :
    3*(∑ s, (1/2-t s)*|rowEval t s x|^criticalQ) ≤ 1 + criticalQ/2*(variance (mean t) x - 1) := by
  calc
    _ = ∑ s, (1/2-t s)*(3*|rowEval t s x|^criticalQ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ s, (1/2-t s)*(1+criticalQ/2*((2*rowEval t s x)^2-1)) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (power_tangent _) (hw s)
    _ = _ := by
      have piece (s : Fin 4) : (1/2-t s)*(1+criticalQ/2*((2*rowEval t s x)^2-1)) =
          (1-criticalQ/2)*(1/2-t s) + criticalQ/2*((1/2-t s)*(2*rowEval t s x)^2) := by ring
      simp_rw [piece]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, variance_eq ht]
      ring

private theorem chart_bound {m x : Row} (hm : ∀ i, |m i| ≤ 1/125) (k : Fin 3)
    (hk : x k = 1) (hx : ∀ j, |x j| ≤ 1) :
    1 + criticalQ/2*(variance m x - 1) ≤ ∑ j, budgets m j * |x j|^criticalQ := by
  have covs := cov_bound hm
  have lower := budgets_lower hm
  fin_cases k
  · change x 0 = 1 at hk
    have h := chart_majorant (d := m 0) (e := m 1) (f := m 2)
      (covs 2) (covs 1) (covs 0) (hx 1) (hx 2) (lower 1) (lower 2)
    simp only [Fin.sum_univ_three, variance, hk, one_pow, mul_one, abs_one, Real.one_rpow,
      show budgets m 0 = axisBudget (m 0) (cov m 2) (cov m 1) from rfl]
    linarith only [h]
  · change x 1 = 1 at hk
    have h := chart_majorant (d := m 1) (e := m 0) (f := m 2)
      (covs 2) (covs 0) (covs 1) (hx 0) (hx 2) (lower 0) (lower 2)
    simp only [Fin.sum_univ_three, variance, hk, one_pow, mul_one, abs_one, Real.one_rpow,
      show budgets m 1 = axisBudget (m 1) (cov m 2) (cov m 0) from rfl]
    linarith only [h]
  · change x 2 = 1 at hk
    have h := chart_majorant (d := m 2) (e := m 0) (f := m 1)
      (covs 1) (covs 0) (covs 2) (hx 0) (hx 1) (lower 0) (lower 1)
    simp only [Fin.sum_univ_three, variance, hk, one_pow, mul_one, abs_one, Real.one_rpow,
      show budgets m 2 = axisBudget (m 2) (cov m 1) (cov m 0) from rfl]
    linarith only [h]

/-- A closed centre cube of exactly the radius needed to join E2. -/
theorem rowAt_center_cube {t : Profile} (ht : IsSimplex t)
    (hc : ∀ s, |t s - 1/4| ≤ 1/500) : RowAt criticalQ t := by
  have hm := mean_bound hc
  have hw (s : Fin 4) : 0 ≤ 1/2-t s := by have h := (abs_le.mp (hc s)).2; linarith
  have hs : ∑ s, (1/2-t s) = 1 := by rw [Finset.sum_sub_distrib, ht.2]; norm_num
  refine ⟨fun s => 1/2-t s, ⟨hw,hs⟩, fun j => budgets (mean t) j/3, ?_, ?_, ?_⟩
  · intro j
    linarith only [budgets_lower hm j]
  · rw [← Finset.sum_div]
    linarith only [budgets_sum hm]
  apply weightedRow_of_normalized_charts critical_conjugate.symm.pos
  intro k x hk hx
  change (∑ s, (1/2-t s)*|rowEval t s x|^criticalQ) ≤ ∑ j, (budgets (mean t) j/3)*|x j|^criticalQ
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  linarith only [weighted_tangent ht hw hs x, chart_bound hm k hk hx]

end
end HlawkaSchatten.BelowExponent.CenterCovariance
