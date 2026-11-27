/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.StableMoments
public import Mathlib.Probability.Distributions.Pareto
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.UnitInterval

/-! A triangular array of finite Pareto sums. The lower cutoff is chosen so
that the first-order Laplace deficit of n samples converges to t^α. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open ProbabilityTheory MeasureTheory Real Set Filter
open scoped NNReal ENNReal Topology

private noncomputable def jumpKernel (α t x : ℝ) :=
  (1 - Real.exp (-t*x)) * x^(-α-1)

private theorem pareto_laplace_deficit {a α t : ℝ} (ha : 0 < a) (hα : 0 < α) (ht : 0 ≤ t) :
    1 - (∫ x : ℝ, Real.exp (-t * (x.toNNReal : ℝ)) ∂(paretoMeasure a α)) =
      (α*a^α) * ∫ x in Ioi a, jumpKernel α t x := by
  have : IsProbabilityMeasure (paretoMeasure a α) := isProbabilityMeasure_paretoMeasure ha hα
  have hi : Integrable (fun x : ℝ => Real.exp (-t * (x.toNNReal : ℝ))) (paretoMeasure a α) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact .of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) x.toNNReal.coe_nonneg)
  calc
    _ = ∫ x : ℝ, 1 - Real.exp (-t * (x.toNNReal : ℝ)) ∂(paretoMeasure a α) := by
      rw [integral_sub (integrable_const _) hi, integral_const]; simp
    _ = ∫ x : ℝ, (Ici a).indicator (fun u => (α*a^α) * jumpKernel α t u) x := by
      have hm : Measurable (paretoPDF a α) := by unfold paretoPDF; fun_prop
      rw [paretoMeasure, integral_withDensity_eq_integral_toReal_smul hm
        (.of_forall (fun x => (show paretoPDF a α x < ∞ from ENNReal.ofReal_lt_top)))]
      apply integral_congr_ae
      refine .of_forall fun x => ?_
      change (ENNReal.ofReal (paretoPDFReal a α x)).toReal * (1-Real.exp (-t*(x.toNNReal:ℝ))) = _
      rw [ENNReal.toReal_ofReal (paretoPDFReal_nonneg ha.le hα.le _)]
      by_cases hx : a ≤ x
      · rw [indicator_of_mem (show x ∈ Ici a from hx), paretoPDFReal, ite_eq_left hx, Real.coe_toNNReal _ (ha.le.trans hx)]
        simp only [jumpKernel, neg_add, sub_eq_add_neg]
        ring
      · simp [paretoPDFReal, hx]
    _ = _ := by rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]

private noncomputable def paretoCutoff (α C : ℝ) (n : ℕ) : ℝ :=
  ((1 / ((n:ℝ)+1)) / (α*C))^(1/α)

private theorem cutoff_props {α C : ℝ} (hα : 0 < α) (hC : 0 < C) :
    (∀ n, 0 < paretoCutoff α C n) ∧ Antitone (paretoCutoff α C) ∧
    Tendsto (paretoCutoff α C) atTop (𝓝 0) := by
  have hpow : 0 < 1/α := one_div_pos.mpr hα
  refine ⟨fun n => by unfold paretoCutoff; positivity, ?_, ?_⟩
  · intro n m hnm
    apply Real.rpow_le_rpow (by positivity) _ hpow.le
    apply div_le_div_of_nonneg_right _ (mul_pos hα hC).le
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
  · have hbase := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (α*C)
    rw [zero_div] at hbase
    change Tendsto (fun n : ℕ => ((1 / ((n:ℝ)+1)) / (α*C))^(1/α)) atTop (𝓝 0)
    simpa only [Function.comp_def, Real.zero_rpow hpow.ne'] using
      ((Real.continuous_rpow_const hpow.le).tendsto 0).comp hbase

private theorem cutoff_integral_tendsto {α C t : ℝ} (hα : 0 < α) (hα₁ : α < 1)
    (hC : 0 < C) (ht : 0 < t) :
    Tendsto (fun n => ∫ x in Ioi (paretoCutoff α C n), jumpKernel α t x) atTop
      (𝓝 (t^α * fractionalMomentConstant 1 α)) := by
  obtain ⟨hpos, hanti, hto⟩ := cutoff_props hα hC
  have hs : (⋃ n : ℕ, Ioi (paretoCutoff α C n)) = Ioi 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact (hpos n).trans hn
    · intro hx
      obtain ⟨n, hn⟩ := (hto.eventually_lt_const hx).exists
      exact mem_iUnion.mpr ⟨n, hn⟩
  have he : (∫ x in Ioi 0, jumpKernel α t x) = t^α * fractionalMomentConstant 1 α := by
    simpa [jumpKernel, fractionalMomentConstant, Real.rpow_one, neg_mul] using
      (integral_scaled_fractionalMomentKernel (α := 1) (β := α) ht)
  have hi : IntegrableOn (jumpKernel α t) (Ioi 0) := by
    by_contra hh
    exact (mul_pos (Real.rpow_pos_of_pos ht α) (integral_fractionalMomentKernel_pos hα hα₁)).ne
      ((integral_undef hh).symm.trans he)
  rw [← he, ← hs] at *
  exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioi)
    (fun _ _ h => Ioi_subset_Ioi (hanti h)) hi

private noncomputable def compactSum {n : ℕ} (y : Fin n → ℝ) : unitInterval :=
  ⟨Real.exp (-(∑ i, ((y i).toNNReal : ℝ))), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg fun i _ => (y i).toNNReal.coe_nonneg))⟩

private theorem compactSum_measurable (n : ℕ) : Measurable (@compactSum n) := by
  apply Measurable.subtype_mk
  fun_prop

private theorem compactSum_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : unitInterval, (x:ℝ)^t ∂((Measure.pi (fun _ : Fin n => μ)).map compactSum)) =
      (∫ x : ℝ, Real.exp (-t * (x.toNNReal : ℝ)) ∂μ)^n := by
  have hm : Measurable (fun x : unitInterval => (x:ℝ)^t) :=
    ((Real.continuous_rpow_const ht).comp continuous_subtypeVal).measurable
  rw [integral_map (compactSum_measurable n).aemeasurable hm.aestronglyMeasurable]
  have h (y : Fin n → ℝ) : (compactSum y : ℝ)^t = ∏ i, Real.exp (-t * ((y i).toNNReal : ℝ)) := by
    change (Real.exp (-(∑ i, ((y i).toNNReal : ℝ))))^t = _
    rw [← Real.exp_mul, ← Real.exp_sum, ← Finset.mul_sum]
    congr 1
    ring
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (fun _ (x : ℝ) => Real.exp (-t * (x.toNNReal : ℝ)))]
  simp

/-- Probability measures on [0,1] with moments converging to the desired Laplace transform. -/
theorem exists_pareto_approximants {α : ℝ} (hα : 0 < α) (hα₁ : α < 1) :
    ∃ ν : ℕ → ProbabilityMeasure unitInterval, ∀ t : ℝ, 0 < t →
      Tendsto (fun n => ∫ x, (x : ℝ)^t ∂(ν n : Measure unitInterval)) atTop (𝓝 (Real.exp (-(t^α)))) := by
  let C := fractionalMomentConstant 1 α
  have hC : 0 < C := integral_fractionalMomentKernel_pos hα hα₁
  let a := paretoCutoff α C
  have ha : ∀ n, 0 < a n := (cutoff_props hα hC).1
  let μ (n : ℕ) := paretoMeasure (a n) α
  have hμ (n : ℕ) : IsProbabilityMeasure (μ n) := isProbabilityMeasure_paretoMeasure (ha n) hα
  let ν (n : ℕ) : ProbabilityMeasure unitInterval :=
    ⟨(Measure.pi (fun _ : Fin n => μ n)).map compactSum, inferInstance⟩
  refine ⟨ν, fun t ht => ?_⟩
  let J (n : ℕ) := ∫ x in Ioi (a n), jumpKernel α t x
  let g (n : ℕ) := - (J n / C) / ((n:ℝ)+1)
  have hJ : Tendsto J atTop (𝓝 (t^α*C)) := cutoff_integral_tendsto hα hα₁ hC ht
  have hscale (n : ℕ) : α * (a n)^α = 1 / (((n:ℝ)+1)*C) := by
    change α * (((1 / ((n:ℝ)+1)) / (α*C))^(1/α))^α = _
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
    field_simp
  have hg : Tendsto (fun n : ℕ => (n:ℝ)*g n) atTop (𝓝 (-(t^α))) := by
    have hL := (tendsto_natCast_div_add_atTop (1:ℝ)).mul ((hJ.div_const C).neg)
    have hlim : (1:ℝ) * (-(t^α*C / C)) = -(t^α) := by field_simp
    rw [hlim] at hL
    exact hL.congr (fun n => by dsimp [g]; ring)
  apply (Real.tendsto_one_add_pow_exp_of_tendsto hg).congr
  intro n
  change (1+g n)^n = ∫ x : unitInterval, (x:ℝ)^t ∂((Measure.pi (fun _ : Fin n => μ n)).map compactSum)
  rw [compactSum_moment _ _ ht.le]
  congr 1
  have hd := pareto_laplace_deficit (ha n) hα ht.le
  rw [hscale] at hd
  change 1 + -(J n/C) / ((n:ℝ)+1) = _
  change 1 - _ = (1 / (((n:ℝ)+1)*C)) * J n at hd
  change 1 + -(J n/C)/((n:ℝ)+1) =
    ∫ x : ℝ, Real.exp (-t * (x.toNNReal : ℝ)) ∂paretoMeasure (a n) α
  have he : -(J n/C)/((n:ℝ)+1) = -(1/(((n:ℝ)+1)*C) * J n) := by
    field_simp
  linarith only [hd, he]

end HlawkaSchatten.BelowExponent
