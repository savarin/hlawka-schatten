/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.StableMoments
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.UnitInterval

/-! Recover a law on the nonnegative reals from limits of the moments of
probability measures on the compact interval. The small positive exponents
rule out an atom at zero before applying the negative logarithm. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open MeasureTheory Set Filter
open scoped NNReal Topology

private noncomputable def unitPower (t : ℝ) (ht : 0 ≤ t) : BoundedContinuousFunction unitInterval ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (x : ℝ)^t, (Real.continuous_rpow_const ht).comp continuous_subtypeVal⟩

/-- Compactness and continuity at zero suffice for existence of the positive stable law. -/
theorem positiveStable_of_unitInterval_approximants {α : ℝ} (hα : 0 < α)
    (ν : ℕ → ProbabilityMeasure unitInterval)
    (hν : ∀ t : ℝ, 0 < t → Tendsto (fun n => ∫ x, (x : ℝ)^t ∂(ν n : Measure unitInterval))
      atTop (𝓝 (Real.exp (-(t^α))))) : HasPositiveStable α := by
  obtain ⟨ρ, φ, hφ, hρ⟩ := CompactSpace.tendsto_subseq ν
  let μ : Measure unitInterval := ρ
  have hprob : IsProbabilityMeasure μ := ρ.property
  have hpow (t : ℝ) (ht : 0 < t) : (∫ x : unitInterval, (x : ℝ)^t ∂μ) = Real.exp (-(t^α)) := by
    have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hρ (unitPower t ht.le)
    exact tendsto_nhds_unique hc ((hν t ht).comp hφ.tendsto_atTop)
  have hmass (t : ℝ) (ht : 0 < t) : μ.real ({0} : Set unitInterval) ≤ 1 - Real.exp (-(t^α)) := by
    have hi : Integrable (fun x : unitInterval => (x : ℝ)^t) μ :=
      (unitPower t ht.le).integrable (μ := μ)
    have hdom (x : unitInterval) :
        ({0} : Set unitInterval).indicator (fun _ => (1:ℝ)) x ≤ 1 - (x:ℝ)^t := by
      by_cases h : x = 0
      · subst x; simp [Real.zero_rpow ht.ne']
      · rw [Set.indicator_of_notMem (show x ∉ ({0}:Set unitInterval) from h)]
        exact sub_nonneg.mpr (Real.rpow_le_one x.2.1 x.2.2 ht.le)
    calc
      _ = ∫ x, ({0} : Set unitInterval).indicator (fun _ => (1:ℝ)) x ∂μ :=
        (integral_indicator_one (measurableSet_singleton _)).symm
      _ ≤ ∫ x : unitInterval, 1 - (x:ℝ)^t ∂μ :=
        integral_mono ((integrable_const _).indicator (measurableSet_singleton _)) ((integrable_const _).sub hi) hdom
      _ = _ := by rw [integral_sub (integrable_const _) hi, integral_const, hpow t ht]; simp [μ]
  have hlim : Tendsto (fun t : ℝ => 1 - Real.exp (-(t^α))) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => 1 - Real.exp (-(t^α))) :=
      continuous_const.sub (Real.continuous_exp.comp (Real.continuous_rpow_const hα.le).neg)
    simpa [Real.zero_rpow hα.ne'] using (hcont.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hzReal : μ.real ({0} : Set unitInterval) = 0 := le_antisymm
    (ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono (fun t ht => hmass t ht))) measureReal_nonneg
  have hz : μ ({0} : Set unitInterval) = 0 := (measureReal_eq_zero_iff).mp hzReal
  have hae : ∀ᵐ x : unitInterval ∂μ, x ≠ 0 := by simpa [ae_iff] using hz
  let expand (x : unitInterval) := Real.toNNReal (-(Real.log (x : ℝ)))
  have hm : Measurable expand := by unfold expand; fun_prop
  refine ⟨μ.map expand, inferInstance, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h | h
  · subst t
    simp [Real.zero_rpow hα.ne']
  · rw [integral_map hm.aemeasurable (by fun_prop), ← hpow t h]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    have hx₀ : 0 < (x : ℝ) := lt_of_le_of_ne x.2.1 (by
      intro H
      exact hx (Subtype.ext (by simpa using H.symm)))
    have hx₁ : Real.log (x:ℝ) ≤ 0 := Real.log_nonpos x.2.1 x.2.2
    change Real.exp (-t * ((Real.toNNReal (-(Real.log (x:ℝ))) : ℝ≥0) : ℝ)) = (x:ℝ)^t
    rw [Real.coe_toNNReal _ (neg_nonneg.mpr hx₁), Real.rpow_def_of_pos hx₀]
    congr 1
    ring

end HlawkaSchatten.BelowExponent
