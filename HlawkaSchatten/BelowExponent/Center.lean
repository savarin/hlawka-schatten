/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Exponents
public import HlawkaSchatten.BelowExponent.Boundary
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.BigOperators.Field

/-! A sharp certificate at the barycenter. The four even sign rows are orthogonal
in their three columns, and concavity of the half power gives the row estimate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable def centerProfile : Profile := fun _ => 1/4

private theorem rpow_sq_half (v q : ℝ) : (v^2)^(q/2) = |v|^q := by
  calc
    _ = (|v|^(2:ℝ))^(q/2) := by rw [Real.rpow_two, sq_abs]
    _ = _ := by rw [← Real.rpow_mul (abs_nonneg v), show 2*(q/2)=q by ring]

private theorem halfPower_sum_le {ι : Type*} (s : Finset ι) (v : ι → ℝ) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) : (∑ i ∈ s, v i ^ 2)^r ≤ ∑ i ∈ s, (v i ^ 2)^r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hr.ne']
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
      hr.le hr₁).trans (add_le_add_right ih _)

theorem center_rowAt {q : ℝ} (hq₀ : 0 < q) (hq₂ : q ≤ 2) (hp : 3 ≤ (2 : ℝ)^q) :
    RowAt q centerProfile := by
  have hden : 0 < (2:ℝ)^q := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : 0 < q/2 := by linarith
  have hhalf₁ : q/2 ≤ 1 := by linarith
  refine ⟨centerProfile, ⟨fun _ => by norm_num [centerProfile], by norm_num [centerProfile]⟩,
    fun _ => 1/(2:ℝ)^q, fun _ => (one_div_pos.mpr hden).le, ?_, ?_⟩
  · simpa [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using (div_le_one hden).2 hp
  intro x
  let v (s : Fin 4) := ∑ j, sign j s * x j
  have hv (s : Fin 4) : rowEval centerProfile s x = v s / 2 := by
    unfold rowEval centerProfile v
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have horth : (∑ s, (1/4:ℝ) * (v s)^2) = ∑ j, x j ^ 2 := by
    simp (config := {decide := true}) [Fin.sum_univ_three, Fin.sum_univ_four, v, sign, partner]
    ring
  have hj := (Real.concaveOn_rpow hhalf.le hhalf₁).le_map_sum (t := Finset.univ)
    (w := fun _ : Fin 4 => (1/4:ℝ)) (p := fun s => (v s)^2)
    (fun _ _ => by norm_num) (by norm_num) (fun s _ => Set.mem_Ici.mpr (sq_nonneg _))
  simp only [smul_eq_mul, horth] at hj
  have hs := hj.trans (halfPower_sum_le Finset.univ x hhalf hhalf₁)
  simp only [rpow_sq_half] at hs
  change (∑ s, (1/4:ℝ)*|rowEval centerProfile s x|^q) ≤ ∑ j, (1/(2:ℝ)^q)*|x j|^q
  calc
    _ = (∑ s, (1/4:ℝ)*|v s|^q)/(2:ℝ)^q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [hv, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), Real.div_rpow (abs_nonneg _) (by norm_num)]
      ring
    _ ≤ (∑ j, |x j|^q)/(2:ℝ)^q := div_le_div_of_nonneg_right hs hden.le
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem critical_rowAt_center : RowAt criticalQ centerProfile :=
  center_rowAt critical_conjugate.symm.pos (by linarith [criticalQ_bracket.2])
    two_rpow_criticalQ.ge

end HlawkaSchatten.BelowExponent
