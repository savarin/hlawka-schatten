/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Defs
public import HlawkaSchatten.BelowExponent.Target
public import Mathlib.Analysis.MeanInequalities

/-! Finite real Hölder duality in the mission's coordinate norm, and the passage
from a common point of four dual balls to the Hlawka inequality. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

theorem lpNorm_eq_norm_toLp {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

theorem real_holder {p q : ℝ} (hpq : p.HolderConjugate q) (x y : ι → ℝ) :
    (∑ i, x i * y i) ≤ lpNorm p x * lpNorm q y := by
  simpa only [lpNorm, Real.norm_eq_abs] using Real.inner_le_Lp_mul_Lq Finset.univ x y hpq

/-- A norming vector exists also when the given vector or the entire coordinate type is zero. -/
theorem exists_norming_vector {p q : ℝ} (hpq : p.HolderConjugate q) (x : ι → ℝ) :
    ∃ u : ι → ℝ, lpNorm q u ≤ 1 ∧ (∑ i, u i * x i) = lpNorm p x := by
  classical
  obtain ⟨g, hg, hval⟩ := (NNReal.isGreatest_Lp Finset.univ (fun i => ‖x i‖₊) hpq).1
  change (∑ i, g i ^ q) ≤ 1 at hg
  have hcost : (∑ i, (g i : ℝ) ^ q) ≤ 1 := by exact_mod_cast hg
  let u (i : ι) : ℝ := if 0 ≤ x i then g i else -(g i : ℝ)
  have hu (i : ι) : |u i| = (g i : ℝ) := by
    simp only [u]
    split <;> simp
  have hpairs (i : ι) : u i * x i = ‖x i‖ * g i := by
    simp only [u, Real.norm_eq_abs]
    split
    · next h => rw [abs_of_nonneg h, mul_comm]
    · next h => rw [abs_of_neg (lt_of_not_ge h)]; ring
  refine ⟨u, ?_, ?_⟩
  · simp only [lpNorm, Real.norm_eq_abs, hu]
    exact Real.rpow_le_one (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (g i).2 _) hcost
      (one_div_nonneg.mpr hpq.symm.nonneg)
  · simp only [hpairs]
    simpa only [Function.comp_apply, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow,
      coe_nnNorm, lpNorm] using congrArg NNReal.toReal hval

/-- Coordinatewise pairing identity for the four sign vectors, including any common translation. -/
theorem quartet_pairing (u : Row) (x : Profile) (z : ℝ) (hx : ∑ s, x s = 0) :
    (∑ j, u j * (x 0 + x (partner j 0))) =
      ∑ s, ((∑ j, sign j s * u j)/2 - z) * x s := by
  simp [Fin.sum_univ_succ] at hx
  have h₃ : x 3 = -(x 0 + x 1 + x 2) := by linarith
  simp [Fin.sum_univ_succ, sign, partner, h₃]
  ring

theorem hlawka_of_common_dual_ball {p q : ℝ} (hpq : p.HolderConjugate q)
    (hball : ∀ u : Fin 3 → ι → ℝ, (∀ j, lpNorm q (u j) ≤ 1) →
      ∃ z : ι → ℝ, ∀ s : Fin 4, lpNorm q (fun i => (∑ j, sign j s * u j i)/2 - z i) ≤ 1) :
    HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) 1 := by
  apply hasHlawkaConstant_one_of_zeroSum
  · intro x
    simp [lpNorm]
  intro x hx
  let b (j : Fin 3) := x 0 + x (partner j 0)
  choose u hu hpair using fun j => exists_norming_vector hpq (b j)
  obtain ⟨z, hz⟩ := hball u hu
  let w (s : Fin 4) (i : ι) := (∑ j, sign j s * u j i)/2 - z i
  have hsum (i : ι) : ∑ s, x s i = 0 := by
    simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hx i
  have hid (i : ι) : (∑ j, u j i * b j i) = ∑ s, w s i * x s i :=
    quartet_pairing (fun j => u j i) (fun s => x s i) (z i) (hsum i)
  have hsize (s : Fin 4) : 0 ≤ lpNorm p (x s) := by
    exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hbound (s : Fin 4) : (∑ i, w s i * x s i) ≤ lpNorm p (x s) := calc
    _ ≤ lpNorm q (w s) * lpNorm p (x s) := real_holder hpq.symm _ _
    _ ≤ 1 * lpNorm p (x s) := mul_le_mul_of_nonneg_right (hz s) (hsize s)
    _ = _ := one_mul _
  have total : (∑ j, lpNorm p (b j)) ≤ ∑ s, lpNorm p (x s) := calc
    _ = ∑ j, ∑ i, u j i * b j i := Finset.sum_congr rfl fun j _ => (hpair j).symm
    _ = ∑ i, ∑ j, u j i * b j i := Finset.sum_comm
    _ = ∑ i, ∑ s, w s i * x s i := Finset.sum_congr rfl fun i _ => hid i
    _ = ∑ s, ∑ i, w s i * x s i := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun s _ => hbound s
  simpa [b, partner, Fin.sum_univ_succ, add_assoc] using total

end HlawkaSchatten.BelowExponent
