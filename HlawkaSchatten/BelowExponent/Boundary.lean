/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Defs
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-! On every closed face there is a direct point-mass row certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

theorem sum_partner (t : Profile) (s : Fin 4) :
    t s + (∑ j, t (partner j s)) = ∑ r, t r := by
  fin_cases s <;> simp [partner, Fin.sum_univ_succ] <;> ring

theorem abs_sign (j : Fin 3) (s : Fin 4) : |sign j s| = 1 := by
  unfold sign
  split <;> norm_num

/-- The only active output row is the missing simplex coordinate. The three
partner coordinates are the nonnegative weights in its scalar Jensen bound. -/
theorem rowAt_of_zero_coord {q : ℝ} (hq : 1 ≤ q) {t : Profile} (ht : IsSimplex t)
    {s : Fin 4} (hs : t s = 0) : RowAt q t := by
  classical
  let γ : Row := fun j => t (partner j s)
  have hγ : ∀ j, 0 ≤ γ j := fun j => ht.1 _
  have hsum : ∑ j, γ j = 1 := by simpa only [hs, zero_add, ht.2, γ] using sum_partner t s
  let π : Profile := fun r => if r = s then 1 else 0
  have hπ : IsSimplex π := ⟨fun r => by simp only [π]; split <;> norm_num, by simp [π]⟩
  refine ⟨π, hπ, γ, hγ, hsum.le, ?_⟩
  intro x
  have hnorm : |rowEval t s x| ≤ ∑ j, γ j * |x j| := calc
    _ ≤ ∑ j, |sign j s * (t s + t (partner j s)) * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [hs, zero_add, abs_mul, abs_sign, one_mul, abs_of_nonneg (ht.1 _), γ]
  have hpow := Real.rpow_le_rpow (abs_nonneg _) hnorm (zero_le_one.trans hq)
  have hjensen := (convexOn_rpow hq).map_sum_le (t := Finset.univ) (fun j _ => hγ j) hsum
    (p := fun j => |x j|) (fun j _ => Set.mem_Ici.mpr (abs_nonneg _))
  have hface : |rowEval t s x| ^ q ≤ ∑ j, γ j * |x j| ^ q :=
    hpow.trans (by simpa only [smul_eq_mul] using hjensen)
  simpa [WeightedRow, π, ite_mul] using hface

end HlawkaSchatten.BelowExponent
