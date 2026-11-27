/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Boundary
public import HlawkaSchatten.BelowExponent.Coverage
public import HlawkaSchatten.BelowExponent.Exponents
public import HlawkaSchatten.BelowExponent.Norming
public import HlawkaSchatten.BelowExponent.Reduction
public import HlawkaSchatten.BelowExponent.Symmetry

/-! Route T: a scalar certificate at all simplex profiles implies the mission's
constant-one Hlawka inequality in every finite real dimension. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

/-- The full row-to-Hlawka implication, at any pair of conjugate exponents. -/
theorem routeT {p q : ℝ} (hpq : p.HolderConjugate q)
    (hrows : ∀ t : Profile, IsSimplex t → RowAt q t)
    (ι : Type*) [Fintype ι] : HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) 1 := by
  apply hlawka_of_common_dual_ball hpq
  intro u hu
  let Q := ENNReal.ofReal q
  let U (j : Fin 3) : PiLp Q (fun _ : ι => ℝ) := WithLp.toLp Q (u j)
  have hreal : Q.toReal = q := ENNReal.toReal_ofReal hpq.symm.nonneg
  let _ : Fact (1 ≤ Q) := ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
  have hU (j : Fin 3) : ‖U j‖ ≤ 1 := (lpNorm_eq_norm_toLp hpq.symm.pos (u j)) ▸ hu j
  obtain ⟨t, _, hball⟩ := exists_common_routeTPoint (hreal.symm ▸ hpq.symm.pos)
    (hreal.symm ▸ hrows) U hU
  refine ⟨fun i => routeTPoint U t i, fun s => ?_⟩
  rw [lpNorm_eq_norm_toLp hpq.symm.pos]
  exact hball s

/-- The ordered open simplex suffices. A point-mass certificate handles a zero coordinate. -/
theorem rowAt_of_ordered_interior {q : ℝ} (hq : 1 ≤ q)
    (h : ∀ t, OrderedInterior t → RowAt q t) {t : Profile} (ht : IsSimplex t) : RowAt q t := by
  apply rowAt_of_ordered (t := t) ?_ ht
  rintro v hv ⟨h₀, h₁, h₂⟩
  by_cases hpos : 0 < v 3
  · exact h v ⟨hv, hpos, h₀, h₁, h₂⟩
  · exact rowAt_of_zero_coord hq hv (le_antisymm (le_of_not_gt hpos) (hv.1 3))

/-- The regional row proofs are the remaining hypothesis of the critical endpoint. -/
theorem critical_hlawka_of_regions
    (hregions : ∀ t : Profile, OrderedInterior t → InRegion t → RowAt criticalQ t)
    (n : ℕ) : HasHlawkaConstant (lpNorm criticalP : (Fin n → ℝ) → ℝ) 1 :=
  routeT critical_conjugate (fun _ ht => rowAt_of_ordered_interior critical_conjugate.symm.lt.le
    (fun t hord => hregions t hord (ordered_mem_region hord)) ht) (Fin n)

end HlawkaSchatten.BelowExponent
