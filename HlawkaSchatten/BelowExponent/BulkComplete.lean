/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.CenterCovariance
public import HlawkaSchatten.BelowExponent.Tangent.OutsideCube

/-! The checked centre cube and the E2 tangent cover join at deviation 1/500. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

theorem rowAt_bulk_adaptive {t : Profile} (ht : OrderedInterior t)
    (hd : 1/500 ≤ t 3) : RowAt criticalQ t := by
  by_cases outside : ∃ i, 1/500 ≤ |t i - 1/4|
  · exact Tangent.rowAt_e2_outside_cube ht hd outside
  · exact CenterCovariance.rowAt_center_cube ht.simplex
      (fun i => (lt_of_not_ge fun h => outside ⟨i, h⟩).le)

/-- The ball used by the earlier assembly lies inside the full bulk domain. -/
theorem rowAt_center_collar {t : Profile} (ht : OrderedInterior t)
    (hc : ∑ i, (t i - centerProfile i)^2 ≤ (1/100 : ℝ)^2) : RowAt criticalQ t := by
  have hlast : (t 3 - 1/4)^2 ≤ (1/100 : ℝ)^2 := calc
    _ ≤ ∑ i, (t i - centerProfile i)^2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (t i - centerProfile i)) (Finset.mem_univ (3 : Fin 4))
    _ ≤ _ := hc
  apply rowAt_bulk_adaptive ht
  nlinarith only [hlast, sq_nonneg (t 3)]

end HlawkaSchatten.BelowExponent
