/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.FineCoverage
public import HlawkaSchatten.BelowExponent.Tangent.FineRows

/-! The complete E2 certificate on the ordered, depth-truncated simplex outside the centre cube. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

/-- All rows through the 167 E2 leaf certificates on the ordered bulk domain outside the open cube. -/
theorem rowAt_e2_outside_cube {t : Profile} (ht : OrderedInterior t) (hd : 1 / 500 ≤ t 3)
    (hOut : ∃ i, 1 / 500 ≤ |t i - 1 / 4|) : RowAt criticalQ t := by
  obtain ⟨G, hG, hLeaf⟩ := mem_fine_leaf_of_outside_cube ht hd hOut
  exact rowAt_of_mem_fine_leaf hG hLeaf

end HlawkaSchatten.BelowExponent.Tangent
