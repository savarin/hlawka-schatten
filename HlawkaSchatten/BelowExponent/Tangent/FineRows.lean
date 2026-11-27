/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.CellRows
public import HlawkaSchatten.BelowExponent.Tangent.Certificates

/-! Real row inequalities for every checked non-centre leaf of the concrete E2 cover. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

set_option maxRecDepth 10000 in
theorem rowAt_fine_leaf {i : ℕ} (hi : i < TC.R002_geoms.length) {t : Profile}
    (ht : t ∈ cellSet (TC.R002_geoms.getD i default)) : RowAt criticalQ t :=
  rowAt_of_cellOK (H := TC.R002_hdr) (G := TC.R002_geoms.getD i default)
    (D := TC.R002_cells.getD i default) TC.fine_tab_ok TC.R002_exponent_denominators_pos
    (TC.R002_cellOK hi) ht

set_option maxRecDepth 10000 in
theorem rowAt_of_mem_fine_leaf {G : TC.Geom} (hG : G ∈ TC.R002_geoms) {t : Profile}
    (ht : t ∈ cellSet G) : RowAt criticalQ t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hG
  apply rowAt_fine_leaf hi
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using ht

end HlawkaSchatten.BelowExponent.Tangent
