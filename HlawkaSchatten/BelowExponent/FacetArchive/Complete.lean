/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F0Root
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Root
public import HlawkaSchatten.BelowExponent.FacetArchive.F2Root

/-! The adaptive F0–F2 proof on the entire ordered facet-interior strip. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

theorem rowAt_facetInterior_adaptive {t : Profile} (ht : OrderedInterior t)
    (hd : t 3 ≤ 1 / 400) (hf : 1 / 20 ≤ facetCoord t) : RowAt criticalQ t := by
  apply rowAt_facetInterior_of_archive_roots _ ht hd hf
  intro i
  fin_cases i
  · exact @FacetNumeric.f0RowsRoot
  · exact @FacetNumeric.f1RowsRoot
  · exact @FacetNumeric.f2RowsRoot

end HlawkaSchatten.BelowExponent
