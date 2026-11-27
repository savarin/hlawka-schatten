/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.BalancedJunctions
public import HlawkaSchatten.BelowExponent.G3PLow

/-! The balanced row estimate at the vertex-edge junction across both tau ranges. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

theorem rowAt_vertexEdge_balanced {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 7 / 10000) (hε : vertexDepth t ≤ 13 / 50) : RowAt criticalQ t :=
  rowAt_vertexEdge_of_low_chart ht hσ hε
    (fun _ _ hs hc hh hh' _ _ => g3_p_low_chart_gap hh hs hc hh')

end HlawkaSchatten.BelowExponent
