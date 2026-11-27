/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcJoin
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Complete

/-!
# The critical row inequality in the vertex middle and band

The two regions share the checked corner values in `vcCutPoints_checked`. Each uses its own
curvature bounds to extend those values to the full parameter cells.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 30000

theorem rowAt_vertexMiddle_optimized {t : Profile} (ht : OrderedInterior t)
    (hmin : 1 / 20 ≤ minDirection t) (hmax : maxDirection t ≤ 4 / 5)
    (hdepth : vertexDepth t ≤ 1 / 20) : RowAt criticalQ t :=
  rowAt_vertexMiddle_cut vcCutPoints_checked ht hmin hmax hdepth

theorem rowAt_vertexBand_optimized {t : Profile} (ht : OrderedInterior t)
    (hmin₀ : 1 / 40 ≤ minDirection t) (hmin₁ : minDirection t ≤ 1 / 20)
    (hmax : maxDirection t ≤ 4 / 5) (hdepth : vertexDepth t ≤ 1 / 12) : RowAt criticalQ t :=
  rowAt_vertexBand_cut vcCutPoints_checked ht hmin₀ hmin₁ hmax hdepth

end HlawkaSchatten.BelowExponent.Vertex
