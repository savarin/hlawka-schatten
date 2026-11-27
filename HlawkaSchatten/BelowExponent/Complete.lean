/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Assembly
public import HlawkaSchatten.BelowExponent.RegionalCertificates
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcComplete
public import HlawkaSchatten.BelowExponent.Vertex.SideCutCorners.CoarseComplete

/-!
# Hlawka's inequality through the critical exponent

The middle, band and side theorems supply the three vertex hypotheses of
`HlawkaSchatten.BelowExponent.rowAt_of_three_vertex_regions`. This gives the critical row
inequality on the ordered simplex at `criticalP = log 3 / log (3 / 2)`. In every finite
dimension, `HlawkaSchatten.BelowExponent.hlawka_below_of_regions` combines that endpoint with
the Euclidean case at `p = 2` and uses the stable-law transfer for `2 < p < criticalP`.
-/

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open HlawkaSchatten.DiagonalConstruction

/-- Hlawka's inequality with constant one throughout the closed lower exponent interval. -/
theorem hlawka_holds_below_exponent :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 :=
  hlawka_below_of_regions (rowAt_of_three_vertex_regions
    (fun _ => Vertex.rowAt_vertexMiddle_optimized)
    (fun _ => Vertex.rowAt_vertexBand_optimized)
    (fun _ => Vertex.rowAt_vertexSide_optimized))

end HlawkaSchatten.BelowExponent
