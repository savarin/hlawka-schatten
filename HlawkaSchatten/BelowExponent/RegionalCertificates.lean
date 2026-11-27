/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.AdaptiveCoverage
public import HlawkaSchatten.BelowExponent.BalancedJunctions
public import HlawkaSchatten.BelowExponent.BulkComplete
public import HlawkaSchatten.BelowExponent.BulkGeometry
public import HlawkaSchatten.BelowExponent.F0Prism10
public import HlawkaSchatten.BelowExponent.F2Prism71
public import HlawkaSchatten.BelowExponent.FSlabData.Complete
public import HlawkaSchatten.BelowExponent.FacetArchive.Complete
public import HlawkaSchatten.BelowExponent.FacetG2.Complete
public import HlawkaSchatten.BelowExponent.G1Complete
public import HlawkaSchatten.BelowExponent.G3Cone
public import HlawkaSchatten.BelowExponent.G3EdgeComplete
public import HlawkaSchatten.BelowExponent.G3HeadCertificate
public import HlawkaSchatten.BelowExponent.G3SBands.Complete
public import HlawkaSchatten.BelowExponent.G3Wider
public import HlawkaSchatten.BelowExponent.Tangent.FineRows
public import HlawkaSchatten.BelowExponent.Tangent.OutsideCube
public import HlawkaSchatten.BelowExponent.Tangent.Root
public import HlawkaSchatten.BelowExponent.VertexRegion
public import HlawkaSchatten.BelowExponent.Vertex.CoefficientDerivatives

/-! Regional certificates and reductions for the critical weighted row inequality. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- Prove the row bound on the ordered chamber from the bulk and facet estimates and the balanced-edge
bounds, given the center collar and the four indicated vertex bounds. -/
theorem rowAt_of_center_and_vertices
    (center : ∀ t : Profile, OrderedInterior t →
      (∑ i, (t i - centerProfile i) ^ 2 ≤ (1 / 100 : ℝ) ^ 2) → RowAt criticalQ t)
    (middle : ∀ t : Profile, OrderedInterior t → 1/20 ≤ minDirection t →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/20 → RowAt criticalQ t)
    (band : ∀ t : Profile, OrderedInterior t → 1/40 ≤ minDirection t → minDirection t ≤ 1/20 →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/12 → RowAt criticalQ t)
    (side : ∀ t : Profile, OrderedInterior t → minDirection t ≤ 1/40 →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/8 → RowAt criticalQ t)
    (corner : ∀ t : Profile, OrderedInterior t → 7/10000 ≤ sigma t → sigma t ≤ 1/5 →
      0 < cornerH t → cornerH t ≤ 1/(2 - cornerK t) → RowAt criticalQ t)
    (t : Profile) (ht : OrderedInterior t) (region : InRegion t) : RowAt criticalQ t := by
  cases region with
  | bulk hd => exact rowAt_bulk_of_e2_and_center (fun _ => Tangent.rowAt_e2_outside_cube) center ht hd
  | facetInterior hd hf => exact rowAt_facetInterior_adaptive ht (hd.trans (by norm_num)) hf
  | edgeJunction hl _ hτ => exact rowAt_edgeJunction ht hl hτ
  | balancedEdge hl₀ hl₁ he₀ he₁ => exact rowAt_g1 ht.simplex hl₀ hl₁ he₀ he₁
  | facetStrip hf₀ hf₁ _ hτ hd _ => exact rowAt_facetStrip_balanced ht hf₀ hf₁ hτ hd
  | deepFacet hd hf hε hσ _ => exact rowAt_deepFacet_adaptive ht hd hf hε hσ
  | vertexMiddle hm hM hε => exact middle t ht hm hM hε
  | vertexBand hm₀ hm₁ hM hε => exact band t ht hm₀ hm₁ hM hε
  | vertexSide hm hM hε => exact side t ht hm hM hε
  | vertexEdge hσ hε => exact rowAt_vertexEdge_balanced ht hσ hε
  | vertexCorner hσ₀ hσ₁ hh₀ hh₁ => exact corner t ht hσ₀ hσ₁ hh₀ hh₁

/-- Prove the row bound on the ordered chamber using the middle, band and side bounds and the central
vertex-corner chart. The chart hypothesis is proved by `g3_central_wider_chart`. -/
theorem rowAt_of_vertex_inputs
    (middle : ∀ t : Profile, OrderedInterior t → 1/20 ≤ minDirection t →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/20 → RowAt criticalQ t)
    (band : ∀ t : Profile, OrderedInterior t → 1/40 ≤ minDirection t → minDirection t ≤ 1/20 →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/12 → RowAt criticalQ t)
    (side : ∀ t : Profile, OrderedInterior t → minDirection t ≤ 1/40 →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/8 → RowAt criticalQ t)
    (pChart : ∀ h σ s z : ℝ, 0 < h → 7/10000 ≤ σ → σ ≤ 1/5 →
      h ≤ 1/(2 - σ/(2-σ)) → |s| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap h σ 1 s z)
    (t : Profile) (ht : OrderedInterior t) (region : InRegion t) : RowAt criticalQ t := by
  apply rowAt_of_center_and_vertices (fun _ => rowAt_center_collar) middle band side _ t ht region
  intro v hv hσ₀ hσ₁ hh₀ hh₁
  have hσ : 0 < sigma v := (by norm_num : (0 : ℝ) < 7/10000).trans_le hσ₀
  exact rowAt_g3_of_charts hv hσ₀ hσ₁ hh₀ hh₁
    (fun _ _ => g3_head_chart_gap hh₀ hσ hσ₁ hh₁)
    (fun s z => pChart _ _ s z hh₀ hσ₀ hσ₁ hh₁)
    (fun _ _ => G3S.wider_chart hh₀ hσ₀ hσ₁ hh₁)

/-- Combine the bulk, facet, edge and vertex-corner estimates with the middle, band and
side bounds. The public theorem
`HlawkaSchatten.BelowExponent.hlawka_holds_below_exponent` uses this form. -/
theorem rowAt_of_three_vertex_regions
    (middle : ∀ t : Profile, OrderedInterior t → 1/20 ≤ minDirection t →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/20 → RowAt criticalQ t)
    (band : ∀ t : Profile, OrderedInterior t → 1/40 ≤ minDirection t → minDirection t ≤ 1/20 →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/12 → RowAt criticalQ t)
    (side : ∀ t : Profile, OrderedInterior t → minDirection t ≤ 1/40 →
      maxDirection t ≤ 4/5 → vertexDepth t ≤ 1/8 → RowAt criticalQ t)
    (t : Profile) (ht : OrderedInterior t) (region : InRegion t) : RowAt criticalQ t :=
  rowAt_of_center_and_vertices (fun _ => rowAt_center_collar) middle band side
    (fun _ => rowAt_vertexCorner_balanced) t ht region

end HlawkaSchatten.BelowExponent
