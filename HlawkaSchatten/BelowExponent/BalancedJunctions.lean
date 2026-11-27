/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.EdgeTrial
public import HlawkaSchatten.BelowExponent.G1Edge
public import HlawkaSchatten.BelowExponent.G3EdgeS
public import HlawkaSchatten.BelowExponent.G3HeadCertificate

/-! Assemble the reusable balanced charts on the two physical edge junctions. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- The full U′ constructor on the ordered open simplex, through its overlap with G1. -/
theorem rowAt_edgeJunction {t : Profile} (ht : OrderedInterior t)
    (hl : edgeMass t ≤ 1/4000) (hτ : tau t ≤ 3/4) : RowAt criticalQ t :=
  rowAt_edgeJunction_of_balanced ht hl hτ (rowAt_g1Edge ht.simplex)
    (fun lower _ => rowAt_g1Edge_overlap ht.simplex lower hl)

/-- On VE and G4, only the two small-ratio charts at p=1 and s=1 remain. -/
theorem rowAt_vertexEdge_of_two_charts {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 7/10000) (hε : vertexDepth t ≤ 13/50)
    (left : ∀ h σ : ℝ, 0 < σ → σ ≤ 7/10000 → 0 < h → h ≤ 1/(2-σ/(2-σ)) →
      ∀ s z, |s| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap h σ 1 s z)
    (right : ∀ h σ : ℝ, 0 < σ → σ ≤ 7/10000 → 0 < h → h ≤ 1/(2-σ/(2-σ)) →
      ∀ p z, |p| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap h σ p 1 z) : RowAt criticalQ t := by
  apply rowAt_vertexEdge_of_balanced ht hσ hε (rowAt_g1Edge ht.simplex)
  intro _ hp hh hh'
  exact ⟨fun _ _ => g3_head_chart_gap hh hp (hσ.trans (by norm_num)) hh',
    left _ _ hp hσ hh hh', right _ _ hp hσ hh hh'⟩

/-- Only the low p=1 chart is needed to finish this junction. -/
theorem rowAt_vertexEdge_of_low_chart {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 7/10000) (hε : vertexDepth t ≤ 13/50)
    (low : ∀ h σ : ℝ, 0 < σ → σ ≤ 7/10000 → 0 < h → h ≤ 1/(2-σ/(2-σ)) →
      ∀ s z, |s| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap h σ 1 s z) : RowAt criticalQ t :=
  rowAt_vertexEdge_of_two_charts ht hσ hε low
    (fun _ _ hp hs hh hh' _ _ => g3_transverse_edge_chart hp hs hh hh')

end HlawkaSchatten.BelowExponent
