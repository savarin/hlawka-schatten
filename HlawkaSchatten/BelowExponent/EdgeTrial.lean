/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3

/-! Physical joins for the balanced extensions of U′ and the vertex-edge junction. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

private theorem edgeMass_pos {t : Profile} (ht : OrderedInterior t) : 0 < edgeMass t := by
  exact add_pos (ht.last_pos.trans_le ht.third_ge) ht.last_pos

private theorem pair_pos {t : Profile} (ht : OrderedInterior t) : 0 < t 0 + t 1 := by
  linarith only [ht.last_pos, ht.third_ge, ht.second_ge, ht.first_ge]

theorem imbalance_of_tau_le {t : Profile} (ht : OrderedInterior t) (hτ : tau t ≤ 3/4) :
    0 ≤ imbalance t ∧ imbalance t ≤ 1/2 := by
  have hlin := (div_le_iff₀ (pair_pos ht)).1 hτ
  exact ⟨sub_nonneg.mpr ht.first_ge, by
    unfold imbalance
    linarith only [hlin, ht.sum_four, ht.last_pos, ht.third_ge]⟩

/-- The two positive-length balanced certificates overlap, including at 1/4096. -/
theorem rowAt_edgeJunction_of_balanced {t : Profile} (ht : OrderedInterior t)
    (hl : edgeMass t ≤ 1/4000) (hτ : tau t ≤ 3/4)
    (small : 0 < edgeMass t → edgeMass t ≤ 1/4096 → 0 ≤ imbalance t →
      imbalance t ≤ 1/2 → RowAt criticalQ t)
    (slabs : 1/4096 ≤ edgeMass t → edgeMass t ≤ 74/4096 → 0 ≤ imbalance t →
      imbalance t ≤ 1/2 → RowAt criticalQ t) : RowAt criticalQ t := by
  obtain ⟨he, he'⟩ := imbalance_of_tau_le ht hτ
  rcases le_total (edgeMass t) (1/4096) with h | h
  · exact small (edgeMass_pos ht) h he he'
  · exact slabs h (hl.trans (by norm_num)) he he'

theorem vertexEdge_length {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 7/10000) (hε : vertexDepth t ≤ 13/50) : edgeMass t ≤ 1/4096 := by
  have h := (div_le_iff₀ ht.depth_pos).1 hσ
  linarith only [h, hε]

/-- On the high-tau part the original corner height is admissible at every positive ratio. -/
theorem vertexEdge_corner_height {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 7/10000) (hτ : 3/4 ≤ tau t) :
    0 < cornerH t ∧ cornerH t ≤ 1/(2-cornerK t) := by
  have hs : sigma t ≤ 1/5 := hσ.trans (by norm_num)
  have hk : cornerK t ≤ 1/9 :=
    (div_le_iff₀ (by linarith : 0 < 2-sigma t)).2 (by linarith)
  have hlin := (le_div_iff₀ (pair_pos ht)).1 hτ
  refine ⟨?_, (le_div_iff₀ (by linarith : 0 < 2-cornerK t)).2 ?_⟩
  · unfold cornerH imbalance
    linarith only [ht.sum_four, ht.last_pos, ht.second_ge, ht.third_ge]
  · rw [mul_sub, ht.depth_mul_ratio hs]
    unfold cornerH imbalance edgeMass
    linarith only [ht.sum_four, hlin]

/-- Split the whole VE and G4 region at tau=3/4. The low half uses small G1.
The high half consumes exactly the three small-ratio G3 chart inequalities. -/
theorem rowAt_vertexEdge_of_balanced {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 7/10000) (hε : vertexDepth t ≤ 13/50)
    (small : 0 < edgeMass t → edgeMass t ≤ 1/4096 → 0 ≤ imbalance t →
      imbalance t ≤ 1/2 → RowAt criticalQ t)
    (charts : 3/4 ≤ tau t → 0 < sigma t → 0 < cornerH t → cornerH t ≤ 1/(2-cornerK t) →
      (∀ p s, |p| ≤ 1/8 → |s| ≤ 1/8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) p s 1) ∧
      (∀ s z, |s| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) 1 s z) ∧
      (∀ p z, |p| ≤ 1 → |z| ≤ 8 → 0 ≤ g3FacetGap (cornerH t) (sigma t) p 1 z)) :
    RowAt criticalQ t := by
  rcases le_total (tau t) (3/4) with h | h
  · obtain ⟨he, he'⟩ := imbalance_of_tau_le ht h
    exact small (edgeMass_pos ht) (vertexEdge_length ht hσ hε) he he'
  · obtain ⟨hh, hh'⟩ := vertexEdge_corner_height ht hσ h
    have hp : 0 < sigma t := div_pos (edgeMass_pos ht) ht.depth_pos
    obtain ⟨head, left, right⟩ := charts h hp hh hh'
    exact rowAt_g3_of_positive_charts ht hp (hσ.trans (by norm_num)) hh hh' head left right

end HlawkaSchatten.BelowExponent
