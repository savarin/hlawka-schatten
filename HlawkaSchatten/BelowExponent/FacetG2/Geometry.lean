/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Coverage
public import HlawkaSchatten.BelowExponent.FacetPrismCover
public import HlawkaSchatten.BelowExponent.BulkGeometry

/-! Exact coverage and depth joins for the adaptive G2 envelope. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def g2FacetBase (t : Profile) : Row :=
  fun j => t j.castSucc / (1 - t 3)

/-- A rational trapezoid in the second and third ordered base coordinates. -/
structure G2FacetBand (b : Row) : Prop where
  sum_one : b 0 + b 1 + b 2 = 1
  third_lower : 23 / 1000 ≤ b 2
  third_upper : b 2 ≤ 1 / 20
  second_lower : 123 / 1000 ≤ b 1 + b 2
  second_upper : b 1 ≤ 4 * b 2 + 1 / 120

private theorem g2_depth_den_pos {t : Profile} (ht : OrderedInterior t) : 0 < 1 - t 3 := by
  linarith [ht.sum_four, ht.first_ge, ht.second_ge, ht.third_ge, ht.last_pos]

theorem g2_facetCap_base {t : Profile} (ht : OrderedInterior t) :
    facetCap (g2FacetBase t) (t 3) = t := by
  have hden := g2_depth_den_pos ht
  funext i
  fin_cases i
  · change (1 - t 3) * (t 0 / (1 - t 3)) = t 0
    field_simp
  · change (1 - t 3) * (t 1 / (1 - t 3)) = t 1
    field_simp
  · change (1 - t 3) * (t 2 / (1 - t 3)) = t 2
    field_simp
  · rfl

/-- Every ordered deep-facet point belongs to the full G2 band. -/
theorem g2FacetBand_of_deepFacet {t : Profile} (ht : OrderedInterior t)
    (hd : t 3 ≤ 1 / 500) (hf : facetCoord t ≤ 1 / 20)
    (hε : 1 / 8 ≤ vertexDepth t) (hσ : 1 / 5 ≤ sigma t) :
    G2FacetBand (g2FacetBase t) := by
  have hden := g2_depth_den_pos ht
  have hsum := ht.sum_four
  have hpos := ht.last_pos
  have hs := (le_div_iff₀ ht.depth_pos).1 hσ
  change (1 / 5) * (1 - t 0) ≤ t 2 + t 3 at hs
  change (1 / 8) ≤ 1 - t 0 at hε
  constructor
  · change t 0 / (1 - t 3) + t 1 / (1 - t 3) + t 2 / (1 - t 3) = 1
    rw [← add_div, ← add_div]
    exact (div_eq_iff hden.ne').2 (by linarith)
  · change (23 / 1000) ≤ t 2 / (1 - t 3)
    exact (le_div_iff₀ hden).2 (by linarith)
  · exact hf
  · change (123 / 1000) ≤ t 1 / (1 - t 3) + t 2 / (1 - t 3)
    rw [← add_div]
    exact (le_div_iff₀ hden).2 (by linarith)
  · change t 1 / (1 - t 3) ≤ 4 * (t 2 / (1 - t 3)) + 1 / 120
    apply (div_le_iff₀ hden).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hden.ne']
    linarith

theorem rowAt_deepFacet_of_g2Band {q : ℝ}
    (hband : ∀ {b d}, G2FacetBand b → 0 ≤ d → d ≤ 1 / 500 → RowAt q (facetCap b d))
    {t : Profile} (ht : OrderedInterior t)
    (hd : t 3 ≤ 1 / 500) (hf : facetCoord t ≤ 1 / 20)
    (hε : 1 / 8 ≤ vertexDepth t) (hσ : 1 / 5 ≤ sigma t) : RowAt q t := by
  rw [← g2_facetCap_base ht]
  exact hband (g2FacetBand_of_deepFacet ht hd hf hε hσ) ht.last_pos.le hd

/-- The top boundary lies in the existing closed F0–F2 band. -/
theorem g2_top_join {t : Profile} (hd : t 3 ≤ 1 / 500) (hf : facetCoord t = 1 / 20) :
    InRegion t :=
  .facetInterior hd hf.symm.le

/-- The depth cap lies in the closed E2 bulk region. -/
theorem g2_depth_join {t : Profile} (hd : t 3 = 1 / 500) : InRegion t :=
  .bulk hd.symm.le

def g2Point (x y : ℝ) : Row := ![1 - x - y, x, y]

def g2Lower (y : ℝ) : ℝ := 123 / 1000 - y

def g2Upper (y : ℝ) : ℝ := 4 * y + 1 / 120

/-- Split the trapezoid along the diagonal from its lower left to its upper right. -/
def g2Root (lo hi : ℝ) (side : Bool) : Fin 3 → Row :=
  if side then ![g2Point (g2Lower lo) lo, g2Point (g2Upper lo) lo, g2Point (g2Upper hi) hi]
  else ![g2Point (g2Lower lo) lo, g2Point (g2Lower hi) hi, g2Point (g2Upper hi) hi]

theorem g2Root_covers {b : Row} (hb : G2FacetBand b) {lo hi : ℝ}
    (hlo : lo ≤ b 2) (hhi : b 2 ≤ hi) :
    ∃ (side : Bool) (w : Fin 3 → ℝ), (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g2Root lo hi side i) = b := by
  obtain ⟨u, hu, hy⟩ := exists_interval_lerp hlo hhi
  have hu₁ : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hleft : g2Lower (b 2) ≤ b 1 := by
    unfold g2Lower
    linarith only [hb.second_lower]
  have hright : b 1 ≤ g2Upper (b 2) := hb.second_upper
  have hL : (1 - u) * g2Lower lo + u * g2Lower hi = g2Lower (b 2) := by
    rw [hy]
    simp only [g2Lower]
    ring
  have hU : (1 - u) * g2Upper lo + u * g2Upper hi = g2Upper (b 2) := by
    rw [hy]
    simp only [g2Upper]
    ring
  have hfirst : b 0 = 1 - b 1 - b 2 := by linarith only [hb.sum_one]
  let middle := (1 - u) * g2Lower lo + u * g2Upper hi
  by_cases hm : b 1 ≤ middle
  · obtain ⟨v, hv, hx⟩ := exists_interval_lerp hleft hm
    rw [← hL] at hx
    dsimp only [middle] at hx
    refine ⟨false, ![1-u, u*(1-v), u*v], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hu₁
      · exact mul_nonneg hu.1 (sub_nonneg.mpr hv.2)
      · exact mul_nonneg hu.1 hv.1
    · simp [Fin.sum_univ_three]
      ring
    · funext j
      fin_cases j <;>
        simp [g2Root, g2Point, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, hfirst, hx, hy] <;>
        ring
  · obtain ⟨v, hv, hx⟩ := exists_interval_lerp (le_of_not_ge hm) hright
    rw [← hU] at hx
    dsimp only [middle] at hx
    refine ⟨true, ![(1-u)*(1-v), (1-u)*v, u], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact mul_nonneg hu₁ (sub_nonneg.mpr hv.2)
      · exact mul_nonneg hu₁ hv.1
      · exact hu.1
    · simp [Fin.sum_univ_three]
      ring
    · funext j
      fin_cases j <;>
        simp [g2Root, g2Point, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, hfirst, hx, hy] <;>
        ring

def g2SliceRoot (upper side : Bool) : Fin 3 → Row :=
  if upper then g2Root (3 / 125) (1 / 20) side else g2Root (23 / 1000) (3 / 125) side

theorem g2SliceRoot_covers {b : Row} (hb : G2FacetBand b) :
    ∃ (upper side : Bool) (w : Fin 3 → ℝ), (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g2SliceRoot upper side i) = b := by
  by_cases h : b 2 ≤ 3 / 125
  · obtain ⟨side, w, hp, hs, he⟩ := g2Root_covers hb hb.third_lower h
    exact ⟨false, side, w, hp, hs, he⟩
  · obtain ⟨side, w, hp, hs, he⟩ := g2Root_covers hb (le_of_not_ge h) hb.third_upper
    exact ⟨true, side, w, hp, hs, he⟩

theorem rowAt_g2Band_of_roots {q : ℝ}
    (hrows : ∀ (upper side : Bool) (w : Fin 3 → ℝ) (d : ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i = 1) → 0 ≤ d → d ≤ 1 / 500 →
      RowAt q (facetCap (∑ i, w i • g2SliceRoot upper side i) d))
    {b : Row} {d : ℝ} (hb : G2FacetBand b) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt q (facetCap b d) := by
  obtain ⟨upper, side, w, hp, hs, hrepr⟩ := g2SliceRoot_covers hb
  rw [← hrepr]
  exact hrows upper side w d hp hs hd₀ hd

end

end HlawkaSchatten.BelowExponent
