/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabMesh
public import HlawkaSchatten.BelowExponent.Balanced
public import HlawkaSchatten.BelowExponent.BulkGeometry
public import HlawkaSchatten.BelowExponent.Coverage

/-! A full F-strip cover from the existing G1 range and closed slab endpoints. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

def FSlabEndpoints (μ : Fin 156 → ℝ) : Prop :=
  ∀ i (cap : Bool) e p s z, 0 ≤ e → e ≤ 1 / 2 →
    0 ≤ balancedFacetGap criticalQ (μ i)
      (fSlabKnot (if cap then i.succ else i.castSucc) : ℝ) e p s z

theorem facetStrip_balanced_bounds {t : Profile} (ht : OrderedInterior t)
    (hf₀ : 1 / 64 ≤ facetCoord t) (hf₁ : facetCoord t ≤ 1 / 20)
    (hτ : tau t ≤ 3 / 4) (hd : t 3 ≤ 1 / 400) :
    (1 / 64 ≤ t 2 + t 3 ∧ t 2 + t 3 ≤ 419 / 8000) ∧
      (0 ≤ t 0 - t 1 ∧ t 0 - t 1 ≤ 1 / 2) := by
  have hden : 0 < 1 - t 3 := by linarith only [hd]
  have hflo : (1 / 64 : ℝ) * (1 - t 3) ≤ t 2 := (le_div_iff₀ hden).mp hf₀
  have hfhi : t 2 ≤ (1 / 20 : ℝ) * (1 - t 3) := (div_le_iff₀ hden).mp hf₁
  have hdenτ : 0 < t 0 + t 1 := by linarith [ht.first_ge, ht.second_ge, ht.third_ge, ht.last_pos]
  have hτ' : t 0 ≤ (3 / 4 : ℝ) * (t 0 + t 1) := (div_le_iff₀ hdenτ).mp hτ
  have hpair : t 0 + t 1 ≤ 1 := by
    linarith only [ht.sum_four, ht.simplex.1 2, ht.simplex.1 3]
  exact ⟨⟨by linarith only [hflo, ht.last_pos], by linarith only [hfhi, hd]⟩,
    ⟨by linarith only [ht.first_ge], by linarith only [hτ', hpair]⟩⟩

/-- A common weight at each pair of closed endpoints covers every split and row in its slab. -/
theorem rowAt_of_fSlabEndpoints {t : Profile} (ht : IsSimplex t)
    (hl₀ : 74 / 4096 ≤ t 2 + t 3) (hl₁ : t 2 + t 3 ≤ 7 / 125)
    (he₀ : 0 ≤ t 0 - t 1) (he₁ : t 0 - t 1 ≤ 1 / 2)
    (μ : Fin 156 → ℝ) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1)
    (hslabs : FSlabEndpoints μ) : RowAt criticalQ t := by
  have hq : 1 ≤ criticalQ :=
    (by norm_num : (1 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le
  have hlo : (fSlabKnot 0 : ℝ) ≤ t 2 + t 3 := by
    rw [fSlabKnot_first]
    norm_num at hl₀ ⊢
    exact hl₀
  have hhi : t 2 + t 3 ≤ (fSlabKnot (Fin.last 156) : ℝ) := by
    rw [fSlabKnot_last]
    norm_num
    exact hl₁
  obtain ⟨i, hi₀, hi₁⟩ := exists_adjacent_knots 155 (f := fun i => (fSlabKnot i : ℝ)) hlo hhi
  refine rowAt_of_balancedFacetGap hq ht (hμ i).1 (hμ i).2 (fun p s z => ?_)
  obtain ⟨u, hu, huL⟩ := exists_interval_lerp hi₀ hi₁
  rw [huL]
  have he : |t 0 - t 1| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  exact balancedFacetGap_nonneg_lerp hq hu.1 hu.2 (hμ i).1 (hμ i).2 he
    (by simpa using hslabs i false _ p s z he₀ he₁)
    (by simpa using hslabs i true _ p s z he₀ he₁)

/-- The hypotheses cover the entire ordered F region, with overlap at \(74/4096\). -/
theorem rowAt_facetStrip_of_fSlabEndpoints
    (g1 : ∀ t : Profile, IsSimplex t → 1/4096 ≤ t 2 + t 3 → t 2 + t 3 ≤ 74/4096 →
      0 ≤ t 0 - t 1 → t 0 - t 1 ≤ 1/2 → RowAt criticalQ t)
    (μ : Fin 156 → ℝ) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (hslabs : FSlabEndpoints μ)
    {t : Profile} (ht : OrderedInterior t)
    (hf₀ : 1 / 64 ≤ facetCoord t) (hf₁ : facetCoord t ≤ 1 / 20)
    (hτ : tau t ≤ 3 / 4) (hd : t 3 ≤ 1 / 400) : RowAt criticalQ t := by
  obtain ⟨⟨hl₀, hl₁⟩, he₀, he₁⟩ := facetStrip_balanced_bounds ht hf₀ hf₁ hτ hd
  rcases le_total (t 2 + t 3) (74 / 4096 : ℝ) with h | h
  · exact g1 t ht.simplex ((by norm_num : (1 : ℝ)/4096 ≤ 1/64).trans hl₀) h he₀ he₁
  · exact rowAt_of_fSlabEndpoints ht.simplex h
      (hl₁.trans (by norm_num)) he₀ he₁ μ hμ hslabs

end HlawkaSchatten.BelowExponent
