/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterGrid

/-! Parameter geometry for the 510 original SC-S, SC-D and SC-E cells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def scDepthS : List RatBounds :=
  (List.range 4).map (fun k => (⟨0,1/10⟩ : RatBounds).subinterval 4 k)

def scDepthD : List RatBounds :=
  (List.range 2).map (fun k => (⟨1/10,1/8⟩ : RatBounds).subinterval 2 k)

def scDepthE : List RatBounds :=
  (List.range 3).map (fun k => (⟨1/8,13/80⟩ : RatBounds).subinterval 3 k) ++ [⟨13/80,1/6⟩]

def scDirectionSlab (a b : RatBounds) (n : ℕ) (depths : List RatBounds) : List ParameterCell :=
  (List.range n).flatMap fun k => depths.map fun η => ⟨a,b.subinterval n k,η⟩

def scParameterFamily (depths : List RatBounds) : List ParameterCell :=
  scDirectionSlab ⟨0,1/80⟩ ⟨3/16,1/2⟩ 25 depths ++
    scDirectionSlab ⟨1/80,1/40⟩ ⟨7/40,1/2⟩ 26 depths

def scParameterGrid : List ParameterCell :=
  scParameterFamily scDepthS ++ (scParameterFamily scDepthD ++ scParameterFamily scDepthE)

theorem scParameterGrid_length : scParameterGrid.length = 510 := by decide +kernel

private theorem scDirectionSlab_cover {A B E : RatBounds} {depths : List RatBounds} {n : ℕ}
    {a b η : ℝ} (ha : A.Contains a) (hb : B.Contains b) (he : E.Contains η)
    (hn : 0 < n) (hmem : E ∈ depths) :
    ∃ c ∈ scDirectionSlab A B n depths, c.Contains a b η := by
  obtain ⟨k, hk⟩ := RatBounds.subinterval_cover hb hn
  refine ⟨⟨A, B.subinterval n k.val,E⟩, ?_, ha, hk, he⟩
  exact List.mem_flatMap.mpr ⟨k, by simp, List.mem_map.mpr ⟨E, hmem, rfl⟩⟩

private theorem scParameterFamily_cover {a b η : ℝ} {E : RatBounds} {D : List RatBounds}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1/40) (hb : b ≤ 1/2) (hab : 1/5 ≤ a+b)
    (he : E.Contains η) (hE : E ∈ D) : ∃ c ∈ scParameterFamily D, c.Contains a b η := by
  by_cases hmid : a ≤ 1/80
  · have hA : (⟨0,1/80⟩ : RatBounds).Contains a := by
      norm_num [RatBounds.Contains]
      exact ⟨ha,hmid⟩
    have hB : (⟨3/16,1/2⟩ : RatBounds).Contains b := by
      norm_num [RatBounds.Contains]
      exact ⟨by linarith only [hmid, hab], hb⟩
    obtain ⟨c, hc, hp⟩ := scDirectionSlab_cover hA hB he (by decide : 0 < 25) hE
    exact ⟨c, List.mem_append_left _ hc, hp⟩
  · have hA : (⟨1/80,1/40⟩ : RatBounds).Contains a := by
      norm_num [RatBounds.Contains]
      exact ⟨(le_of_not_ge hmid),ha₁⟩
    have hB : (⟨7/40,1/2⟩ : RatBounds).Contains b := by
      norm_num [RatBounds.Contains]
      exact ⟨by linarith only [ha₁, hab], hb⟩
    obtain ⟨c, hc, hp⟩ := scDirectionSlab_cover hA hB he (by decide : 0 < 26) hE
    exact ⟨c, List.mem_append_right _ hc, hp⟩

private theorem scDepth_grid_cover {E : RatBounds} {η : ℝ} {n : ℕ} (h : E.Contains η) (hn : 0 < n) :
    ∃ e ∈ (List.range n).map (fun k => E.subinterval n k), e.Contains η := by
  obtain ⟨k, hk⟩ := RatBounds.subinterval_cover h hn
  exact ⟨_, List.mem_map.mpr ⟨k, by simp, rfl⟩, hk⟩

theorem scParameterGrid_cover {a b η : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1/40)
    (hb : b ≤ 1/2) (hab : 1/5 ≤ a+b) (hη : 0 ≤ η) (hη₁ : η ≤ 1/6) :
    ∃ c ∈ scParameterGrid, c.Contains a b η := by
  by_cases hs : η ≤ 1/10
  · have he : (⟨0,1/10⟩ : RatBounds).Contains η := by norm_num [RatBounds.Contains]; exact ⟨hη, hs⟩
    obtain ⟨e, he₀, hev⟩ := scDepth_grid_cover he (by decide : 0 < 4)
    obtain ⟨c, hm, hc⟩ := scParameterFamily_cover ha ha₁ hb hab hev (show e ∈ scDepthS from he₀)
    exact ⟨c, List.mem_append_left _ hm, hc⟩
  by_cases hd : η ≤ 1/8
  · have he : (⟨1/10,1/8⟩ : RatBounds).Contains η := by
      norm_num [RatBounds.Contains]
      exact ⟨le_of_not_ge hs, hd⟩
    obtain ⟨e, he₀, hev⟩ := scDepth_grid_cover he (by decide : 0 < 2)
    obtain ⟨c, hm, hc⟩ := scParameterFamily_cover ha ha₁ hb hab hev (show e ∈ scDepthD from he₀)
    exact ⟨c, List.mem_append_right _ (List.mem_append_left _ hm), hc⟩
  have hex : ∃ e ∈ scDepthE, e.Contains η := by
    by_cases hh : η ≤ 13/80
    · have he : (⟨1/8,13/80⟩ : RatBounds).Contains η := by
        norm_num [RatBounds.Contains]
        exact ⟨le_of_not_ge hd, hh⟩
      obtain ⟨e, he₀, hev⟩ := scDepth_grid_cover he (by decide : 0 < 3)
      exact ⟨e, List.mem_append_left _ he₀, hev⟩
    · refine ⟨⟨13/80,1/6⟩, List.mem_append_right _ (by simp), ?_⟩
      norm_num [RatBounds.Contains]
      exact ⟨le_of_not_ge hh, hη₁⟩
  obtain ⟨e, he₀, hev⟩ := hex
  obtain ⟨c, hm, hc⟩ := scParameterFamily_cover ha ha₁ hb hab hev he₀
  exact ⟨c, List.mem_append_right _ (List.mem_append_right _ hm), hc⟩

end HlawkaSchatten.BelowExponent.Vertex
