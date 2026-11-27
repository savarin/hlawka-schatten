/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterGrid

/-! Closed parameter covers for the vertex middle and band. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcParameterGrid {n : ℕ} (first depth : RatBounds)
    (second : Fin n → RatBounds × ℕ) (nη : ℕ) : List ParameterCell :=
  (List.finRange n).flatMap fun i =>
    (⟨first.subinterval n i.val, (second i).1, depth⟩ : ParameterCell).grid 1 (second i).2 nη

private theorem vcParameterGrid_cover {n nη : ℕ} {first depth : RatBounds}
    {second : Fin n → RatBounds × ℕ} {a b η : ℝ}
    (ha : first.Contains a) (hη : depth.Contains η) (hn : 0 < n) (hnη : 0 < nη)
    (hb : ∀ i : Fin n, (first.subinterval n i.val).Contains a →
      (second i).1.Contains b ∧ 0 < (second i).2) :
    ∃ c ∈ vcParameterGrid first depth second nη, c.Contains a b η := by
  obtain ⟨i, hi⟩ := RatBounds.subinterval_cover ha hn
  obtain ⟨hb', hn'⟩ := hb i hi
  let slab : ParameterCell := ⟨first.subinterval n i.val, (second i).1, depth⟩
  have hp : slab.Contains a b η := ⟨hi, hb', hη⟩
  obtain ⟨c, hc, ht⟩ := ParameterCell.grid_cover hp (by decide : 0 < 1) hn' hnη
  exact ⟨c, List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hc⟩, ht⟩

def vcMiddleA : RatBounds := ⟨1/20, 7/20⟩

def vcMiddleSecond : Fin 12 → RatBounds × ℕ :=
  ![(⟨1/8,19/40⟩,14), (⟨1/10,19/40⟩,15), (⟨1/10,9/20⟩,14), (⟨1/8,9/20⟩,13),
    (⟨3/20,17/40⟩,11), (⟨7/40,17/40⟩,10), (⟨1/5,2/5⟩,8), (⟨9/40,2/5⟩,7),
    (⟨1/4,3/8⟩,5), (⟨11/40,3/8⟩,4), (⟨3/10,7/20⟩,2), (⟨13/40,7/20⟩,1)]

def vcMiddleParameterGrid : List ParameterCell :=
  vcParameterGrid vcMiddleA ⟨0,1/18⟩ vcMiddleSecond 2

private theorem vcMiddleParameterGrid_cover {a b η : ℝ}
    (ha : 1/20 ≤ a) (hab : a ≤ b) (hb : b ≤ 1-a-b) (hs : 1/5 ≤ a+b)
    (hη : 0 ≤ η) (hη' : η ≤ 1/18) :
    ∃ c ∈ vcMiddleParameterGrid, c.Contains a b η := by
  refine vcParameterGrid_cover (n := 12) (nη := 2) ?_ ?_ (by decide) (by decide) ?_
  · norm_num [RatBounds.Contains, vcMiddleA]
    exact ⟨ha, by linarith only [hab, hb]⟩
  · norm_num [RatBounds.Contains]
    exact ⟨hη, hη'⟩
  · intro i hi
    fin_cases i <;>
      norm_num [RatBounds.Contains, RatBounds.subinterval, RatBounds.knot,
        vcMiddleA, vcMiddleSecond] at hi ⊢ <;>
      constructor <;> linarith only [hi.1, hi.2, hab, hb, hs]

def vcBandA : RatBounds := ⟨1/40, 1/20⟩

def vcBandSecond : Fin 2 → RatBounds × ℕ :=
  ![(⟨13/80,39/80⟩,26), (⟨3/20,39/80⟩,27)]

def vcBandParameterGrid : List ParameterCell :=
  vcParameterGrid vcBandA ⟨0,1/10⟩ vcBandSecond 4

theorem vcBandParameterGrid_cover {a b η : ℝ}
    (ha : 1/40 ≤ a) (ha' : a ≤ 1/20) (hb : b ≤ 1-a-b) (hs : 1/5 ≤ a+b)
    (hη : 0 ≤ η) (hη' : η ≤ 1/10) :
    ∃ c ∈ vcBandParameterGrid, c.Contains a b η := by
  refine vcParameterGrid_cover (n := 2) (nη := 4) ?_ ?_ (by decide) (by decide) ?_
  · norm_num [RatBounds.Contains, vcBandA]
    exact ⟨ha, ha'⟩
  · norm_num [RatBounds.Contains]
    exact ⟨hη, hη'⟩
  · intro i hi
    fin_cases i <;>
      norm_num [RatBounds.Contains, RatBounds.subinterval, RatBounds.knot,
        vcBandA, vcBandSecond] at hi ⊢ <;>
      constructor <;> linarith only [hi.1, hi.2, hb, hs]

def vcMiddleSplit (i : ℕ) : Bool := [1,28,29,31,59,61].contains i

/-- The original cells that remain, followed by the six two-by-two-by-two refinements. -/
def vcMiddleRefinedGrid : List ParameterCell :=
  let indexed := vcMiddleParameterGrid.zipIdx
  (indexed.filter fun entry => !vcMiddleSplit entry.2).map Prod.fst ++
    (indexed.filter fun entry => vcMiddleSplit entry.2).flatMap fun entry => entry.1.grid 2 2 2

theorem vcMiddleRefinedGrid_cover {a b η : ℝ}
    (ha : 1/20 ≤ a) (hab : a ≤ b) (hb : b ≤ 1-a-b) (hs : 1/5 ≤ a+b)
    (hη : 0 ≤ η) (hη' : η ≤ 1/18) :
    ∃ c ∈ vcMiddleRefinedGrid, c.Contains a b η := by
  obtain ⟨c, hc, ht⟩ := vcMiddleParameterGrid_cover ha hab hb hs hη hη'
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
  have hm : (c, i) ∈ vcMiddleParameterGrid.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi, he⟩)
  cases hs' : vcMiddleSplit i with
  | false =>
      refine ⟨c, List.mem_append_left _ (List.mem_map.mpr ⟨(c,i), ?_, rfl⟩), ht⟩
      exact List.mem_filter.mpr ⟨hm, by simp [hs']⟩
  | true =>
      obtain ⟨d, hd, hdt⟩ := ParameterCell.grid_cover ht
        (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
      refine ⟨d, List.mem_append_right _ (List.mem_flatMap.mpr ⟨(c,i), ?_, hd⟩), hdt⟩
      exact List.mem_filter.mpr ⟨hm, hs'⟩

end HlawkaSchatten.BelowExponent.Vertex
