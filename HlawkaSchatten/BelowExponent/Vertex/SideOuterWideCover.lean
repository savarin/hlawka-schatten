/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideData
public import HlawkaSchatten.BelowExponent.Vertex.CornerGrid
public import HlawkaSchatten.BelowExponent.Vertex.SideCornerLinks

/-! Restrict each checked wider rectangle to every original closed rectangle it contains. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

private theorem outerNodes_order (i j : Fin 35) (h : i.val ≤ j.val) :
    outerNodes.get i ≤ outerNodes.get j := by
  have all : ∀ i j : Fin 35, i.val ≤ j.val → outerNodes.get i ≤ outerNodes.get j := by decide +kernel
  exact all i j h

theorem SideOuterSpan.bounds_contains {U : SideOuterSpan} {i : Fin 34} (hi : U.covers i)
    {x : ℝ} (hx : (outerInterval i).Contains x) : U.bounds.Contains x := by
  have hlo := outerNodes_order U.lo i.castSucc (show U.lo.val ≤ i.castSucc.val from hi.1)
  have hhi := outerNodes_order i.succ U.hi (show i.succ.val ≤ U.hi.val from hi.2)
  exact ⟨(show ((U.bounds).lo : ℝ) ≤ (outerInterval i).lo by exact_mod_cast hlo).trans hx.1,
    hx.2.trans (show ((outerInterval i).hi : ℝ) ≤ U.bounds.hi by exact_mod_cast hhi)⟩

private theorem SideOuterSpan.split_cover {U : SideOuterSpan} {i : Fin 34} (h : U.covers i) :
    U.first.covers i ∨ U.second.covers i := by
  rcases lt_or_ge i.val U.mid.val with hleft | hright
  · exact Or.inl ⟨h.1, hleft⟩
  · exact Or.inr ⟨hright, h.2⟩

private theorem SideOuterSpan.mem_intervals_of_covers {U : SideOuterSpan} {i : Fin 34} (hi : U.covers i) :
    i ∈ U.intervals := by
  have hlo := hi.1
  have hhi := hi.2
  let offset : Fin (U.hi.val - U.lo.val) := ⟨i.val - U.lo.val, by omega⟩
  refine List.mem_map.mpr ⟨offset, List.mem_finRange offset, Fin.ext ?_⟩
  change U.lo.val + (i.val - U.lo.val) = i.val
  omega

private theorem sideOuterStart_cover (i : Fin 34) : ∃ s : Bool, (sideOuterStart s).covers i := by
  rcases lt_or_ge i.val 17 with h | h
  · exact ⟨false, Nat.zero_le _, h⟩
  · exact ⟨true, h, i.isLt⟩

/-- Every unskipped fine rectangle is contained, by knot indices, in one checked leaf. -/
theorem SideOuterTree.find_rectangle
    {rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool}
    {skip : Fin 3 → Fin 34 → Fin 34 → Bool}
    {tree : SideOuterTree} {k : Fin 3} {U V : SideOuterSpan}
    (ht : tree.check rect skip k U V = true) {i j : Fin 34}
    (hi : U.covers i) (hj : V.covers j) (hkeep : skip k i j = false) :
    ∃ A B, (A,B) ∈ tree.rectangleLeaves U V ∧ A.covers i ∧ B.covers j ∧ rect k A B = true := by
  induction tree generalizing U V with
  | skip =>
    have hh := List.all_eq_true.mp ht i (U.mem_intervals_of_covers hi)
    have hs := List.all_eq_true.mp hh j (V.mem_intervals_of_covers hj)
    rw [hkeep] at hs
    cases hs
  | rectangle =>
    exact ⟨U, V, List.mem_singleton.mpr rfl, hi, hj, ht⟩
  | cutU left right ihLeft ihRight =>
    obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp ht
    rcases U.split_cover hi with hi | hi
    · obtain ⟨A, B, hm, hA, hB, hcert⟩ := ihLeft hleft hi hj
      exact ⟨A, B, List.mem_append_left _ hm, hA, hB, hcert⟩
    · obtain ⟨A, B, hm, hA, hB, hcert⟩ := ihRight hright hi hj
      exact ⟨A, B, List.mem_append_right _ hm, hA, hB, hcert⟩
  | cutV left right ihLeft ihRight =>
    obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp ht
    rcases V.split_cover hj with hj | hj
    · obtain ⟨A, B, hm, hA, hB, hcert⟩ := ihLeft hleft hi hj
      exact ⟨A, B, List.mem_append_left _ hm, hA, hB, hcert⟩
    · obtain ⟨A, B, hm, hA, hB, hcert⟩ := ihRight hright hi hj
      exact ⟨A, B, List.mem_append_right _ hm, hA, hB, hcert⟩

def SideOuterWideAt (p : SideCornerEntry) (k : Fin 3) (U V : SideOuterSpan) : Prop :=
  ∀ ⦃u v : ℝ⦄, U.bounds.Contains u → V.bounds.Contains v →
    CornerMarginAt p.margin.get (outerFaceRow k u v) p.a p.b p.eta

theorem SideOuterTree.sound {p : SideCornerEntry}
    {rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool}
    {skip : Fin 3 → Fin 34 → Fin 34 → Bool}
    (hrect : ∀ k U V, rect k U V = true → SideOuterWideAt p k U V)
    {tree : SideOuterTree} {k : Fin 3} {U V : SideOuterSpan}
    (ht : tree.check rect skip k U V = true) {i j : Fin 34}
    (hi : U.covers i) (hj : V.covers j) (hkeep : skip k i j = false) :
    OuterRectangleAt p.margin.get p.a p.b p.eta k i j := by
  obtain ⟨A, B, _, hA, hB, hc⟩ := tree.find_rectangle ht hi hj hkeep
  intro u v hu hv
  exact hrect k A B hc (A.bounds_contains hA hu) (B.bounds_contains hB hv)

theorem sideOuterPoint_of_trees {p : SideCornerEntry}
    {rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool}
    {skip : Fin 3 → Fin 34 → Fin 34 → Bool}
    (hskip : ∀ k i j, skip k i j = outerSideSkip k i j)
    (hrect : ∀ k U V, rect k U V = true → SideOuterWideAt p k U V)
    {trees : Fin 3 → Bool → Bool → SideOuterTree}
    (h : ∀ k s t, (trees k s t).check rect skip k (sideOuterStart s) (sideOuterStart t) = true) :
    p.Valid := by
  intro z hz
  apply cornerMargin_of_sc_grid _ z hz
  intro k i j hkeep
  obtain ⟨s, hi⟩ := sideOuterStart_cover i
  obtain ⟨t, hj⟩ := sideOuterStart_cover j
  exact SideOuterTree.sound hrect (h k s t) hi hj ((hskip k i j).trans hkeep)

theorem vcOuterPoint_of_trees {p : SideCornerEntry}
    {rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool}
    (hrect : ∀ k U V, rect k U V = true → SideOuterWideAt p k U V)
    {trees : Fin 3 → Bool → Bool → SideOuterTree}
    (h : ∀ k s t, (trees k s t).check rect (fun _ _ _ => false) k
      (sideOuterStart s) (sideOuterStart t) = true) : p.ValidFor (fun _ => True) := by
  intro z _
  apply cornerMargin_of_vc_grid _ z
  intro k i j
  obtain ⟨s, hi⟩ := sideOuterStart_cover i
  obtain ⟨t, hj⟩ := sideOuterStart_cover j
  exact SideOuterTree.sound hrect (h k s t) hi hj rfl

end HlawkaSchatten.BelowExponent.Vertex
