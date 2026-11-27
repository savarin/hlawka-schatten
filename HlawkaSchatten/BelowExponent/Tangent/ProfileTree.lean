/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.CellSplits
public import HlawkaSchatten.BelowExponent.Tangent.CentreLeaves

/-! A successful profile-tree check covers the parent hull outside the open centre cube. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

private theorem walk_append_success {left right : Option (List TC.Geom)} {geoms : List TC.Geom}
    (h : (match left, right with
      | some a, some b => some (a ++ b)
      | _, _ => none) = some geoms) :
    ∃ a b, left = some a ∧ right = some b ∧ geoms = a ++ b := by
  cases left <;> cases right <;> simp_all

/-- A point on or beyond the cube surface belongs to one of the exact certified leaf hulls. -/
theorem walkCT_covers_outside_cube {H : TC.Hdr} (hd : 0 < H.rcD) {tree : TC.CT}
    {G : TC.Geom} {geoms : List TC.Geom} (hG : CellGeometry G)
    (hw : TC.walkCT H tree G = some geoms) {t : Profile} (ht : t ∈ cellSet G)
    (hOut : ∃ i, (H.rcN : ℝ) / H.rcD ≤ |t i - 1 / 4|) :
    ∃ L ∈ geoms, t ∈ cellSet L := by
  induction tree generalizing G geoms with
  | T i j left right ihL ihR =>
      cases hs : TC.tsplit G i j with
      | none => simp [TC.walkCT, hs] at hw
      | some children =>
          obtain ⟨L, R⟩ := children
          obtain ⟨hL, hR, hcover⟩ := tangentialSplit_cover hG hs
          simp only [TC.walkCT, hs] at hw
          obtain ⟨a, b, ha, hb, rfl⟩ := walk_append_success hw
          rcases hcover ht with hl | hr
          · obtain ⟨K, hk, hK⟩ := ihL hL ha hl
            exact ⟨K, List.mem_append_left _ hk, hK⟩
          · obtain ⟨K, hk, hK⟩ := ihR hR hb hr
            exact ⟨K, List.mem_append_right _ hk, hK⟩
  | R p q left right ihL ihR =>
      let gate := Nat.blt 0 q && Nat.blt (G.l1n * q) (p * G.l1d) && Nat.blt (p * G.l2d) (G.l2n * q)
      have hg : gate = true := by
        by_contra! h
        simp [TC.walkCT, show (Nat.blt 0 q && Nat.blt (G.l1n * q) (p * G.l1d) &&
          Nat.blt (p * G.l2d) (G.l2n * q)) ≠ true from h] at hw
      have htests : (0 < q ∧ G.l1n * q < p * G.l1d) ∧ p * G.l2d < G.l2n * q := by
        simpa only [gate, Bool.and_eq_true, TC.blt_true] using hg
      obtain ⟨hL, hR, hcover⟩ := radialSplit_cover hG htests.1.1 htests.1.2 htests.2
      simp only [TC.walkCT, show (Nat.blt 0 q && Nat.blt (G.l1n * q) (p * G.l1d) &&
        Nat.blt (p * G.l2d) (G.l2n * q)) = true from hg, ite_true] at hw
      obtain ⟨a, b, ha, hb, rfl⟩ := walk_append_success hw
      rcases hcover ht with hl | hr
      · obtain ⟨K, hk, hK⟩ := ihL hL ha hl
        exact ⟨K, List.mem_append_left _ hk, hK⟩
      · obtain ⟨K, hk, hK⟩ := ihR hR hb hr
        exact ⟨K, List.mem_append_right _ hk, hK⟩
  | c =>
      have hc : TC.inCube H G = true := by
        by_contra! h
        simp [TC.walkCT, h] at hw
      obtain ⟨i, hi⟩ := hOut
      exact (not_lt_of_ge hi (inside_of_inCube hd hG.vertexDen_pos hc ht i)).elim
  | C =>
      simp only [TC.walkCT, Option.some.injEq] at hw
      subst geoms
      exact ⟨G, by simp, ht⟩

end HlawkaSchatten.BelowExponent.Tangent
