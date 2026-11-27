/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetNumeric
public import HlawkaSchatten.BelowExponent.Tangent.Sound

/-! Coverage of the three normalized row squares by the facet checker. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

def PassingBox (P : Prism) (j : Nat) (faces : List (Bool × TC.Face))
    (A1 A2 B1 B2 : Nat) : Prop :=
  ∃ ca cb, (faces.all fun (onBase, F) =>
    (onBase && isConeBox P j A2 B1 B2) || numericBoxOK F A1 A2 B1 B2 ca cb) = true

theorem checkTree_cover (P : Prism) (j : Nat) (faces : List (Bool × TC.Face))
    {tree : RowTree} {A1 A2 B1 B2 : Nat} (h : checkTree P j faces tree A1 A2 B1 B2 = true) :
    TC.BoxCover (PassingBox P j faces) A1 A2 B1 B2 := by
  induction tree generalizing A1 A2 B1 B2 with
  | box ca cb => exact .leaf ⟨ca, cb, h⟩
  | splitA left right ihl ihr =>
    simp only [checkTree, Bool.and_eq_true, TC.blt_true, and_assoc] at h
    exact .splitA _ (Nat.le_of_lt h.1) (Nat.le_of_lt h.2.1)
      (ihl h.2.2.1) (ihr h.2.2.2)
  | splitB left right ihl ihr =>
    simp only [checkTree, Bool.and_eq_true, TC.blt_true, and_assoc] at h
    exact .splitB _ (Nat.le_of_lt h.1) (Nat.le_of_lt h.2.1)
      (ihl h.2.2.1) (ihr h.2.2.2)

theorem checkChart_cover (P : Prism) (j k l : Nat) {tree : RowTree}
    (h : checkChart P j k l tree = true) :
    TC.BoxCover (PassingBox P j (chartFaces P j k l)) 0 (2 * ctx.Da) 0 (2 * ctx.Da) :=
  checkTree_cover P j _ h

theorem PassingBox.vertex {P : Prism} {j : Nat} {faces : List (Bool × TC.Face)}
    {A1 A2 B1 B2 : Nat} (h : PassingBox P j faces A1 A2 B1 B2)
    {onBase : Bool} {F : TC.Face} (hF : (onBase, F) ∈ faces) :
    (onBase = true ∧ isConeBox P j A2 B1 B2 = true) ∨
      ∃ ca cb, numericBoxOK F A1 A2 B1 B2 ca cb = true := by
  obtain ⟨ca, cb, h⟩ := h
  have h := List.all_eq_true.mp h (onBase, F) hF
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  exact h.imp id (fun h => ⟨ca, cb, h⟩)

end HlawkaSchatten.BelowExponent.FacetNumeric
