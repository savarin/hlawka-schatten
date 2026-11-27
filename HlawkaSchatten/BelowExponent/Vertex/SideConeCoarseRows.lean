/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeFastDirect

/-! Closed wider row rectangles with the same near-cone parameter checks. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideCoarseAxis where
  bounds : RatBounds
  data : SideFastAxis
  checked : data.check bounds = true

def SideFastDirectTree.checkOn (U V : SideCoarseAxis) (C : ParameterCell) : SideFastDirectTree → Bool
  | .leaf P _ M => C.containedIn P.cell && P.leafCheck U.bounds V.bounds U.data V.data M
  | .bisect k l r => l.checkOn U V (C.sideHalf k false) && r.checkOn U V (C.sideHalf k true)

theorem SideFastDirectTree.checkOn_sound (U V : SideCoarseAxis) (C : ParameterCell)
    (T : SideFastDirectTree) (hT : T.checkOn U V C = true) : SideConeOn C U.bounds V.bounds := by
  induction T generalizing C with
  | leaf P hp M =>
    obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp hT
    intro a b η u v ha hu hv
    exact SideFastParameter.leafCheck_sound hp U.checked V.checked ht
      (ParameterCell.containedIn_sound hc ha) hu hv
  | bisect k l r ihl ihr =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hT
    intro a b η u v ha hu hv
    rcases ParameterCell.sideHalf_cover ha k with hleft | hright
    · exact ihl _ hl hleft hu hv
    · exact ihr _ hr hright hu hv

structure SideCoarseTile where
  u : SideCoarseAxis
  v : SideCoarseAxis
  tree : SideFastDirectTree

def SideCoarseTile.check (C : ParameterCell) (T : SideCoarseTile) : Bool :=
  T.tree.checkOn T.u T.v C

def SideCoarseTile.covers (T : SideCoarseTile) (ij : Fin 27 × Fin 36) : Bool :=
  (sideURange ij.1).containedIn T.u.bounds && (sideVRange ij.2).containedIn T.v.bounds

theorem sideCoarseTiles_sound {C : ParameterCell} {tiles : List SideCoarseTile}
    (ht : tiles.all (SideCoarseTile.check C) = true)
    (hcover : sideRowGrid.all (fun ij => tiles.any (fun tile => tile.covers ij)) = true) :
    ∀ ij ∈ sideRowGrid, SideConeOn C (sideURange ij.1) (sideVRange ij.2) := by
  intro ij hr a b η u v hp hu hv
  obtain ⟨T, hmem, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcover ij hr)
  obtain ⟨hU, hV⟩ := Bool.and_eq_true_iff.mp hb
  exact T.tree.checkOn_sound T.u T.v C (List.all_eq_true.mp ht T hmem) hp
    (RatBounds.containedIn_sound hU hu) (RatBounds.containedIn_sound hV hv)

end HlawkaSchatten.BelowExponent.Vertex
