/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeFastTree

/-! Replay larger parameter slabs with direct references to shared checked parameters. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

inductive SideFastDirectTree where
  | leaf (P : SideFastParameter) (checked : P.check = true) (mixed : FactorSamples)
  | bisect (axis : Fin 3) (lo hi : SideFastDirectTree)

def SideFastDirectTree.check (G : SideFastGrid) (row : Fin 27 × Fin 36)
    (C : ParameterCell) : SideFastDirectTree → Bool
  | .leaf P _ M => C.containedIn P.cell &&
      P.leafCheck (sideURange row.1) (sideVRange row.2) (G.u row.1) (G.v row.2) M
  | .bisect axis lo hi => check G row (C.sideHalf axis false) lo &&
      check G row (C.sideHalf axis true) hi

theorem SideFastDirectTree.check_sound {G : SideFastGrid} (hG : G.check = true)
    (row : Fin 27 × Fin 36) (C : ParameterCell) (T : SideFastDirectTree)
    (hT : T.check G row C = true) : SideConeOn C (sideURange row.1) (sideVRange row.2) := by
  induction T generalizing C with
  | leaf P hp M =>
    simp only [SideFastDirectTree.check, Bool.and_eq_true] at hT
    have hb := Bool.and_eq_true_iff.mp hG
    have hU := List.all_eq_true.mp hb.1 row.1 (by simp)
    have hV := List.all_eq_true.mp hb.2 row.2 (by simp)
    have h := SideFastParameter.leafCheck_sound hp hU hV hT.2
    intro a b η u v hc hu hv
    exact h (ParameterCell.containedIn_sound hT.1 hc) hu hv
  | bisect axis lo hi il ir =>
    simp only [SideFastDirectTree.check, Bool.and_eq_true] at hT
    intro a b η u v hc hu hv
    rcases ParameterCell.sideHalf_cover hc axis with hl | hr
    · exact il _ hT.1 hl hu hv
    · exact ir _ hT.2 hr hu hv

structure SideFastDirectRow where
  row : Fin 27 × Fin 36
  tree : SideFastDirectTree

def SideFastDirectRow.check (G : SideFastGrid) (C : ParameterCell) (R : SideFastDirectRow) : Bool :=
  R.tree.check G R.row C

theorem sideFastDirectRows_sound {G : SideFastGrid} {C : ParameterCell} {data : List SideFastDirectRow}
    (hG : G.check = true) (ht : data.all (SideFastDirectRow.check G C) = true)
    (hcover : data.map SideFastDirectRow.row = sideRowGrid) :
    ∀ row ∈ sideRowGrid, SideConeOn C (sideURange row.1) (sideVRange row.2) := by
  intro row hr
  rw [← hcover] at hr
  obtain ⟨R, hmem, hrow⟩ := List.mem_map.mp hr
  subst row
  exact R.tree.check_sound hG R.row C (List.all_eq_true.mp ht R hmem)

end HlawkaSchatten.BelowExponent.Vertex
