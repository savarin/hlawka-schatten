/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeReplay

/-! Staged row data for kernel replay of closed rectangles in a fixed parameter cell. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideNearRowData where
  row : Fin 27 × Fin 36
  samples : SideNearSamples

def SideNearRowData.box (D : SideNearRowData) (c : ParameterCell) (roots : Fin 3 → RatBounds) :
    SideNearBox := ⟨c, roots, sideNearExponent, sideURange D.row.1, sideVRange D.row.2⟩

def sideNearParameterGuard (c : ParameterCell) (roots : Fin 3 → RatBounds) : Bool :=
  (⟨c, roots, sideNearExponent, RatBounds.point 0, RatBounds.point 0⟩ : SideNearBox).parameterOK

def sideNearCanonicalValues (c : ParameterCell) (roots : Fin 3 → RatBounds) : SideNearParameterValues :=
  (⟨c, roots, sideNearExponent, RatBounds.point 0, RatBounds.point 0⟩ : SideNearBox).parameterValues

def SideNearRowData.checkFrom (D : SideNearRowData) (c : ParameterCell) (roots : Fin 3 → RatBounds)
    (P : SideNearParameterValues) : Bool :=
  let B := D.box c roots
  let I := (B.inputFrom D.samples P).evaluate.lower (sideAxisSign B.u) (sideAxisSign B.v)
  B.signsOK && B.multipliersOK D.samples && (I.detOK c.a.hi || I.rectangleOK c.a B.u B.v)

def SideNearRowData.check (D : SideNearRowData) (c : ParameterCell) (roots : Fin 3 → RatBounds) : Bool :=
  D.checkFrom c roots (sideNearCanonicalValues c roots)

theorem SideNearRowData.check_sound {D : SideNearRowData} {c : ParameterCell} {roots : Fin 3 → RatBounds}
    (hp : sideNearParameterGuard c roots = true) (h : D.check c roots = true) :
    SideConeOn c (sideURange D.row.1) (sideVRange D.row.2) := by
  simp only [SideNearRowData.check, SideNearRowData.checkFrom, Bool.and_eq_true, and_assoc] at h
  exact SideNearBox.checked (B := D.box c roots) hp h.2.1 rfl h.1 h.2.2

theorem SideNearRowData.checkFrom_sound {D : SideNearRowData} {c : ParameterCell} {roots : Fin 3 → RatBounds}
    {P : SideNearParameterValues} (hp : sideNearParameterGuard c roots = true)
    (hP : P = sideNearCanonicalValues c roots) (h : D.checkFrom c roots P = true) :
    SideConeOn c (sideURange D.row.1) (sideVRange D.row.2) := by
  subst P
  exact D.check_sound hp h

theorem sideNearRowList_sound {data : List SideNearRowData} {c : ParameterCell} {roots : Fin 3 → RatBounds}
    (hp : sideNearParameterGuard c roots = true) (h : data.all (fun D => D.check c roots) = true)
    {D : SideNearRowData} (hD : D ∈ data) : SideConeOn c (sideURange D.row.1) (sideVRange D.row.2) :=
  D.check_sound hp (List.all_eq_true.mp h D hD)

theorem sideNearStagedRowList_sound {data : List SideNearRowData} {c : ParameterCell}
    {roots : Fin 3 → RatBounds} {P : SideNearParameterValues}
    (hp : sideNearParameterGuard c roots = true) (hP : P = sideNearCanonicalValues c roots)
    (h : data.all (fun D => D.checkFrom c roots P) = true)
    {D : SideNearRowData} (hD : D ∈ data) : SideConeOn c (sideURange D.row.1) (sideVRange D.row.2) :=
  D.checkFrom_sound hp hP (List.all_eq_true.mp h D hD)

end HlawkaSchatten.BelowExponent.Vertex
