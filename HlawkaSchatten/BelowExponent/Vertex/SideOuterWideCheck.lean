/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideData
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerData.Chord
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerData.WideAxisBank
public import HlawkaSchatten.BelowExponent.Vertex.CornerSpanAxes

/-! Numerical rectangle tests shared by coarse VC and SC witnesses. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def outerWideEndpointIndex (e : Bool) : Fin 2 :=
  ⟨e.toNat, by cases e <;> decide⟩

def outerWideSpanAxes (S : SideOuterSpan) (e : Bool) : OuterAxisBounds :=
  match (outerWideAxisBank.get S.lo).find? (fun row => decide (row.1 = S.hi)) with
  | some row => row.2.get (outerWideEndpointIndex e)
  | none => outerWideSpanAxesCanonical S e

def outerWideRectOK (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) : Bool :=
  P.spanOK k U.bounds V.bounds (outerWideSpanAxes U) (outerWideSpanAxes V)
    (outerRpowChord outerChordQTable)

end HlawkaSchatten.BelowExponent.Vertex
