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
public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideInteger

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

/-- The rectangle test in exact rationals: the reference for `outerWideRectOK`. -/
def outerWideRectOKRat (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) : Bool :=
  P.spanOK k U.bounds V.bounds (outerWideSpanAxes U) (outerWideSpanAxes V)
    (outerRpowChord outerChordQTable)

/-- The rectangle test in integers, equal to `outerWideRectOKRat` by `outerWideRectOK_eq_rat`. -/
def outerWideRectOK (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) : Bool :=
  let (m,n) := outerTransverse k
  decide (outerNodeNum.get U.lo < outerNodeNum.get U.hi ∧
      outerNodeNum.get V.lo < outerNodeNum.get V.hi ∧
      (0 ≤ outerNodeNum.get U.lo ∨ outerNodeNum.get U.hi ≤ 0) ∧
      (0 ≤ outerNodeNum.get V.lo ∨ outerNodeNum.get V.hi ≤ 0)) &&
    [false,true].all fun x => [false,true].all fun y =>
      P.spanEndpointOKInt k m n U V x y (outerWideSpanAxes U) (outerWideSpanAxes V)

theorem outerWideRectOK_eq_rat (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) :
    outerWideRectOK P k U V = outerWideRectOKRat P k U V := by
  unfold outerWideRectOK outerWideRectOKRat OuterPointBounds.spanOK
  rcases h : outerTransverse k with ⟨m, n⟩
  simp only [outerSpanEndpointOK_int, outerSpanBounds_lo, outerSpanBounds_hi,
    outerDiv256_nonneg_iff, outerDiv256_nonpos_iff, outerDiv256_lt_iff]

end HlawkaSchatten.BelowExponent.Vertex
