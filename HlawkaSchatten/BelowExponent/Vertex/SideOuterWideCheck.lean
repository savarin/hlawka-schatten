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
public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideKernel

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

/-- The rectangle test in integers, equal to `outerWideRectOKRat` by
`outerWideRectOKInt_eq_rat`. -/
def outerWideRectOKInt (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) : Bool :=
  let (m,n) := outerTransverse k
  decide (outerNodeNum.get U.lo < outerNodeNum.get U.hi ∧
      outerNodeNum.get V.lo < outerNodeNum.get V.hi ∧
      (0 ≤ outerNodeNum.get U.lo ∨ outerNodeNum.get U.hi ≤ 0) ∧
      (0 ≤ outerNodeNum.get V.lo ∨ outerNodeNum.get V.hi ≤ 0)) &&
    [false,true].all fun x => [false,true].all fun y =>
      P.spanEndpointOKInt k m n U V x y (outerWideSpanAxes U) (outerWideSpanAxes V)

theorem outerWideRectOKInt_eq_rat (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) :
    outerWideRectOKInt P k U V = outerWideRectOKRat P k U V := by
  unfold outerWideRectOKInt outerWideRectOKRat OuterPointBounds.spanOK
  rcases h : outerTransverse k with ⟨m, n⟩
  simp only [outerSpanEndpointOK_int, outerSpanBounds_lo, outerSpanBounds_hi,
    outerDiv256_nonneg_iff, outerDiv256_nonpos_iff, outerDiv256_lt_iff]

/-- `List.find?` on an axis-bank row by a direct walk. -/
def outerBankFindK (h : ℕ) (l : List (Fin 35 × Vector OuterAxisBounds 2)) :
    Option (Fin 35 × Vector OuterAxisBounds 2) :=
  List.rec (motive := fun _ => Option (Fin 35 × Vector OuterAxisBounds 2)) none
    (fun a _ ih => Bool.rec ih (some a) (Nat.beq a.1.val h)) l

theorem outerBankFindK_eq (h : Fin 35) (l : List (Fin 35 × Vector OuterAxisBounds 2)) :
    outerBankFindK h.val l = l.find? (fun row => decide (row.1 = h)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.find?_cons]
    by_cases hb : a.1 = h
    · have : Nat.beq a.1.val h.val = true := by rw [hb]; exact Nat.beq_refl _
      simp [outerBankFindK, hb]
    · have : Nat.beq a.1.val h.val = false := by
        cases hc : Nat.beq a.1.val h.val
        · rfl
        · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hc)) hb
      simp only [outerBankFindK, this, hb, decide_false] at ih ⊢
      exact ih

/-- `outerWideSpanAxes` by direct walks; the canonical fallback is unchanged. -/
def outerWideSpanAxesK (S : SideOuterSpan) (e : Bool) : OuterAxisBounds :=
  Option.rec (motive := fun _ => OuterAxisBounds) (outerWideSpanAxesCanonical S e)
    (fun row => Bool.rec (outerListGetK (outerWideSpanAxesCanonical S e) row.2.toList 0)
      (outerListGetK (outerWideSpanAxesCanonical S e) row.2.toList 1) e)
    (outerBankFindK S.hi.val (outerListGetK [] outerWideAxisBank.toList S.lo.val))

theorem outerWideSpanAxesK_eq (S : SideOuterSpan) :
    outerWideSpanAxesK S = outerWideSpanAxes S := by
  funext e
  unfold outerWideSpanAxesK outerWideSpanAxes
  rw [outerListGetK_vector, outerBankFindK_eq]
  cases (outerWideAxisBank.get S.lo).find? (fun row => decide (row.1 = S.hi)) with
  | none => rfl
  | some row =>
    cases e
    · exact outerListGetK_vector _ row.2 (outerWideEndpointIndex false)
    · exact outerListGetK_vector _ row.2 (outerWideEndpointIndex true)

/-- The rectangle test in kernel form, equal to `outerWideRectOKInt` by `outerWideRectOK_eq_int`. -/
noncomputable def outerWideRectOK (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) :
    Bool :=
  let (m,n) := outerTransverse k
  (Nat.blt U.lo.val U.hi.val && Nat.blt V.lo.val V.hi.val &&
      (Nat.ble 17 U.lo.val || Nat.ble U.hi.val 17) &&
      (Nat.ble 17 V.lo.val || Nat.ble V.hi.val 17)) &&
    [false,true].all fun x => [false,true].all fun y =>
      P.spanEndpointOKK k m n U V x y (outerWideSpanAxesK U) (outerWideSpanAxesK V)

theorem outerWideRectOK_eq_int (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) :
    outerWideRectOK P k U V = outerWideRectOKInt P k U V := by
  unfold outerWideRectOK outerWideRectOKInt
  rcases h : outerTransverse k with ⟨m, n⟩
  simp only [outerSpanEndpointOKK_eq, outerWideSpanAxesK_eq, ← outerNode_nonneg_iff,
    ← outerNode_nonpos_iff, ← outerNode_lt_iff, Bool.decide_and, Bool.decide_or, Bool.and_assoc]

theorem outerWideRectOK_eq_rat (P : OuterPointBounds) (k : Fin 3) (U V : SideOuterSpan) :
    outerWideRectOK P k U V = outerWideRectOKRat P k U V :=
  (outerWideRectOK_eq_int P k U V).trans (outerWideRectOKInt_eq_rat P k U V)

end HlawkaSchatten.BelowExponent.Vertex
