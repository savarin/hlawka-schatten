/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerGridData

/-! Bisection of closed groups of consecutive Grid B row intervals. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideOuterSpan where
  lo : Fin 35
  hi : Fin 35
  deriving DecidableEq, Repr

def SideOuterSpan.bounds (span : SideOuterSpan) : RatBounds :=
  ⟨outerNodes.get span.lo, outerNodes.get span.hi⟩

def SideOuterSpan.covers (span : SideOuterSpan) (i : Fin 34) : Prop :=
  span.lo.val ≤ i.val ∧ i.val < span.hi.val

instance (span : SideOuterSpan) (i : Fin 34) : Decidable (span.covers i) := by
  unfold SideOuterSpan.covers
  infer_instance

def SideOuterSpan.mid (span : SideOuterSpan) : Fin 35 :=
  ⟨(span.lo.val + span.hi.val) / 2, by
    have ha := span.lo.isLt
    have hb := span.hi.isLt
    omega⟩

def SideOuterSpan.first (span : SideOuterSpan) : SideOuterSpan := ⟨span.lo, span.mid⟩
def SideOuterSpan.second (span : SideOuterSpan) : SideOuterSpan := ⟨span.mid, span.hi⟩

def SideOuterSpan.intervals (span : SideOuterSpan) : List (Fin 34) :=
  (List.finRange (span.hi.val - span.lo.val)).map fun i =>
    ⟨span.lo.val + i.val, by
      have hhi := span.hi.isLt
      have hi := i.isLt
      omega⟩

def sideOuterStart (positive : Bool) : SideOuterSpan :=
  if positive then ⟨17,34⟩ else ⟨0,17⟩

def sideOuterAllSkipped (skip : Fin 3 → Fin 34 → Fin 34 → Bool)
    (k : Fin 3) (U V : SideOuterSpan) : Bool :=
  U.intervals.all fun i => V.intervals.all fun j => skip k i j

inductive SideOuterTree where
  | skip
  | rectangle
  | cutU (left right : SideOuterTree)
  | cutV (left right : SideOuterTree)
  deriving Repr

def SideOuterTree.check (rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool)
    (skip : Fin 3 → Fin 34 → Fin 34 → Bool) (k : Fin 3) :
    SideOuterTree → SideOuterSpan → SideOuterSpan → Bool
  | .skip, U, V => sideOuterAllSkipped skip k U V
  | .rectangle, U, V => rect k U V
  | .cutU left right, U, V => left.check rect skip k U.first V && right.check rect skip k U.second V
  | .cutV left right, U, V => left.check rect skip k U V.first && right.check rect skip k U V.second

def SideOuterTree.rectangleLeaves : SideOuterTree → SideOuterSpan → SideOuterSpan →
    List (SideOuterSpan × SideOuterSpan)
  | .skip, _, _ => []
  | .rectangle, U, V => [(U,V)]
  | .cutU left right, U, V => left.rectangleLeaves U.first V ++ right.rectangleLeaves U.second V
  | .cutV left right, U, V => left.rectangleLeaves U V.first ++ right.rectangleLeaves U V.second

end HlawkaSchatten.BelowExponent.Vertex
