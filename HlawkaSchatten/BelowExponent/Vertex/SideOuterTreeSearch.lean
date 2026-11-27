/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideData

/-! Generate candidate bisections for the shared VC and SC corner checks. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def outerSearchSpanWidth (S : SideOuterSpan) : ℚ :=
  S.bounds.hi - S.bounds.lo

def outerSearchCanSplit (S : SideOuterSpan) : Bool :=
  decide (S.lo.val + 1 < S.hi.val)

/-- Search only proposes a tree. The closed-cover checker validates every leaf. -/
partial def outerSearchTree (rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool)
    (skip : Fin 3 → Fin 34 → Fin 34 → Bool) (k : Fin 3) (U V : SideOuterSpan) : Option SideOuterTree := do
  if sideOuterAllSkipped skip k U V then
    return .skip
  if rect k U V then
    return .rectangle
  if outerSearchCanSplit U && (!outerSearchCanSplit V ||
      decide (outerSearchSpanWidth V ≤ outerSearchSpanWidth U)) then
    return .cutU (← outerSearchTree rect skip k U.first V) (← outerSearchTree rect skip k U.second V)
  if outerSearchCanSplit V then
    return .cutV (← outerSearchTree rect skip k U V.first) (← outerSearchTree rect skip k U V.second)
  none

def SideOuterTree.rectangleCount : SideOuterTree → Nat
  | .skip => 0
  | .rectangle => 1
  | .cutU l r | .cutV l r => l.rectangleCount + r.rectangleCount

def SideOuterTree.dataSource : SideOuterTree → String
  | .skip => ".skip"
  | .rectangle => ".rectangle"
  | .cutU l r => s!"(.cutU {l.dataSource} {r.dataSource})"
  | .cutV l r => s!"(.cutV {l.dataSource} {r.dataSource})"

def outerSearchQuadrants (rect : Fin 3 → SideOuterSpan → SideOuterSpan → Bool)
    (skip : Fin 3 → Fin 34 → Fin 34 → Bool) : Option (List SideOuterTree) := do
  (List.finRange 3).flatMap (fun k =>
    [false,true].flatMap fun u => [false,true].map fun v => (k,u,v)) |>.mapM fun (k,u,v) =>
      outerSearchTree rect skip k (sideOuterStart u) (sideOuterStart v)

def outerTreeIndex (k : Fin 3) (s t : Bool) : Fin 12 :=
  ⟨k.val*4+s.toNat*2+t.toNat, by
    have hk := k.isLt
    cases s <;> cases t <;> simp <;> omega⟩

end HlawkaSchatten.BelowExponent.Vertex
