/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideCheck
public import HlawkaSchatten.BelowExponent.Vertex.SideOuterTreeSearch

/-! Check a proposed cover of all twelve signed quadrants at a shared VC point. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcOuterTreesOK (P : OuterPointBounds) (trees : Vector SideOuterTree 12) : Bool :=
  (List.finRange 3).all fun k => [false,true].all fun s => [false,true].all fun t =>
    (trees.get (outerTreeIndex k s t)).check (outerWideRectOK P) (fun _ _ _ => false) k
      (sideOuterStart s) (sideOuterStart t)

end HlawkaSchatten.BelowExponent.Vertex
