/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideData
public import HlawkaSchatten.BelowExponent.Vertex.CornerWidePowerValues
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowers
public import HlawkaSchatten.BelowExponent.Vertex.OuterRowCheck

/-! The exact canonical four multipliers on a signed coarse row span. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def outerWideSpanAxesCanonical (S : SideOuterSpan) (e : Bool) : OuterAxisBounds :=
  let R := S.bounds
  let x := outerEndpoint R e
  let m := outerSpanMidpoint R
  let px := outerWideAxisQAt x
  let pm := outerWideAxisQAt m
  outerSpanAxisBounds R e (.ofRat px) (outerSignedFromQ x px)
    (.ofRat pm) (outerSignedFromQ m pm) (outerSlopeFromQ m pm)

end HlawkaSchatten.BelowExponent.Vertex
