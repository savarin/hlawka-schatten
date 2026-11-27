/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegChartPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegChartPart6Box : Box := ((((((((⟨![9/136, 19/100, 0, -1], ![9/68, 1/5, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H1NegChartPart6Tree : RatioChart :=
  .cut 3 (-3/16)
    (.row ⟨123862991199, 126950446638, (.direct 9401829831 11077222744), 43500686443, 91625974997, 339360881355/274877906944, .leaf (.secant 947956812746 18760293062 2782915881 19358451269)⟩)
    (.cut 0 (27/272)
      (.row ⟨123862991199, 126950446638, (.direct 5775011364 6864036123), 43500686443, 91625974997, 353621284245/274877906944, .leaf (.secant 905317911275 9710076544 831549814 10180561190)⟩)
      (.row ⟨123862991199, 126950446638, (.direct 5443209626 6886270098), 43500686443, 91625974997, 362531429079/274877906944, .leaf (.secant 883038795102 5861616439 114172333 10180561190)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegChartPart6_ok : CutTop4H1NegChartPart6Tree.ok CutTop4H1NegChartPart6Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
