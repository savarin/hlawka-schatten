/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart11`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart11Box : Box := ((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart11Tree : RatioRemainder :=
  .cut 1 (2/25)
    (.original (.row ⟨76698504228, 81775466253, (.direct 30541785600 33806907894), (.variance 626100874367)⟩))
    (.cut 3 (3/16)
      (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 22778756699), (.variance 622593494013)⟩))
      (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 34243258062), (.variance 535046590360)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart11_ok : CutMid1H3NegRestPart11Tree.ok CutMid1H3NegRestPart11Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
