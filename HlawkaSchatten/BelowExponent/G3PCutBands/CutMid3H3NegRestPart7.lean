/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegRestPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegRestPart7Box : Box := ((((((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H3NegRestPart7Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (3/25)
      (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 24040286089), (.variance 612251190716)⟩))
      (.original (.row ⟨99345187399, 103236350716, (.direct 19358451269 24475494724), (.variance 608861584221)⟩)))
    (.cut 1 (3/25)
      (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 35592967368), (.variance 529260117899)⟩))
      (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 36056875820), (.variance 527338346875)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegRestPart7_ok : CutMid3H3NegRestPart7Tree.geometryOK CutMid3H3NegPowerCache CutMid3H3NegRestPart7Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
