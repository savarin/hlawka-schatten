/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart20`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart20Box : Box := ((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart20Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (1/10)
      (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 23192064358), (.variance 619116518642)⟩))
      (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 23612525680), (.variance 615669295946)⟩)))
    (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 35136153758), (.variance 533114168895)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart20_ok : CutMid2H3NegRestPart20Tree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegRestPart20Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
