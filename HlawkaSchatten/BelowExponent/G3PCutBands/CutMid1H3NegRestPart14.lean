/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart14Box : Box := ((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart14Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.original (.row ⟨76698504228, 86531900009, (.direct 91625662891 95275083416), (.variance 480168384014)⟩))
        (.cut 3 (5/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 130501749339 133611499997), (.variance 364335371803)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 176529288980), (.variance 332894427977)⟩))))
      (.cut 3 (1/2)
        (.original (.row ⟨76698504228, 86531900009, (.direct 91625662891 95275083416), (.variance 480168384014)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 176529288980), (.variance 364335371803)⟩))))
    (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 176529288980), (.variance 480168384014)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart14_ok : CutMid1H3NegRestPart14Tree.geometryOK CutMid1H3NegPowerCache CutMid1H3NegRestPart14Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
