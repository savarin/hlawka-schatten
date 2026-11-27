/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegRestPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegRestPart4Box : Box := ((((⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid1H1NegRestPart4Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 58075547817 60000961799), (.variance 485780527627)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 91625662891 93443954901), (.variance 411620042406)⟩)))
        (.cut 3 (5/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 130501749339 132053397536), (.variance 365776172907)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 175376986626), (.variance 333686696608)⟩))))
      (.cut 3 (1/2)
        (.original (.row ⟨76698504228, 86531900009, (.direct 91625662891 93443954901), (.variance 485780527627)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 175376986626), (.variance 365776172907)⟩))))
    (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 175376986626), (.variance 485780527627)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H1NegRestPart4_ok : CutMid1H1NegRestPart4Tree.geometryOK CutMid1H1NegPowerCache CutMid1H1NegRestPart4Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
