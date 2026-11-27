/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegRestPart5Box : Box := ((((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid1H2NegRestPart5Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 58075547817 60972192974), (.variance 482946664417)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 91625662891 94357879775), (.variance 410271650686)⟩)))
        (.cut 3 (5/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 130501749339 132831605606), (.variance 365053348884)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 175952789661), (.variance 333289759669)⟩))))
      (.cut 3 (1/2)
        (.original (.row ⟨76698504228, 86531900009, (.direct 91625662891 94357879775), (.variance 482946664417)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 175952789661), (.variance 365053348884)⟩))))
    (.original (.row ⟨76698504228, 86531900009, (.direct 174227225485 175952789661), (.variance 482946664417)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H2NegRestPart5_ok : CutMid1H2NegRestPart5Tree.geometryOK CutMid1H2NegPowerCache CutMid1H2NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
