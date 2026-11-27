/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegPart15`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegPart15Box : Box := ((((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid1H2NegPart15Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.row ⟨76698504228, 86531900009, (.direct 58075547817 60972192974), (.variance 482946664417)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 91625662891 94357879775), (.variance 410271650686)⟩))
        (.cut 3 (5/8)
          (.row ⟨76698504228, 86531900009, (.direct 130501749339 132831605606), (.variance 365053348884)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 174227225485 175952789661), (.variance 333289759669)⟩)))
      (.cut 3 (1/2)
        (.row ⟨76698504228, 86531900009, (.direct 91625662891 94357879775), (.variance 482946664417)⟩)
        (.row ⟨76698504228, 86531900009, (.direct 174227225485 175952789661), (.variance 365053348884)⟩)))
    (.row ⟨76698504228, 86531900009, (.direct 174227225485 175952789661), (.variance 482946664417)⟩)

set_option maxRecDepth 16000 in
theorem CutMid1H2NegPart15_checked : CutMid1H2NegPart15Tree.commonOK CutMid1H2NegPart15Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
