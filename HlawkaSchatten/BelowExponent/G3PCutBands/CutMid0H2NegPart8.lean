/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegPart8Box : Box := ((((⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid0H2NegPart8Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.row ⟨65259754744, 76698504229, (.direct 91625662891 93726147531), (.variance 484600673359)⟩)
        (.cut 3 (5/8)
          (.row ⟨65259754744, 76698504229, (.direct 130501749339 132293803215), (.variance 365476390523)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 174227225485 175554923881), (.variance 333522201281)⟩)))
      (.row ⟨65259754744, 76698504229, (.direct 174227225485 175554923881), (.variance 484600673359)⟩))
    (.row ⟨65259754744, 76698504229, (.direct 174227225485 175554923881), (.variance 484600673359)⟩)

set_option maxRecDepth 16000 in
theorem CutMid0H2NegPart8_checked : CutMid0H2NegPart8Tree.commonOK CutMid0H2NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
