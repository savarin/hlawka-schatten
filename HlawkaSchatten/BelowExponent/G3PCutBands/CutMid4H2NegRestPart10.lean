/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegRestPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegRestPart10Box : Box := ((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid4H2NegRestPart10Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨103236350715, 110576703735, .zero, (.variance 308952589599)⟩)))
        (.original (.row ⟨103236350715, 110576703735, .zero, (.variance 308952589599)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨103236350715, 110576703735, (.direct 391506126583 387518655120), (.variance 251236846957)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 593382169971 581780367639), (.variance 225878343674)⟩)))
          (.original (.row ⟨103236350715, 110576703735, (.direct 391506126583 387518655120), (.variance 251236846957)⟩)))
        (.original (.row ⟨103236350715, 110576703735, (.direct 391506126583 387518655120), (.variance 251236846957)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩))
              (.original (.row ⟨103236350715, 110576703735, (.direct 1366046989981 1321962756048), (.variance 182193752566)⟩)))
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1929550545221), (.variance 165016399507)⟩)))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1929550545221), (.variance 165016399507)⟩)))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩))))
      (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegRestPart10_ok : CutMid4H2NegRestPart10Tree.geometryOK CutMid4H2NegPowerCache CutMid4H2NegRestPart10Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
