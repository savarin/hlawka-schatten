/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2PosPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2PosPart1Box : Box := ((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid4H2PosPart1Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨103236350715, 110576703735, .zero, (.variance 308952589599)⟩))
        (.row ⟨103236350715, 110576703735, .zero, (.variance 308952589599)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.cut 3 (43/32)
                (.row ⟨103236350715, 110576703735, (.direct 391506126583 387518655120), (.variance 251236846957)⟩)
                (.row ⟨103236350715, 110576703735, (.direct 439055879922 433339220278), (.variance 243991147213)⟩))
              (.row ⟨103236350715, 110576703735, (.direct 488587506629 481022489358), (.variance 237411754740)⟩))
            (.cut 3 (29/16)
              (.row ⟨103236350715, 110576703735, (.direct 593382169971 581780367639), (.variance 225878343674)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 705506110649 689438710376), (.variance 216055957991)⟩)))
          (.cut 3 (13/8)
            (.row ⟨103236350715, 110576703735, (.direct 391506126583 387518655120), (.variance 251236846957)⟩)
            (.row ⟨103236350715, 110576703735, (.direct 593382169971 581780367639), (.variance 225878343674)⟩)))
        (.row ⟨103236350715, 110576703735, (.direct 391506126583 387518655120), (.variance 251236846957)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)
                (.row ⟨103236350715, 110576703735, (.direct 1082810704946 1051002063672), (.variance 193472125989)⟩))
              (.row ⟨103236350715, 110576703735, (.direct 1366046989981 1321962756048), (.variance 182193752566)⟩))
            (.cut 3 (17/4)
              (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1929550545221), (.variance 165016399507)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 2723407729414 2617926343702), (.variance 152345945250)⟩)))
          (.cut 3 (13/2)
            (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩)
            (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5111750349060), (.variance 127859335871)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)
                (.row ⟨103236350715, 110576703735, (.direct 1082810704946 1051002063672), (.variance 193472125989)⟩))
              (.row ⟨103236350715, 110576703735, (.direct 1366046989981 1321962756048), (.variance 182193752566)⟩))
            (.cut 3 (17/4)
              (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1929550545221), (.variance 165016399507)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 2723407729414 2617926343702), (.variance 152345945250)⟩)))
          (.cut 3 (13/2)
            (.cut 3 (23/4)
              (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 4397286982341 4213414951460), (.variance 134496630908)⟩))
            (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5111750349060), (.variance 127859335871)⟩))))
      (.cut 3 (5)
        (.cut 3 (7/2)
          (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1929550545221), (.variance 165016399507)⟩))
        (.cut 3 (13/2)
          (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5111750349060), (.variance 127859335871)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H2PosPart1_checked : CutMid4H2PosPart1Tree.commonOK CutMid4H2PosPart1Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
