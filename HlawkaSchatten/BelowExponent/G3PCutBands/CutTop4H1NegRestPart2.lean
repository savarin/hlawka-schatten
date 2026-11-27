/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegRestPart2Box : Box := ((((((⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H1NegRestPart2Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.cut 3 (9/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 36810312175 39027160640), (.variance 484506461879)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 43500437793 45752337419), (.variance 461971647424)⟩)))
        (.cut 3 (11/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 50594077426 52864085531), (.variance 442651777370)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 58075547817 60348024950), (.variance 425835460194)⟩))))
      (.cut 3 (7/16)
        (.cut 3 (13/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 65931069018 68191451851), (.variance 411015285525)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 74148400816 76383030146), (.variance 397818045678)⟩)))
        (.cut 3 (15/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 84912557676), (.variance 385962135208)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 93770785246), (.variance 375230427021)⟩)))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.cut 3 (17/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 100866659274 102949273988), (.variance 365452381764)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 110431305439 112440281182), (.variance 356491886571)⟩)))
        (.cut 3 (19/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 120312008131 122236667580), (.variance 348238770622)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 130501749339 132331821283), (.variance 340602750037)⟩))))
      (.cut 3 (11/16)
        (.cut 3 (21/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 140994015657 142719594517), (.variance 333509019367)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 153394250640), (.variance 326894984529)⟩)))
        (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 175583058274), (.variance 320707803009)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegRestPart2_ok : CutTop4H1NegRestPart2Tree.ok CutTop4H1NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
