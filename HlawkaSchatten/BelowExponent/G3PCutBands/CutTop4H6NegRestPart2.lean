/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegRestPart2Box : Box := ((((((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H6NegRestPart2Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 43500437793 51562587298), (.variance 465350984375)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 58075547817 66167939735), (.variance 429518966024)⟩)))
      (.cut 3 (7/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 74148400816 82075137842), (.variance 401631075374)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 99212464793), (.variance 379086269225)⟩))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 110431305439 117520130697), (.variance 360344711309)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 130501749339 136947236104), (.variance 344427492200)⟩)))
      (.cut 3 (11/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 157449726364), (.variance 330677819847)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178988954677), (.variance 318635983884)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegRestPart2_ok : CutTop4H6NegRestPart2Tree.ok CutTop4H6NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
