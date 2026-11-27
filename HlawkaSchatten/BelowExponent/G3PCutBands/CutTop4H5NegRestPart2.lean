/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegRestPart2Box : Box := ((((((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H5NegRestPart2Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 43500437793 50380098550), (.variance 468976249299)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 58075547817 64988177306), (.variance 432039532306)⟩)))
      (.cut 3 (7/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 74148400816 80924660979), (.variance 403449593146)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.variance 380428082992)⟩))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 110431305439 116497541276), (.variance 361346797580)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 130501749339 136019485591), (.variance 345178381173)⟩)))
      (.cut 3 (11/16)
        (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 156635508800), (.variance 331237508933)⟩))
        (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178305844413), (.variance 319046699068)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegRestPart2_ok : CutTop4H5NegRestPart2Tree.ok CutTop4H5NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
