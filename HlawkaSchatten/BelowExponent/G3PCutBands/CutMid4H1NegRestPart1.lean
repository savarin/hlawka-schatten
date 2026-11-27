/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegRestPart1Box : Box := (((((((⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid4H1NegRestPart1Tree : RatioRemainder :=
  .cut 1 (7/50)
    (.cut 3 (-1/8)
      (.original (.row ⟨103236350715, 106974752992, (.direct 10180561190 7442991880), (.variance 707255813547)⟩))
      (.cut 1 (27/200)
        (.cut 0 (27/136)
          (.original (.row ⟨103236350715, 105123556200, (.direct 0 330228512), (.chord .universal 0 10180665226)⟩))
          (.original (.row ⟨103236350715, 105123556200, (.direct 0 521000054), (.chord .universal 0 10180665226)⟩)))
        (.cut 0 (27/136)
          (.original (.row ⟨105123556199, 106974752992, (.direct 0 351314263), (.chord .universal 0 10180665226)⟩))
          (.original (.row ⟨105123556199, 106974752992, (.direct 0 554266949), (.chord .universal 0 10180665226)⟩)))))
    (.cut 3 (-1/8)
      (.original (.row ⟨106974752991, 110576703735, (.direct 10180561190 7244935472), (.variance 712268426654)⟩))
      (.cut 1 (29/200)
        (.original (.row ⟨106974752991, 108791878640, (.direct 0 588473114), (.chord .universal 0 10180665226)⟩))
        (.original (.row ⟨108791878639, 110576703735, (.direct 0 623620387), (.chord .universal 0 10180665226)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H1NegRestPart1_ok : CutMid4H1NegRestPart1Tree.ok CutMid4H1NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
