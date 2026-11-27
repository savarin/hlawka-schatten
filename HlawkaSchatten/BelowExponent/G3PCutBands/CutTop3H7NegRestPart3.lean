/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegRestPart3Box : Box := ((⟨![63/136, 9/50, 0, -8], ![9/17, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H7NegRestPart3Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 307795489033)⟩)))
        (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 307795489033)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 384632047654), (.variance 251729213128)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 475555407831), (.variance 238123433910)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 573407086967), (.variance 226737440169)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 384632047654), (.variance 251729213128)⟩)))
        (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 384632047654), (.variance 251729213128)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 788614822332), (.variance 208584447014)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1290279123009), (.variance 183354796010)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1877537993405), (.variance 166201393080)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3278539028225), (.variance 143628820918)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4947965491951), (.chord .universal 0 10180665226)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 788614822332), (.variance 208584447014)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1877537993405), (.variance 166201393080)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3278539028225), (.variance 143628820918)⟩))))
      (.cut 3 (5)
        (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 788614822332), (.variance 208584447014)⟩))
        (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3278539028225), (.variance 143628820918)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H7NegRestPart3_ok : CutTop3H7NegRestPart3Tree.ok CutTop3H7NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
