/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegRestPart2Box : Box := ((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H6NegRestPart2Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308070412538)⟩)))
        (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308070412538)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 385488901761), (.variance 251582574902)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 477177410769), (.variance 237911216285)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 575890326604), (.variance 226481017508)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 385488901761), (.variance 251582574902)⟩)))
        (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 385488901761), (.variance 251582574902)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 793085009592), (.variance 208275946890)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1299663518777), (.variance 183007187562)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1892937472114), (.variance 165846273544)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3308812166908), (.variance 143283549414)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4996424554251), (.chord .universal 0 10180665226)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 793085009592), (.variance 208275946890)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1892937472114), (.variance 165846273544)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3308812166908), (.variance 143283549414)⟩))))
      (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 793085009592), (.variance 208275946890)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegRestPart2_ok : CutTop3H6NegRestPart2Tree.geometryOK CutTop3H6NegPowerCache CutTop3H6NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
