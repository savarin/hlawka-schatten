/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRestPart19`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestPart19Box : Box := ((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid2H2NegRestPart19Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨86531900008, 95281442641, .zero, (.variance 309204812723)⟩)))
        (.original (.row ⟨86531900008, 95281442641, .zero, (.variance 309204812723)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 388642462220), (.variance 251046410165)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 593382169971 585046076117), (.variance 225547501696)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 388642462220), (.variance 251046410165)⟩)))
        (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 388642462220), (.variance 251046410165)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1949902463019), (.variance 164563646391)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩))))
      (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRestPart19_ok : CutMid2H2NegRestPart19Tree.geometryOK CutMid2H2NegPowerCache CutMid2H2NegRestPart19Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
