/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegRestPart3Box : Box := ((⟨![9/68, 9/50, 0, -8], ![27/136, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H2NegRestPart3Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 309178540824)⟩)))
        (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 309178540824)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 388923349190), (.variance 250998920471)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 585862822905), (.variance 225465122969)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 388923349190), (.variance 250998920471)⟩)))
        (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 388923349190), (.variance 250998920471)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 811058807186), (.variance 207057316034)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1954998166981), (.variance 164451219051)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3430927993789), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 811058807186), (.variance 207057316034)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3430927993789), (.variance 141930213726)⟩))))
      (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 811058807186), (.variance 207057316034)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H2NegRestPart3_ok : CutTop3H2NegRestPart3Tree.geometryOK CutTop3H2NegPowerCache CutTop3H2NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
