/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegPart1Box : Box := ((((((⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H4NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 1337461457), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨120689819474, 123862991200, (.direct 1131165907 3602234793), (.chord .universal 0 10180665226)⟩)
          (.cut 2 (1/16)
            (.row ⟨120689819474, 123862991200, (.direct 3393509060 6596659450), (.variance 905171782288)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 3393509060 6596659450), (.chord (.secant 1785626301543 394636532653 9797445721 78325586121) 3393555298 10180665226)⟩)))
        (.cut 3 (3/32)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 10210014778), (.variance 757162629711)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 14374205462), (.variance 668570008962)⟩)))
      (.cut 3 (3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 24175991139), (.variance 607610715350)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 35737713343), (.variance 526625983411)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H4NegPart1_checked : CutTop3H4NegPart1Tree.commonOK CutTop3H4NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
