/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3PosPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3PosPart1Box : Box := ((((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H3PosPart1Tree : CertTree :=
  .cut 1 (7/50)
    (.cut 3 (0)
      (.row ⟨103236350715, 106974752992, (.direct 0 1662800738), (.chord .universal 0 10180665226)⟩)
      (.cut 3 (1/8)
        (.row ⟨103236350715, 106974752992, (.direct 10180561190 15035859214), (.chord .universal 0 10180665226)⟩)
        (.row ⟨103236350715, 106974752992, (.direct 30541785600 36528021730), (.variance 605499873613)⟩)))
    (.cut 3 (0)
      (.row ⟨106974752991, 110576703735, (.direct 0 1870861037), (.chord .universal 0 10180665226)⟩)
      (.cut 3 (1/8)
        (.row ⟨106974752991, 110576703735, (.direct 10180561190 15439192436), (.chord .universal 0 10180665226)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 30541785600 37006551333), (.variance 602165471360)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid4H3PosPart1_checked : CutMid4H3PosPart1Tree.commonOK CutMid4H3PosPart1Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
