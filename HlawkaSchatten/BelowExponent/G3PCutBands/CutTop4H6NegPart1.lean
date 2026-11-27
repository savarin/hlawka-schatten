/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegPart1Box : Box := ((((((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H6NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨123862991199, 126950446638, (.direct 0 2494649276), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 5129580736), (.chord .universal 0 10180665226)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 3393509060 8403949458), (.variance 820964269785)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 16579794853), (.variance 710166681982)⟩))
      (.cut 3 (3/16)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 26635686910), (.variance 585883526906)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 38347478951), (.variance 513977492113)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegPart1_checked : CutTop4H6NegPart1Tree.commonOK CutTop4H6NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
