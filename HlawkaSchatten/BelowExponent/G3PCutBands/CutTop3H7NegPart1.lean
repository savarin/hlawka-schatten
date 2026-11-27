/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegPart1Box : Box := ((((((⟨![63/136, 9/50, 0, -8], ![9/17, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H7NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 3391807444), (.variance 868867363551)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 0 2817109798), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨120689819474, 123862991200, (.direct 1131165907 5533663332), (.variance 988266397159)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 3393509060 8871241147), (.variance 802633568555)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 17138050606), (.variance 699214447754)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 30541785600 38997564469), (.variance 580520646179)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H7NegPart1_checked : CutTop3H7NegPart1Tree.commonOK CutTop3H7NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
