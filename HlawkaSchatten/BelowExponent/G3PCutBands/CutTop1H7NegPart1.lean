/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegPart1Box : Box := ((((((⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H7NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4031178183), (.variance 830450603057)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 0 2321017507), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 3 (1/64)
            (.row ⟨114055813619, 117423580140, (.direct 377054043 3526765411), (.variance 1042495520754)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 1131165907 4908978594), (.variance 914179271749)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 3393509060 8147191353), (.variance 827498371996)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 16271159185), (.variance 714007305375)⟩))
      (.cut 3 (3/16)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 26293930781), (.variance 587736766500)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 37986365340), (.variance 515076768300)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H7NegPart1_checked : CutTop1H7NegPart1Tree.commonOK CutTop1H7NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
