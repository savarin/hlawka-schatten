/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3PosPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3PosPart1Box : Box := ((((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H3PosPart1Tree : CertTree :=
  .cut 1 (3/25)
    (.cut 3 (0)
      (.row ⟨95281442640, 99345187400, (.direct 0 1280471935), (.chord .universal 0 10180665226)⟩)
      (.cut 3 (1/8)
        (.cut 3 (1/16)
          (.row ⟨95281442640, 99345187400, (.direct 3393509060 6499868527), (.chord .universal 0 10180665226)⟩)
          (.row ⟨95281442640, 99345187400, (.direct 10180561190 14253640534), (.variance 767804829962)⟩))
        (.row ⟨95281442640, 99345187400, (.direct 30541785600 35592967368), (.variance 612251190716)⟩)))
    (.cut 3 (0)
      (.row ⟨99345187399, 103236350716, (.direct 0 1466013107), (.chord .universal 0 10180665226)⟩)
      (.cut 3 (1/8)
        (.cut 3 (1/16)
          (.row ⟨99345187399, 103236350716, (.direct 3393509060 6811423945), (.chord .universal 0 10180665226)⟩)
          (.row ⟨99345187399, 103236350716, (.direct 10180561190 14640730591), (.variance 760008703889)⟩))
        (.row ⟨99345187399, 103236350716, (.direct 30541785600 36056875820), (.variance 608861584221)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H3PosPart1_checked : CutMid3H3PosPart1Tree.commonOK CutMid3H3PosPart1Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
