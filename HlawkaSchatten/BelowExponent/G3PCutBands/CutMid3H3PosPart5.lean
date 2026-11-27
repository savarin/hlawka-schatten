/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3PosPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3PosPart5Box : Box := (((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid3H3PosPart5Tree : CertTree :=
  .cut 3 (0)
    (.cut 1 (3/25)
      (.row ⟨95281442640, 99345187400, (.direct 0 1280471935), (.chord .universal 91625974997 274877906944)⟩)
      (.cut 2 (3/4)
        (.row ⟨99345187399, 103236350716, (.direct 0 1466013107), (.chord .universal 91625974997 174227471798)⟩)
        (.row ⟨99345187399, 103236350716, (.direct 0 1466013107), (.chord .universal 174227471798 274877906944)⟩)))
    (.row ⟨95281442640, 103236350716, (.direct 30541785600 36056875820), (.chord (.midpoint ⟨567455228532, 69546882115, 113858919093, 513714175245, 165521579435, 261022851525⟩) 91625974997 274877906944)⟩)

set_option maxRecDepth 16000 in
theorem CutMid3H3PosPart5_checked : CutMid3H3PosPart5Tree.commonOK CutMid3H3PosPart5Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
