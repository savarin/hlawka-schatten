/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3PosPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3PosPart6Box : Box := ((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid3H3PosPart6Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.row ⟨95281442640, 103236350716, (.direct 91625662891 97028037856), (.variance 475264391674)⟩)
        (.row ⟨95281442640, 103236350716, (.direct 174227225485 177627343942), (.variance 363045111981)⟩))
      (.row ⟨95281442640, 103236350716, (.direct 174227225485 177627343942), (.variance 475264391674)⟩))
    (.row ⟨95281442640, 103236350716, (.direct 174227225485 177627343942), (.variance 475264391674)⟩)

set_option maxRecDepth 16000 in
theorem CutMid3H3PosPart6_checked : CutMid3H3PosPart6Tree.commonOK CutMid3H3PosPart6Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
