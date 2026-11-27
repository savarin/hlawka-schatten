/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3PosPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3PosPart7Box : Box := ((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid4H3PosPart7Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.row ⟨103236350715, 110576703735, (.direct 91625662891 97937549923), (.variance 472799529877)⟩)
        (.row ⟨103236350715, 110576703735, (.direct 174227225485 178195160637), (.variance 362385345116)⟩))
      (.cut 3 (1/2)
        (.row ⟨103236350715, 110576703735, (.direct 91625662891 97937549923), (.variance 472799529877)⟩)
        (.row ⟨103236350715, 110576703735, (.direct 174227225485 178195160637), (.variance 362385345116)⟩)))
    (.cut 0 (63/136)
      (.row ⟨103236350715, 110576703735, (.direct 174227225485 177697397627), (.variance 472799529877)⟩)
      (.row ⟨103236350715, 110576703735, (.direct 174227225485 178195160637), (.variance 470320709539)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H3PosPart7_checked : CutMid4H3PosPart7Tree.commonOK CutMid4H3PosPart7Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
