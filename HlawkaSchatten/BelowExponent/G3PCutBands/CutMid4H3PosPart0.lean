/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3PosPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3PosPart0Box : Box := (((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid4H3PosPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3240275053229), (.variance 144071030098)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 824633666698 742079377775), (.variance 211933069403)⟩))
        (.cut 3 (-5)
          (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3240275053229), (.variance 144071030098)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 824633666698 742079377775), (.variance 211933069403)⟩)))
      (.row ⟨103236350715, 110576703735, (.direct 824633666698 742079377775), (.variance 211933069403)⟩))
    (.cut 2 (1/2)
      (.row ⟨103236350715, 110576703735, (.direct 30541785600 20825587808), (.variance 540212518530)⟩)
      (.cut 3 (-9/8)
        (.row ⟨103236350715, 110576703735, (.direct 331294831298 289741338864), (.variance 271113430154)⟩)
        (.cut 2 (3/4)
          (.cut 1 (7/50)
            (.row ⟨103236350715, 106974752992, (.direct 30541785600 21475902333), (.chord .universal 91625974997 174227471798)⟩)
            (.row ⟨106974752991, 110576703735, (.direct 30541785600 20825587808), (.chord .universal 91625974997 174227471798)⟩))
          (.row ⟨103236350715, 110576703735, (.direct 30541785600 20825587808), (.chord .universal 174227471798 274877906944)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H3PosPart0_checked : CutMid4H3PosPart0Tree.commonOK CutMid4H3PosPart0Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
