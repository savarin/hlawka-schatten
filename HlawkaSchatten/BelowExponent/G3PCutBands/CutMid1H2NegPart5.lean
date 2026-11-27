/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegPart5Box : Box := ((((((((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid1H2NegPart5Tree : CertTree :=
  .cut 1 (2/25)
    (.cut 3 (3/16)
      (.row ⟨76698504228, 81775466253, (.direct 19358451269 21603964505), (.variance 634208692228)⟩)
      (.row ⟨76698504228, 81775466253, (.direct 30541785600 32979234251), (.variance 541407815907)⟩))
    (.cut 3 (3/16)
      (.row ⟨81775466252, 86531900009, (.direct 19358451269 21904547605), (.variance 631758289398)⟩)
      (.row ⟨81775466252, 86531900009, (.direct 30541785600 33303333944), (.variance 540077835106)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H2NegPart5_checked : CutMid1H2NegPart5Tree.commonOK CutMid1H2NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
