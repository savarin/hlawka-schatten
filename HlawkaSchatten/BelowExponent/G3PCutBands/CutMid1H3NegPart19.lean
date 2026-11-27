/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegPart19`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegPart19Box : Box := (((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid1H3NegPart19Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨76698504228, 86531900009, (.direct 0 791497279), (.chord .universal 91625974997 274877906944)⟩)
    (.row ⟨76698504228, 86531900009, (.direct 30541785600 34243258062), (.chord .universal 91625974997 274877906944)⟩)

set_option maxRecDepth 16000 in
theorem CutMid1H3NegPart19_checked : CutMid1H3NegPart19Tree.commonOK CutMid1H3NegPart19Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
