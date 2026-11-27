/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegPart16Box : Box := (((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid2H1NegPart16Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨86531900008, 95281442641, (.direct 0 368725954), (.chord .universal 91625974997 274877906944)⟩)
    (.row ⟨86531900008, 95281442641, (.direct 30541785600 32809388292), (.chord .universal 91625974997 274877906944)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegPart16_checked : CutMid2H1NegPart16Tree.commonOK CutMid2H1NegPart16Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
