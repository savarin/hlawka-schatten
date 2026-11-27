/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegPart7Box : Box := (((((⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid0H2NegPart7Tree : CertTree :=
  .row ⟨65259754744, 76698504229, (.direct 30541785600 32659646221), (.chord .universal 91625974997 274877906944)⟩

set_option maxRecDepth 16000 in
theorem CutMid0H2NegPart7_checked : CutMid0H2NegPart7Tree.commonOK CutMid0H2NegPart7Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
