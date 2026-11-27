/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegPart8Box : Box := (((((((((((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 2 (7/32)).lowerChild 3 (0)).upperChild 1 (2/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid1H2NegPart8Tree : CertTree :=
  .cut 2 (11/64)
    (.row ⟨81775466252, 86531900009, (.direct 10180561190 7600725348), (.variance 703382633359)⟩)
    (.row ⟨81775466252, 86531900009, (.direct 10180561190 7600725348), (.chord (.midpoint ⟨396525368313, 170528183576, 205375192051, 338032314580, 230470348417, 115939405651⟩) 16864782083 24716235638)⟩)

set_option maxRecDepth 16000 in
theorem CutMid1H2NegPart8_checked : CutMid1H2NegPart8Tree.commonOK CutMid1H2NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
