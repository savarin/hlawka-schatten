/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegPart24`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegPart24Box : Box := (((((⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid4H0NegPart24Tree : CertTree :=
  .cut 3 (1/2)
    (.row ⟨103236350715, 110576703735, (.direct 91625662891 93189301467), (.chord (.secant 1576955045448 279567886048 9247956506 30541785600) 91625974997 274877906944)⟩)
    (.row ⟨103236350715, 110576703735, (.direct 174227225485 175216301233), (.variance 366503899985)⟩)

set_option maxRecDepth 16000 in
theorem CutMid4H0NegPart24_checked : CutMid4H0NegPart24Tree.commonOK CutMid4H0NegPart24Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
