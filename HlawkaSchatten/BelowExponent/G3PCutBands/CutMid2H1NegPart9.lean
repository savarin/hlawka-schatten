/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegPart9Box : Box := (((((((((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 2 (7/32)).lowerChild 1 (1/10)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid2H1NegPart9Tree : CertTree :=
  .cut 2 (11/64)
    (.row ⟨86531900008, 91020629598, (.direct 10180561190 8232971135), (.variance 688818348335)⟩)
    (.row ⟨86531900008, 91020629598, (.direct 10180561190 8232971135), (.chord (.midpoint ⟨451612059741, 132869852188, 197027428502, 348132473063, 210193273254, 142715130703⟩) 16864782083 24716235638)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegPart9_checked : CutMid2H1NegPart9Tree.commonOK CutMid2H1NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
