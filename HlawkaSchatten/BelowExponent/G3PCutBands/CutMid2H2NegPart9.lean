/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegPart9Box : Box := (((((((((((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 1 (1/10)).lowerChild 1 (21/200)).upperChild 0 (45/136)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid2H2NegPart9Tree : CertTree :=
  .cut 2 (1/16)
    (.row ⟨91020629597, 93177423805, (.direct 3393509060 5332857081), (.variance 968326504464)⟩)
    (.cut 2 (3/32)
      (.row ⟨91020629597, 93177423805, (.direct 3393509060 5332857081), (.chord (.secant 1567332306820 274497644339 9071789234 95514691679) 3393555298 6452870597)⟩)
      (.row ⟨91020629597, 93177423805, (.direct 3393509060 5332857081), (.chord (.secant 1216337361723 108350850004 251226575 60540550200) 6452870597 10180665226)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegPart9_checked : CutMid2H2NegPart9Tree.commonOK CutMid2H2NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
