/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart4Box : Box := (((((((((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (3/25)).lowerChild 1 (23/200)).upperChild 0 (45/136)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart4Tree : CertTree :=
  .cut 2 (1/16)
    (.row ⟨95281442640, 97336292160, (.direct 3393509060 5546329653), (.variance 953796539012)⟩)
    (.cut 2 (3/32)
      (.row ⟨95281442640, 97336292160, (.direct 3393509060 5546329653), (.chord (.secant 1595043166523 289159613014 11538007106 101191738538) 3393555298 6452870597)⟩)
      (.row ⟨95281442640, 97336292160, (.direct 3393509060 5546329653), (.chord (.secant 1233149213866 115299969199 16723721 64138860934) 6452870597 10180665226)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart4_checked : CutMid3H2NegPart4Tree.commonOK CutMid3H2NegPart4Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
