/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart7Box : Box := (((((((((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (3/25)).upperChild 1 (23/200)).upperChild 0 (45/136)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart7Tree : CertTree :=
  .cut 2 (1/16)
    (.row ⟨97336292159, 99345187400, (.direct 3393509060 5655085494), (.variance 946749472688)⟩)
    (.cut 2 (3/32)
      (.row ⟨97336292159, 99345187400, (.direct 3393509060 5655085494), (.chord (.secant 1609076972697 296655319813 12862110330 104098464133) 3393555298 6452870597)⟩)
      (.row ⟨97336292159, 99345187400, (.direct 3393509060 5655085494), (.chord (.secant 1241654450141 118862344631 168117714 65981245218) 6452870597 10180665226)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart7_checked : CutMid3H2NegPart7Tree.commonOK CutMid3H2NegPart7Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
