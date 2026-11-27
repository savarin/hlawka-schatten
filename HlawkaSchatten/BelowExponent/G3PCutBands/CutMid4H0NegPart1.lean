/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegPart1Box : Box := (((((((⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid4H0NegPart1Tree : CertTree :=
  .cut 1 (7/50)
    (.cut 3 (-1/8)
      (.row ⟨103236350715, 106974752992, (.direct 10180561190 8772363392), (.variance 677466541772)⟩)
      (.cut 1 (27/200)
        (.row ⟨103236350715, 105123556200, (.direct 0 173666696), (.chord .universal 0 10180665226)⟩)
        (.row ⟨105123556199, 106974752992, (.direct 0 184755662), (.chord .universal 0 10180665226)⟩)))
    (.cut 3 (-1/8)
      (.row ⟨106974752991, 110576703735, (.direct 10180561190 8666855610), (.variance 679616536049)⟩)
      (.cut 1 (29/200)
        (.row ⟨106974752991, 108791878640, (.direct 0 196157718), (.chord .universal 0 10180665226)⟩)
        (.row ⟨108791878639, 110576703735, (.direct 0 207873476), (.chord .universal 0 10180665226)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid4H0NegPart1_checked : CutMid4H0NegPart1Tree.commonOK CutMid4H0NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
