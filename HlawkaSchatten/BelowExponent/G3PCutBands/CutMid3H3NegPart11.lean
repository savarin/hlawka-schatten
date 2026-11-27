/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegPart11`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegPart11Box : Box := ((((((((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).upperChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H3NegPart11Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨99345187399, 103236350716, (.direct 19358451269 12711489557), (.variance 614762763413)⟩)
      (.row ⟨99345187399, 103236350716, (.direct 10180561190 5380715205), (.chord (.midpoint ⟨377105778328, 185103821071, 200010058031, 344441021242, 237553328641, 110738277608⟩) 10180665226 24716235638)⟩))
    (.cut 0 (63/136)
      (.row ⟨99345187399, 103236350716, (.direct 10180561190 5918196349), (.chord (.midpoint ⟨426243800055, 149558447696, 179493443376, 371932573853, 219575257575, 191426221341⟩) 24716235638 43500686443)⟩)
      (.row ⟨99345187399, 103236350716, (.direct 10180561190 5380715205), (.chord (.midpoint ⟨401110202764, 167189579783, 183063893186, 366770991240, 228794642387, 182541203250⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegPart11_checked : CutMid3H3NegPart11Tree.commonOK CutMid3H3NegPart11Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
