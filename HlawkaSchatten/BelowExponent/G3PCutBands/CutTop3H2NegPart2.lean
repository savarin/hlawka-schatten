/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegPart2Box : Box := (((((((((⟨![9/68, 9/50, 0, -8], ![27/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H2NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨120689819474, 123862991200, (.direct 10180561190 7324836944), (.chord .universal 10180665226 24716235638)⟩)
    (.cut 3 (-3/16)
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 15468218890), (.chord (.midpoint ⟨440657534088, 139943422393, 201277361264, 342900888968, 214255780226, 229283619411⟩) 24716235638 43500686443)⟩)
      (.cut 0 (45/272)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 7776538975), (.chord (.midpoint ⟨539442318108, 83019571561, 161685629867, 400552862687, 176700310715, 282595718348⟩) 24716235638 43500686443)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 7324836944), (.chord (.midpoint ⟨527986015583, 88857893411, 162630291726, 398900667220, 181188517673, 280172369812⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H2NegPart2_checked : CutTop3H2NegPart2Tree.commonOK CutTop3H2NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
