/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegPart2Box : Box := (((((((((⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop0H2NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 16112886410), (.variance 577752809367)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 7790128701), (.chord (.midpoint ⟨460610688371, 127207216179, 193516022027, 352602714347, 206841616327, 161629128504⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 16112886410), (.chord (.midpoint ⟨433630315686, 144586905188, 203990616424, 339658601178, 216852627267, 226809461684⟩) 24716235638 43500686443)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 7790128701), (.chord (.midpoint ⟨539234487956, 83123772400, 161772769920, 400399766031, 176782132219, 275293088353⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H2NegPart2_checked : CutTop0H2NegPart2Tree.commonOK CutTop0H2NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
