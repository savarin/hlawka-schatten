/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegPart2Box : Box := (((((((((⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H4NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 13057704193), (.variance 610452045126)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 5620278234), (.chord (.midpoint ⟨438406770563, 141421613054, 188589328364, 359113762284, 215088273095, 164980968874⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 13057704193), (.chord (.midpoint ⟨400120034863, 167907345729, 203948922460, 339707866461, 229156671571, 218580362329⟩) 24716235638 43500686443)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 5620278234), (.chord (.midpoint ⟨500946725758, 103410790870, 162540695042, 399056665319, 191620248416, 267424451713⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H4NegPart2_checked : CutTop3H4NegPart2Tree.commonOK CutTop3H4NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
