/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegPart6Box : Box := (((((((((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 1 (3/25)).lowerChild 2 (7/32)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H0NegPart6Tree : CertTree :=
  .cut 1 (23/200)
    (.cut 0 (9/136)
      (.row ⟨95281442640, 97336292160, (.direct 10180561190 9600617403), (.chord .universal 10180665226 24716235638)⟩)
      (.row ⟨95281442640, 97336292160, (.direct 10180561190 9033225388), (.variance 672288009474)⟩))
    (.cut 0 (9/136)
      (.row ⟨97336292159, 99345187400, (.direct 10180561190 9574092879), (.chord .universal 10180665226 24716235638)⟩)
      (.row ⟨97336292159, 99345187400, (.direct 10180561190 8981384302), (.variance 673301994573)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegPart6_checked : CutMid3H0NegPart6Tree.commonOK CutMid3H0NegPart6Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
